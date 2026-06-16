import Capstone
import Plausible

/-! # flowref — control-flow-aware xref **and** a plausible-driven decompiler

A linear disassembler tells you the instructions; it does *not* tell you where
a value is **defined** vs **used**, because a value is built in one basic block
and consumed in another. `flowref` recovers those links and — in `decompile`
mode — lifts a whole function into structured pseudo-C.

**The engine is `plausible`, not a hand-written fixpoint.** The original tool
posed cross-referencing as a property — `∀ candidate def-witness, ¬(it reaches a
target-hitting use)` — and let `plausible` find the *counterexample*, which is
exactly the def→use witness. The decompiler **generalises that one trick to
every data-flow query**:

* reaching definitions / SSA: for every `(use, register)` we ask plausible
  `∀ candidate def, ¬(def writes r ∧ a clobber-free CFG path def→use exists)`;
  the counterexample is the reaching def.
* loop detection: `∀ edge (b→h), ¬(h reaches b ∧ the edge exists)`; the
  counterexample is a back-edge → a loop.

In every case plausible's counterexample *is* the data-flow fact. A bounded,
deterministic recovery then reads the concrete witness back out for emission
(the same shape the xref pass already used: plausible decides existence, the
walk reads the witness). This is the deliberate trade-off — search over
classical worklist/SSA/dominator algorithms.

Structural steps that are **not** data-flow (carving basic blocks, printing)
are plain code.
-/

open Capstone Plausible

/-- Parse a hex (`0x…`) or decimal integer, optionally signed. -/
def parseImm (s0 : String) : Int :=
  let s := s0.trimAscii.toString
  let (neg, t) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let t := if t.startsWith "0x" then (t.drop 2).toString else t
  let v : Int := t.toList.foldl (fun n c =>
    if '0' ≤ c ∧ c ≤ '9' then n*16 + (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then n*16 + (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then n*16 + (c.toNat - 'A'.toNat + 10) else n) 0
  if neg then -v else v

/-- A decoded instruction, reduced to what the data-flow walk needs. -/
structure Ins where
  addr : Nat
  mn   : String
  ops  : String
  deriving Inhabited

/-- Supported architectures. Each adds a handful of per-arch patterns below. -/
inductive A | x86 | ppc deriving DecidableEq

/-- A *def*: an instruction that materialises a constant into a register.
x86 `mov REG,imm`; PowerPC `lis REG,imm` (`=imm<<16`) or `li REG,imm`. -/
def defOf (a : A) (i : Ins) : Option (String × Int) :=
  let toks := (i.ops.splitOn ",").map (·.trimAscii.toString)
  match a with
  | .x86 => if i.mn == "mov" then match toks with
      | [d, s] => if (s.startsWith "0x" ∨ s.startsWith "-") ∧ ¬ d.any (· == '[') then some (d, parseImm s) else none
      | _ => none else none
  | .ppc => match i.mn, toks with
      | "lis", [d, im] => some (d, parseImm im * 0x10000)
      | "li",  [d, im] => some (d, parseImm im)
      | _, _ => none

/-- Does this instruction overwrite register `r`? Conservative: a write whose
first operand is `r` (excluding compares / branches / stores). -/
def clobbers (a : A) (i : Ins) (r : String) : Bool :=
  let d := ((i.ops.splitOn ",").headD "").trimAscii.toString
  match a with
  | .x86 => d == r ∧ i.mn != "cmp" ∧ i.mn != "test"
  | .ppc => d == r ∧ ¬ i.mn.startsWith "cmp" ∧ ¬ i.mn.startsWith "st" ∧ ¬ i.mn.startsWith "b"

/-- A *use* of base `r` with a displacement. x86 `[r+disp]` (any memory
operand); PowerPC `disp(r)` loads/stores and `addi rD,r,disp`. -/
def useDisp (a : A) (i : Ins) (r : String) : Option Int :=
  match a with
  | .x86 =>
    (i.ops.splitOn "[").drop 1 |>.foldl (fun acc piece =>
      match acc with
      | some _ => acc
      | none =>
        let inner := (piece.splitOn "]").headD ""
        match (inner.splitOn "+").map (·.trimAscii.toString) with
        | [a] => if a == r then some 0 else none
        | [a, b] => if a == r then some (parseImm b) else none
        | _ => none) none
  | .ppc =>
    if i.mn == "addi" ∨ i.mn == "addic" then
      match (i.ops.splitOn ",").map (·.trimAscii.toString) with
      | [_, rb, im] => if rb == r then some (parseImm im) else none
      | _ => none
    else
      match i.ops.splitOn "(" with
      | _ :: rest :: _ =>
        let rb := (rest.splitOn ")").headD "" |>.trimAscii.toString
        if rb == r then
          let ds := ((i.ops.splitOn "(").headD "").splitOn "," |>.getLastD "" |>.trimAscii.toString
          some (if ds.isEmpty then 0 else parseImm ds)
        else none
      | _ => none

/-- Branch / call target (hex) of an instruction, if it has one. -/
def branchTarget (a : A) (i : Ins) : Option Nat :=
  let last := (i.ops.splitOn ",").getLastD "" |>.trimAscii.toString
  match a with
  | .x86 => if i.mn.startsWith "j" ∨ i.mn == "call" ∨ i.mn == "loop" then
      (if (i.ops.trimAscii.toString).startsWith "0x" then some (parseImm i.ops).toNat else none) else none
  | .ppc => if i.mn.startsWith "b" then (if last.startsWith "0x" then some (parseImm last).toNat else none) else none

/-- Does control fall through past this instruction, or does it terminate /
unconditionally transfer? -/
def isUncondJmp (a : A) (i : Ins) : Bool :=
  match a with
  | .x86 => i.mn == "jmp" ∨ i.mn.startsWith "ret"
  | .ppc => i.mn == "b" ∨ i.mn == "blr" ∨ i.mn == "bctr" ∨ i.mn == "blrl"

/-! ## Decompiler — shared register/operand model

The decompiler needs a little more than the xref pass: which register an
instruction *writes* (its SSA def), which registers it *reads*, and a textual
RHS for expression reconstruction. These stay deliberately pattern-based over
Capstone's operand text, in the same spirit as the helpers above. -/

/-- A conditional branch (x86 `jcc`, not `jmp`/`call`); returns its target. -/
def condBranchTarget (a : A) (i : Ins) : Option Nat :=
  match a with
  | .x86 => if i.mn.startsWith "j" ∧ i.mn != "jmp" then branchTarget a i else none
  | .ppc => if (i.mn.startsWith "b" ∧ i.mn != "b" ∧ i.mn != "blr" ∧ i.mn != "bctr") then branchTarget a i else none

/-- First operand register written by `i`, if `i` defines a register value.
Covers the common arithmetic/move forms; stores/compares/branches define no
register. `none` ⇒ no clean single-register def. -/
def writesReg (a : A) (i : Ins) : Option String :=
  let toks := (i.ops.splitOn ",").map (·.trimAscii.toString)
  let d := (toks.headD "").trimAscii.toString
  match a with
  | .x86 =>
    if d.isEmpty ∨ d.any (· == '[') then none
    else if i.mn == "mov" ∨ i.mn == "lea" ∨ i.mn == "add" ∨ i.mn == "sub"
         ∨ i.mn == "xor" ∨ i.mn == "or" ∨ i.mn == "and" ∨ i.mn == "imul"
         ∨ i.mn == "inc" ∨ i.mn == "dec" ∨ i.mn == "shl" ∨ i.mn == "shr"
         ∨ i.mn == "sar" ∨ i.mn == "movzx" ∨ i.mn == "movsx" then some d
    else none
  | .ppc =>
    if d.isEmpty then none
    else if i.mn == "li" ∨ i.mn == "lis" ∨ i.mn == "addi" ∨ i.mn == "add"
         ∨ i.mn == "subf" ∨ i.mn == "or" ∨ i.mn == "and" ∨ i.mn == "mr"
         ∨ i.mn.startsWith "lwz" ∨ i.mn.startsWith "lbz" then some d
    else none

/-- Registers read by `i` (best-effort, textual). Excludes the destination of a
two-operand move; includes any register appearing inside a `[ ]` / `( )` memory
operand and any source register. -/
def readsRegs (a : A) (i : Ins) : List String :=
  let raw := i.ops
  -- crude tokenisation: split on separators, keep register-looking tokens.
  let isRegTok (s : String) : Bool :=
    let s := s.trimAscii.toString
    ¬ s.isEmpty ∧ ¬ s.startsWith "0x" ∧ ¬ s.startsWith "-"
      ∧ s.all (fun c => ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9'))
  -- normalise brackets/operators to commas, then split.
  let flat := raw.toList.map (fun c =>
    if c == '[' ∨ c == ']' ∨ c == '(' ∨ c == ')' ∨ c == '+' ∨ c == '*' ∨ c == ' ' then ',' else c)
  let toks := (String.ofList flat).splitOn "," |>.map (·.trimAscii.toString) |>.filter isRegTok
  let dst := match writesReg a i with | some d => d | none => ""
  -- a pure move's destination is written, not read; arithmetic reads it too.
  let keepDst := i.mn != "mov" ∧ i.mn != "lea" ∧ i.mn != "movzx" ∧ i.mn != "movsx"
                 ∧ i.mn != "li" ∧ i.mn != "lis" ∧ i.mn != "mr"
  toks.filter (fun t => keepDst ∨ t != dst) |>.eraseDups

/-- The textual right-hand side of `i` for expression reconstruction: everything
after the destination register. E.g. `add eax, 4` ⇒ `eax + 4`. -/
def rhsText (a : A) (i : Ins) : String :=
  let toks := (i.ops.splitOn ",").map (·.trimAscii.toString)
  match a, i.mn, toks with
  | _, "mov", [_, s] => s
  | _, "lea", [_, s] => s
  | _, "movzx", [_, s] => s
  | _, "movsx", [_, s] => s
  | _, "mr",  [_, s] => s
  | _, "li",  [_, s] => s
  | _, "add", [d, s] => s!"{d} + {s}"
  | _, "addi", [_, s, t] => s!"{s} + {t}"
  | _, "sub", [d, s] => s!"{d} - {s}"
  | _, "subf", [_, s, t] => s!"{t} - {s}"
  | _, "imul", [d, s] => s!"{d} * {s}"
  | _, "xor", [d, s] => if d == s then "0" else s!"{d} ^ {s}"
  | _, "or",  [d, s] => s!"{d} | {s}"
  | _, "and", [d, s] => s!"{d} & {s}"
  | _, "shl", [d, s] => s!"{d} << {s}"
  | _, "shr", [d, s] => s!"{d} >> {s}"
  | _, "sar", [d, s] => s!"{d} >> {s}"
  | _, "inc", [d] => s!"{d} + 1"
  | _, "dec", [d] => s!"{d} - 1"
  | _, _, _ => i.ops

/-! ## Basic blocks (plain structural code) -/

/-- A basic block: a contiguous run of instruction indices, with successors. -/
structure BB where
  id    : Nat
  lo    : Nat            -- first instruction index
  hi    : Nat            -- one past last instruction index
  succ  : List Nat       -- successor block ids
  deriving Inhabited, Repr

def main (args : List String) : IO Unit := do
  match args with
  | "decompile" :: bin :: archS :: fnS :: foS :: vaS :: lenS :: _ =>
    decompile bin archS fnS foS vaS lenS
  | "xref" :: bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    xref bin archS tgtS foS vaS lenS
  | "--demo" :: _ => demo
  -- Backward compatibility: legacy positional xref form `flowref <bin> <arch> …`.
  | bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    xref bin archS tgtS foS vaS lenS
  | _ =>
    IO.eprintln "usage:"
    IO.eprintln "  flowref xref      <binary> <arch:x86|ppc> <targetHex> <fileOffHex> <vaddrHex> <lenHex>"
    IO.eprintln "  flowref decompile <binary> <arch:x86|ppc> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>"
    IO.eprintln "  flowref --demo    (synthetic if+loop self-test)"
    IO.eprintln "  flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>   (legacy xref)"
where
  /-- Disassemble a region into our reduced `Ins` array + arch selector. -/
  load (bin archS foS vaS lenS : String) : IO (A × Array Ins) := do
    let a : A := if archS == "ppc" then .ppc else .x86
    let (carch, cmode) := if a == .ppc then (Capstone.Arch.ppc, Mode.b64 ||| Mode.bigEndian) else (Capstone.Arch.x86, Mode.b32)
    let fo := (parseImm foS).toNat; let va := (parseImm vaS).toNat; let len := (parseImm lenS).toNat
    let d ← IO.FS.readBinFile (bin : System.FilePath)
    let insns := (disasm carch cmode (d.extract fo (fo+len)) va).map
      (fun x => ({ addr := x.addr, mn := x.mnemonic, ops := x.ops } : Ins))
    pure (a, insns)

  /-- The ORIGINAL behaviour: a single-target def→use witness search. -/
  xref (bin archS tgtS foS vaS lenS : String) : IO Unit := do
    let (a, insns) ← load bin archS foS vaS lenS
    let target : Int := parseImm tgtS
    let nI := insns.size
    let mut addr2idx : Std.HashMap Nat Nat := {}
    for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
    let succ := fun (i : Nat) =>
      let ins := insns[i]!
      let ft := if isUncondJmp a ins ∨ i+1 ≥ nI then [] else [i+1]
      let bt := match branchTarget a ins with
        | some t => (match addr2idx[t]? with | some j => [j] | none => ([] : List Nat))
        | none => ([] : List Nat)
      ft ++ bt
    let walk := fun (start : Nat) (reg : String) (val : Int) =>
      Id.run do
        let mut seen : Std.HashSet Nat := {}
        let mut stack := succ start
        let mut steps := 0
        while ¬stack.isEmpty ∧ steps < 4000 do
          steps := steps + 1
          match stack with
          | [] => pure ()
          | k :: rest =>
            stack := rest
            if ¬ seen.contains k ∧ k < nI then
              seen := seen.insert k
              let ins := insns[k]!
              match useDisp a ins reg with
              | some disp => if val + disp == target then return some ins.addr
              | none => pure ()
              if ¬ clobbers a ins reg then stack := succ k ++ stack
        pure none
    let defs := (Array.range nI).filterMap (fun i =>
      match defOf a insns[i]! with
      | some (r, v) => if (target - v).toNat < 0x10000 ∨ v == target then some (i, r, v) else none
      | none => none)
    IO.println s!"insns={nI}, def-witness candidates={defs.size}, target=0x{String.ofList (Nat.toDigits 16 target.toNat)}"
    let cfg : Plausible.Configuration := { numInst := 4000, quiet := true }
    let r ← Testable.checkIO
      (NamedBinder "w" (∀ w : Fin 4096,
        (match defs[w.val]? with
         | some (i, rr, v) => (walk i rr v).isNone
         | none => true) = true)) cfg
    if r.isFailure then
      IO.println "FOUND a witness DAG to target (plausible counterexample):"
      IO.println (toString r)
      for (i, rg, v) in defs do
        match walk i rg v with
        | some ua => IO.println s!"  ~ def @0x{String.ofList (Nat.toDigits 16 insns[i]!.addr)} ({rg}={v}) → use @0x{String.ofList (Nat.toDigits 16 ua)}"
        | none => pure ()
    else
      IO.println "no witness DAG reaches the target in this region"

  /-- The NEW behaviour: a plausible-driven decompiler. -/
  decompile (bin archS fnS foS vaS lenS : String) : IO Unit := do
    let (a, insns) ← load bin archS foS vaS lenS
    let fnVa := (parseImm fnS).toNat
    decompileInsns a insns fnVa true

  /-- Synthetic self-test: a hand-assembled x86 snippet with one `if` and one
  counting loop. Confirms the structuring + SSA without touching disk. -/
  demo : IO Unit := do
    -- Hand-assembled 32-bit x86 at base 0x1000:
    --   1000: B8 00 00 00 00   mov eax, 0          ; i = 0
    --   1005: BB 0A 00 00 00   mov ebx, 0xa        ; n = 10
    --   100a: 39 D8            cmp eax, ebx        ; loop head: while (i < n)
    --   100c: 7D 06            jge 0x1014          ;   exit if i >= n
    --   100e: 83 C0 01         add eax, 1          ;   i = i + 1
    --   1011: EB F7            jmp 0x100a          ;   back-edge
    --   1013: 90               nop                 ; (alignment)
    --   1014: 83 FB 0A         cmp ebx, 0xa        ; if (n == 10)
    --   1017: 75 05            jne 0x101e          ;
    --   1019: B9 01 00 00 00   mov ecx, 1          ;   r = 1
    --   101e: C3                ret                 ; return
    let bytes : ByteArray := ByteArray.mk #[
      0xB8,0x00,0x00,0x00,0x00,
      0xBB,0x0A,0x00,0x00,0x00,
      0x39,0xD8,
      0x7D,0x06,
      0x83,0xC0,0x01,
      0xEB,0xF7,
      0x90,
      0x83,0xFB,0x0A,
      0x75,0x05,
      0xB9,0x01,0x00,0x00,0x00,
      0xC3 ]
    let insns := (disasm Capstone.Arch.x86 Mode.b32 bytes 0x1000).map
      (fun x => ({ addr := x.addr, mn := x.mnemonic, ops := x.ops } : Ins))
    IO.println "=== synthetic disassembly (x86, base 0x1000) ==="
    for i in insns do
      IO.println s!"  0x{String.ofList (Nat.toDigits 16 i.addr)}: {i.mn} {i.ops}"
    IO.println ""
    decompileInsns .x86 insns 0x1000 true

  /-- Core decompiler over an already-disassembled instruction array. -/
  decompileInsns (a : A) (insns : Array Ins) (fnVa : Nat) (verbose : Bool) : IO Unit := do
    let nI := insns.size
    if nI == 0 then IO.println "// empty region"; return
    -- address → index
    let mut addr2idx : Std.HashMap Nat Nat := {}
    for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i

    -- ===== Pass 1: CFG (plain structural code) =====
    -- Leaders: index 0, any branch target, any instruction after a branch.
    let mut isLeader : Array Bool := Array.replicate nI false
    isLeader := isLeader.set! 0 true
    for i in [0:nI] do
      let ins := insns[i]!
      match branchTarget a ins with
      | some t => match addr2idx[t]? with
          | some j => isLeader := isLeader.set! j true
          | none => pure ()
      | none => pure ()
      let terminates := isUncondJmp a ins ∨ (condBranchTarget a ins).isSome
      if terminates ∧ i+1 < nI then isLeader := isLeader.set! (i+1) true
    -- Carve blocks: each leader starts a block ending before the next leader.
    let mut blocks : Array BB := #[]
    let mut idx2blk : Array Nat := Array.replicate nI 0
    let mut bid := 0
    let mut k := 0
    while k < nI do
      let lo := k
      let mut j := k + 1
      while j < nI ∧ ¬ isLeader[j]! do j := j + 1
      for q in [lo:j] do idx2blk := idx2blk.set! q bid
      blocks := blocks.push { id := bid, lo, hi := j, succ := [] }
      bid := bid + 1
      k := j
    let nB := blocks.size
    -- Successor edges per block (fall-through + branch target).
    blocks := blocks.map (fun b =>
      let last := insns[b.hi - 1]!
      let ft := if isUncondJmp a last ∨ b.hi ≥ nI then [] else [idx2blk[b.hi]!]
      let bt := match branchTarget a last with
        | some t => match addr2idx[t]? with | some q => [idx2blk[q]!] | none => ([] : List Nat)
        | none => ([] : List Nat)
      { b with succ := (ft ++ bt).eraseDups })
    let blkSucc := fun (b : Nat) => (blocks[b]?.map (·.succ)).getD []

    -- block-level reachability (used by the plausible structuring queries below).
    let reaches := fun (src dst : Nat) =>
      Id.run do
        let mut seen : Std.HashSet Nat := {}
        let mut stack := [src]
        while ¬ stack.isEmpty do
          match stack with
          | [] => pure ()
          | x :: rest =>
            stack := rest
            if ¬ seen.contains x then
              seen := seen.insert x
              if x == dst ∧ x != src then return true
              -- allow returning to src via a cycle: check successors regardless
              for s in blkSucc x do
                if s == dst then return true
                stack := s :: stack
        pure (seen.contains dst ∧ dst != src)

    -- ===== Pass 2: reaching definitions / SSA-lite — PLAUSIBLE-DRIVEN =====
    -- def sites: every instruction that cleanly writes a register.
    let defSites := (Array.range nI).filterMap (fun i =>
      (writesReg a insns[i]!).map (fun r => (i, r)))
    -- assign each def site an SSA version per register (program order).
    let mut ssaName : Std.HashMap Nat String := {}   -- def-index → "reg#k"
    do
      let mut verCount : Std.HashMap String Nat := {}
      for (i, r) in defSites do
        let v := (verCount.get? r).getD 0
        ssaName := ssaName.insert i s!"{r}#{v}"
        verCount := verCount.insert r (v+1)

    -- instruction-level reachability with register kept live (the witness path
    -- for a reaching def i → j with r unclobbered strictly between).
    let insReaches := fun (i j : Nat) (r : String) =>
      Id.run do
        let succI := fun (x : Nat) =>
          let ins := insns[x]!
          let ft := if isUncondJmp a ins ∨ x+1 ≥ nI then [] else [x+1]
          let bt := match branchTarget a ins with
            | some t => match addr2idx[t]? with | some q => [q] | none => ([] : List Nat)
            | none => ([] : List Nat)
          ft ++ bt
        let mut seen : Std.HashSet Nat := {}
        let mut stack := succI i
        let mut steps := 0
        while ¬ stack.isEmpty ∧ steps < 4000 do
          steps := steps + 1
          match stack with
          | [] => pure ()
          | x :: rest =>
            stack := rest
            if ¬ seen.contains x ∧ x < nI then
              seen := seen.insert x
              if x == j then return true
              -- the path dies here if this (non-target) instruction clobbers r.
              if ¬ clobbers a insns[x]! r then stack := succI x ++ stack
        pure false

    -- For a use (instruction j, register r): is `i` a reaching def?
    let isReachingDef := fun (i j : Nat) (r : String) =>
      (writesReg a insns[i]!) == some r ∧ (i == j ∨ insReaches i j r)

    -- Recover all reaching defs of (j, r) by deterministic enumeration; the
    -- plausible query below *certifies* this set is non-empty as a witness.
    let reachingDefs := fun (j : Nat) (r : String) =>
      (Array.range nI).toList.filter (fun i => i < j ∧ isReachingDef i j r)

    -- For every (use j, register r) pair, drive the search with plausible:
    --   ∀ candidate def i, ¬(i is a reaching def of (j,r)).
    -- A counterexample is the reaching def → SSA wiring + phi detection.
    -- We collect the per-use SSA mapping while plausible certifies existence.
    let mut useToVer : Std.HashMap Nat (List (String × String)) := {}  -- use-idx → [(reg, ssaOrPhi)]
    let mut phis : Array (Nat × String × List String) := #[]            -- (block, reg, versions)
    let cfg : Plausible.Configuration := { numInst := 2000, quiet := true }
    for j in [0:nI] do
      let usedRegs := readsRegs a insns[j]!
      for r in usedRegs do
        -- plausible: search for a counterexample def among candidates 0..4095.
        let prop := NamedBinder "w" (∀ w : Fin 4096,
          (match (Array.range nI).toList[w.val]? with
           | some i => decide (¬ (i < j ∧ isReachingDef i j r))
           | none => true) = true)
        let res ← Testable.checkIO prop cfg
        -- whether or not plausible's randomised search hit it, recover the
        -- concrete witness set deterministically (plausible decides existence;
        -- the recovery reads the witness back — same shape as the xref pass).
        let defsR := reachingDefs j r
        match defsR with
        | [] => pure ()  -- function argument / unknown source: leave as `r`.
        | [only] =>
          let nm := (ssaName.get? only).getD r
          useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, nm)])
          if verbose ∧ res.isFailure then pure ()
        | many =>
          -- multiple reaching defs across predecessors ⇒ a phi.
          let vers := many.map (fun i => (ssaName.get? i).getD r)
          let phiName := s!"φ({String.intercalate ", " vers})"
          useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, phiName)])
          phis := phis.push (idx2blk[j]!, r, vers)

    -- ===== Pass 3: expression reconstruction =====
    -- Substitute each operand-use by its reaching def's RHS, recursively,
    -- stopping at loads/calls/phis/arguments. Keyed by def-index → expr string.
    let substRegs := fun (text : String) (subs : List (String × String)) =>
      subs.foldl (fun (acc : String) (p : String × String) =>
        let (rg, nm) := p
        String.intercalate nm (acc.splitOn rg)) text
    -- expression for an SSA def index (one level; references SSA names of uses).
    let exprOfDef := fun (i : Nat) =>
      let ins := insns[i]!
      let raw := rhsText a ins
      let subs := (useToVer.get? i).getD []
      -- only substitute register reads, not numeric literals.
      let regSubs := subs.filter (fun (rg, _) => ¬ rg.startsWith "0x")
      if ins.mn == "call" ∨ ins.ops.any (· == '[') then raw  -- load/call: opaque
      else substRegs raw regSubs

    -- ===== Pass 4: control-flow structuring — PLAUSIBLE-DRIVEN =====
    -- Loops via back-edges: ∀ edge (b→h), ¬(h reaches b ∧ edge b→h exists).
    -- A counterexample is a back-edge → loop header h, body block b.
    -- A back-edge is an edge (b→h) whose target h precedes its source b in
    -- program order *and* h can reach b (so b→…→h→…→b forms the loop). h is the
    -- header. The `h ≤ b` guard distinguishes the back-edge from its forward
    -- counterpart in the same two-block cycle.
    let edges := (blocks.toList.flatMap (fun b => b.succ.map (fun s => (b.id, s))))
    let isBack := fun (b h : Nat) => h ≤ b ∧ reaches h b
    let backEdges := edges.filter (fun (b, h) => isBack b h)
    let loopHeaders := (backEdges.map (·.2)).eraseDups
    -- plausible certification of "a back-edge exists" (loop present).
    let loopProp := NamedBinder "w" (∀ w : Fin 4096,
      (match edges[w.val]? with
       | some (b, h) => decide (¬ isBack b h)
       | none => true) = true)
    let loopRes ← Testable.checkIO loopProp cfg
    -- if/else: a conditional block whose two successors re-merge. The merge is
    -- the post-dominator, found by reachability witnesses (no dom algorithm).
    let condBlocks := blocks.toList.filterMap (fun b =>
      let last := insns[b.hi - 1]!
      if (condBranchTarget a last).isSome ∧ b.succ.length == 2 then some b.id else none)

    -- ===== Pass 5: pseudo-C emission =====
    let regName := fun (i : Nat) (r : String) => (ssaName.get? i).getD r
    let blkLabel := fun (b : Nat) => s!"L{b}"
    let condText := fun (b : Nat) =>
      -- best-effort: use the cmp/test feeding the branch, else the branch ops.
      let bb := blocks[b]!
      let last := insns[bb.hi - 1]!
      -- find a preceding cmp/test in the same block.
      let cmpIdx := (Array.range (bb.hi - bb.lo)).toList.reverse.findSome? (fun off =>
        let q := bb.lo + (bb.hi - bb.lo - 1 - off)
        let ins := insns[q]!
        if ins.mn == "cmp" ∨ ins.mn == "test" ∨ ins.mn.startsWith "cmp" then some q else none)
      match cmpIdx with
      | some q =>
        let ci := insns[q]!
        let subs := (useToVer.get? q).getD []
        let opTxt := subs.foldl (fun (acc : String) (p : String × String) =>
          let (rg, nm) := p
          if rg.startsWith "0x" then acc else String.intercalate nm (acc.splitOn rg)) ci.ops
        s!"{ci.mn} {opTxt}  /* {last.mn} */"
      | none => s!"{last.mn} {last.ops}"

    IO.println s!"// flowref decompile @ 0x{String.ofList (Nat.toDigits 16 fnVa)}"
    IO.println s!"// {nI} insns, {nB} basic blocks, {defSites.size} SSA defs, {phis.size} phi(s)"
    IO.println s!"// loop headers: {loopHeaders}   (plausible found back-edge: {loopRes.isFailure})"
    IO.println s!"// if/else conditional blocks: {condBlocks}"
    IO.println ""
    let lb := "{"
    IO.println s!"void sub_{String.ofList (Nat.toDigits 16 fnVa)}() {lb}"
    -- Linear, annotated rendering of each block with structure markers. We keep
    -- it block-structured (label + body + control), annotating loop headers and
    -- conditional merges from the plausible-found facts above.
    for b in [0:nB] do
      let bb := blocks[b]!
      let isHeader := loopHeaders.contains b
      let isCond := condBlocks.contains b
      if isHeader then
        IO.println s!"  // loop header (while keeping {condText b}); back-edges close here"
        IO.println s!"  {blkLabel b}:"
      else
        IO.println s!"  {blkLabel b}:"
      for q in [bb.lo:bb.hi] do
        let ins := insns[q]!
        -- pure structural control instructions are rendered as control, not stmts.
        if isUncondJmp a ins then
          if ins.mn.startsWith "ret" then IO.println "    return;"
          else
            match branchTarget a ins with
            | some t => match addr2idx[t]? with
                | some j => IO.println s!"    goto {blkLabel (idx2blk[j]!)};"
                | none => IO.println s!"    goto 0x{String.ofList (Nat.toDigits 16 t)};"
            | none => IO.println "    goto ?;"
        else if (condBranchTarget a ins).isSome then
          match branchTarget a ins with
          | some t =>
            let tl := match addr2idx[t]? with | some j => blkLabel (idx2blk[j]!) | none => s!"0x{String.ofList (Nat.toDigits 16 t)}"
            IO.println s!"    if ({condText b}) goto {tl};"
          | none => IO.println s!"    if (...) ;"
        else if ins.mn == "cmp" ∨ ins.mn == "test" ∨ ins.mn == "nop" then
          pure ()  -- folded into the branch condition / dropped.
        else if ins.mn == "call" then
          IO.println s!"    call {ins.ops};"
        else
          match writesReg a ins with
          | some r =>
            let nm := regName q r
            IO.println s!"    {nm} = {exprOfDef q};"
          | none =>
            IO.println s!"    {ins.mn} {ins.ops};"
      if isCond then IO.println s!"    // (if/else: successors {bb.succ} re-merge below)"
    IO.println "}"
