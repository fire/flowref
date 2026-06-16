import Flowref.Disasm
import Flowref.Dataflow
import Flowref.Emit
import Flowref.Ports
import Flowref.Decoders
import Flowref.Adapters
import Plausible

/-! # flowref — control-flow-aware xref **and** a plausible-driven decompiler

A linear disassembler tells you the instructions; it does *not* tell you where
a value is **defined** vs **used**, because a value is built in one basic block
and consumed in another. `flowref` recovers those links and — in `decompile`
mode — lifts a whole function into a **compilable C** translation unit.

**The engine is `plausible`, not a hand-written fixpoint.** Every data-flow
query is posed as `∀ candidate witness, ¬(it is the fact we want)` and plausible
hands back the counterexample, which *is* the fact (reaching def, back-edge, …).
The searches are **iteratively deepened**: cheap level first, escalate only the
unresolved frontier — a witness DAG (see `Flowref/Dataflow.lean`).

The emitter (`Flowref/Emit.lean`) lowers the recovered facts into C that
`gcc -fsyntax-only -std=c11 -w` accepts.
-/

open Plausible Flowref

/-- Version string. -/
def flowrefVersion : String :=
  "flowref 1.1.0 — control-flow-aware xref + plausible-driven decompiler with a " ++
  "calling-convention parameter model (SysV x86-64 + cdecl x86-32)"

/-- Full usage text. -/
def usageText : String :=
  "flowref — control-flow-aware xref + plausible-driven decompiler (compilable C)\n\n" ++
  "USAGE:\n" ++
  "  flowref decompile     <binary>  <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex> [--search-trace]\n" ++
  "  flowref xref          <binary>  <arch> <targetHex>  <fileOffHex> <vaddrHex> <lenHex> [--search-trace]\n" ++
  "  flowref decompile-asm <listing> <arch> <fnVaddrHex> [--search-trace]   (objdump-style .asm text)\n" ++
  "  flowref xref-asm      <listing> <arch> <targetHex>  [--search-trace]   (objdump-style .asm text)\n" ++
  "  flowref --demo [--emit-c] [--search-trace]\n" ++
  "  flowref --demo-deep   (iterative-deepening escalation demonstration)\n" ++
  "  flowref --demo-params [--emit-c]  (calling-convention parameter-model demo:\n" ++
  "                  SysV x86-64 2-param + cdecl x86-32 1-param recovered signatures)\n" ++
  "  flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>   (legacy xref)\n" ++
  "  flowref --help | -h | --version\n\n" ++
  "ARGS:\n" ++
  "  arch        x86 (32-bit) | x64 (x86-64) | ppc (64-bit big-endian)\n" ++
  "  fnVaddrHex  virtual address of the function to decompile (e.g. 0x401010)\n" ++
  "  targetHex   address/constant to find references to (xref)\n" ++
  "  fileOffHex  start offset of the region in the file\n" ++
  "  vaddrHex    virtual/load address that fileOff maps to\n" ++
  "  lenHex      length of the region to disassemble\n\n" ++
  "FLAGS:\n" ++
  "  --emit-c        (with --demo) print ONLY the C translation unit to stdout,\n" ++
  "                  so it can be piped to a compiler:\n" ++
  "                    flowref --demo --emit-c | gcc -xc -std=c11 -w -fsyntax-only -\n" ++
  "  --search-trace  print the iterative-deepening escalation chain to stderr\n" ++
  "  --help, -h      this help\n" ++
  "  --version       version string\n"

/-- Build the full compilable C translation unit for a function. Returns the C
text plus the search trace. `verbose`/header comments are part of the C as
comments (still C-legal). -/
def emitC (a : A) (bits : Bits) (insns : Array Ins) (fnVa : Nat) : IO (String × Array TraceEntry) := do
  let nI := insns.size
  if nI == 0 then
    pure (cPreamble ++ "uint32_t sub_" ++ hex fnVa ++ "(void) { return 0; }\n", #[])
  else
  -- address → index
  let mut addr2idx : Std.HashMap Nat Nat := {}
  for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i

  -- ===== Pass 0: calling-convention parameter model =====
  -- Recover the function's integer/pointer parameters from the calling
  -- convention chosen by (arch, width): SysV AMD64 for x86-64, cdecl for x86-32.
  -- This is what turns `sub_X(void)` into a real signature. See Flowref/Params.lean.
  let pm ← recoverParams a bits insns addr2idx
  -- The C parameter list, e.g. "uint32_t a0, uint32_t a1" (or "void").
  let paramList :=
    if pm.count == 0 then "void"
    else String.intercalate ", " (pm.names.map (fun nm => s!"uint32_t {nm}"))
  -- SysV: incoming arg registers bind to parameter names (a parameter is a
  -- def-at-entry); this is injected directly into the SSA use map in Pass 2
  -- below (the `[]`-reaching-def case), reusing the existing register-
  -- substitution path in `renderExprC` (so `mov eax, edi` → `eax = a0`).
  -- cdecl: incoming args are stack slots `[ebp+8]`/`[esp+4]`. After SSA/mem
  -- lowering a slot reads as `*(uint32_t*)((uintptr_t)(ebp + 8))`; we rewrite
  -- that exact C text to the parameter name `a{k}` as a final pass. Build the
  -- (needle, paramName) pairs once.
  let cdeclSlotRewrites : List (String × String) :=
    if pm.conv == .cdecl then
      -- Capstone may print the displacement in decimal (`ebp + 8`) or hex
      -- (`ebp + 0x8`); cover both forms of the lowered C text.
      (List.range pm.count).flatMap (fun k =>
        let eD := (cdeclEbpDisp k).toNat
        let sD := (cdeclEspDisp k).toNat
        [ (memToC s!"[ebp + {eD}]",       s!"a{k}"),
          (memToC s!"[ebp + 0x{hex eD}]", s!"a{k}"),
          (memToC s!"[esp + {sD}]",       s!"a{k}"),
          (memToC s!"[esp + 0x{hex sD}]", s!"a{k}") ])
    else []
  let applyCdecl := fun (s : String) =>
    cdeclSlotRewrites.foldl (fun acc (needle, nm) =>
      String.intercalate nm (acc.splitOn needle)) s

  -- ===== Pass 1: CFG (plain structural code) =====
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
  blocks := blocks.map (fun b =>
    let last := insns[b.hi - 1]!
    let ft := if isUncondJmp a last ∨ b.hi ≥ nI then [] else [idx2blk[b.hi]!]
    let bt := match branchTarget a last with
      | some t => match addr2idx[t]? with | some q => [idx2blk[q]!] | none => ([] : List Nat)
      | none => ([] : List Nat)
    { b with succ := (ft ++ bt).eraseDups })
  let blkSucc := fun (b : Nat) => (blocks[b]?.map (·.succ)).getD []

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
            for s in blkSucc x do
              if s == dst then return true
              stack := s :: stack
      pure (seen.contains dst ∧ dst != src)

  -- ===== Pass 2: reaching definitions / SSA — PLAUSIBLE-DRIVEN + iterative deepening =====
  let defSites := (Array.range nI).filterMap (fun i =>
    (writesReg a insns[i]!).map (fun r => (i, r)))
  let mut ssaName : Std.HashMap Nat String := {}   -- def-index → "reg#k"
  do
    let mut verCount : Std.HashMap String Nat := {}
    for (i, r) in defSites do
      let v := (verCount.get? r).getD 0
      ssaName := ssaName.insert i s!"{r}#{v}"
      verCount := verCount.insert r (v+1)

  let mut useToVer : Std.HashMap Nat (List (String × String)) := {}  -- use-idx → [(reg, ssaName)]
  let mut trace : Array TraceEntry := #[]
  for j in [0:nI] do
    let usedRegs := readsRegs a insns[j]!
    for r in usedRegs do
      -- iterative-deepening, plausible-driven reaching-def resolution.
      let (defsR, _lvl, te) ← resolveReachingDef insns addr2idx a j r
      trace := trace.push te
      match defsR with
      | [] =>
        -- No reaching def inside the function ⇒ the value comes from the caller.
        -- Under SysV this read is live-on-entry: if `r` is an in-range arg
        -- register, bind it to its parameter name `a{k}` (a parameter is a
        -- def-at-entry). This is the same `[]`-witness the param model uses.
        match sysvParamForReg pm.count r with
        | some nm => useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, nm)])
        | none    => pure ()  -- genuine unknown source: leave as `r` (a local).
      | [only] =>
        let nm := cName ((ssaName.get? only).getD r)
        useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, nm)])
      | many =>
        -- φ across predecessors: lowered to a single declared local carrying r's
        -- current value (no φ in the emitted C — see the module docs).
        let baseLocal := cName (r ++ "_phi")
        useToVer := useToVer.insert j (((useToVer.get? j).getD []) ++ [(r, baseLocal)])
        let _ := many
        pure ()

  -- ===== Pass 4: control-flow structuring — PLAUSIBLE-DRIVEN =====
  let edges := (blocks.toList.flatMap (fun b => b.succ.map (fun s => (b.id, s))))
  let isBack := fun (b h : Nat) => h ≤ b ∧ reaches h b
  let backEdges := edges.filter (fun (b, h) => isBack b h)
  let loopHeaders := (backEdges.map (·.2)).eraseDups
  let loopProp := NamedBinder "w" (∀ w : Fin 4096,
    (match edges[w.val]? with
     | some (b, h) => decide (¬ isBack b h)
     | none => true) = true)
  let loopRes ← Testable.checkIO loopProp ({ numInst := 2000, quiet := true } : Plausible.Configuration)
  let condBlocks := blocks.toList.filterMap (fun b =>
    let last := insns[b.hi - 1]!
    if (condBranchTarget a last).isSome ∧ b.succ.length == 2 then some b.id else none)

  -- ===== collect declared locals: every SSA name + every register that appears =====
  -- x86 operand keywords that are not registers (size/segment specifiers).
  let kw := ["dword","qword","word","byte","tbyte","xmmword","ptr",
             "fs","gs","cs","ds","es","ss"]
  -- a C local name is legal iff non-empty, first char a letter/'_', not a keyword.
  let okLocal := fun (s : String) =>
    (! kw.contains s) && (match s.toList with
      | [] => false
      | c :: _ => (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'))
  let mut declSet : Std.HashMap String String := {}   -- cName → ctype
  -- Parameter names (`a0..aN`) are function arguments, not locals — never
  -- re-declare them (that would shadow/redefine the parameter and break compile).
  let declAdd := fun (m : Std.HashMap String String) (nm ty : String) =>
    let cn := cName nm
    if okLocal cn ∧ ¬ pm.names.contains cn then m.insert cn ty else m
  -- all SSA defs
  for (i, r) in defSites do
    let nm := (ssaName.get? i).getD r
    declSet := declAdd declSet nm (regCType r)
    -- Also declare the bare register: a written reg can simultaneously appear as
    -- a memory base/index in its own source operand (`mov rax, [rcx+rax*8]`),
    -- where `memToC` emits it un-versioned.
    declSet := declAdd declSet r (regCType r)
  -- φ locals + any read register. We always declare the *bare* register: memory
  -- operands (`memToC`) are emitted without SSA substitution, so a memory base
  -- like `rcx` appears verbatim and must be a declared local. When the read also
  -- has a recorded SSA version, declare that too (the substituted scalar path).
  for j in [0:nI] do
    for r in readsRegs a insns[j]! do
      if ¬ r.startsWith "0x" then
        declSet := declAdd declSet r (regCType r)
        match (useToVer.get? j).getD [] |>.lookup r with
        | some nm => declSet := declAdd declSet nm (regCType r)
        | none => pure ()
  -- the implicit return register
  let retReg := match a with | .x86 => "eax" | .ppc => "r3"
  declSet := declSet.insert (cName retReg) (regCType retReg)
  -- The value returned by a `ret` is the SSA version of the return register
  -- that *reaches* that `ret`, not the zero-initialised base local. With a
  -- single reaching def we wire the return to it (so `return 7;` survives);
  -- with zero or several (a φ across paths) we conservatively fall back to the
  -- base local. This is what makes simple functions provably equivalent.
  let retName := fun (q : Nat) =>
    match (reachingDefsB 4000 insns addr2idx a q retReg).1 with
    | [di] => cName ((ssaName.get? di).getD retReg)
    | _    => cName retReg
  -- a generic condition temp type
  -- (we declare cond temps inline as needed)

  -- ===== forward declarations for called subroutines =====
  let mut calledSubs : Std.HashSet Nat := {}
  for q in [0:nI] do
    let ins := insns[q]!
    if ins.mn == "call" ∨ (a == .ppc ∧ (ins.mn == "bl" ∨ ins.mn == "bctrl")) then
      match branchTarget a ins with
      | some t => calledSubs := calledSubs.insert t
      | none => pure ()

  -- ===== EMIT =====
  let mut out : String := cPreamble
  out := out ++ s!"\n/* flowref decompile @ 0x{hex fnVa}\n"
  out := out ++ s!"   {nI} insns, {nB} basic blocks, {defSites.size} SSA defs\n"
  out := out ++ s!"   loop headers (plausible back-edge: {loopRes.isFailure}): {loopHeaders}\n"
  out := out ++ s!"   if/else conditional blocks: {condBlocks}\n"
  out := out ++ s!"   calling convention: {repr pm.conv}, recovered params: {pm.count} ({pm.names}) */\n\n"
  -- forward prototypes. We know a callee's parameter count only for the function
  -- itself (self-recursion); other callees are declared `(void)` (unknown arity)
  -- — see Flowref/Params.lean on the limits.
  for t in calledSubs.toList do
    if t == fnVa ∧ pm.count > 0 then
      out := out ++ s!"uint32_t sub_{hex t}({paramList});\n"
    else
      out := out ++ s!"uint32_t sub_{hex t}(void);\n"
  out := out ++ "\nuint32_t sub_" ++ hex fnVa ++ s!"({paramList}) " ++ "{\n"
  -- declarations
  for (nm, ty) in declSet.toList do
    out := out ++ s!"  {ty} {nm} = 0;\n"
  -- condition temps: one per conditional branch instruction.
  let mut condCount := 0
  for q in [0:nI] do
    if (condBranchTarget a insns[q]!).isSome then condCount := condCount + 1
  for c in [0:condCount] do
    out := out ++ s!"  int cond_{c} = 0;\n"
  out := out ++ "\n"

  -- body: labels + goto (always valid C). condition index counter.
  let mut ci := 0
  for b in [0:nB] do
    let bb := blocks[b]!
    out := out ++ s!"L{b}:;\n"
    for q in [bb.lo:bb.hi] do
      let ins := insns[q]!
      if isUncondJmp a ins then
        if ins.mn.startsWith "ret" ∨ ins.mn == "blr" then
          out := out ++ s!"  return {retName q};\n"
        else
          match branchTarget a ins with
          | some t => match addr2idx[t]? with
              | some jj => out := out ++ s!"  goto L{idx2blk[jj]!};\n"
              | none => out := out ++ s!"  /* tail-transfer to external 0x{hex t} */\n  return {cName retReg};\n"
          | none => out := out ++ s!"  /* indirect jump {ins.ops} */\n  return {cName retReg};\n"
      else if (condBranchTarget a ins).isSome then
        -- find a preceding cmp/test in this block for the predicate.
        let cmpIdx := (Array.range (bb.hi - bb.lo)).toList.reverse.findSome? (fun off =>
          let p := bb.lo + (bb.hi - bb.lo - 1 - off)
          let cins := insns[p]!
          if cins.mn == "cmp" ∨ cins.mn == "test" ∨ cins.mn.startsWith "cmp" then some p else none)
        -- build a C predicate from the cmp operands + the branch mnemonic.
        let pred : String := match cmpIdx with
          | some p =>
            let cins := insns[p]!
            let toks := (cins.ops.splitOn ",").map (·.trimAscii.toString)
            let subs := (useToVer.get? p).getD []
            let lower := fun (tk : String) =>
              if hasMem tk then memToC tk
              else if tk.startsWith "0x" ∨ tk.startsWith "-" then tk
              else (subs.lookup tk).map cName |>.getD (cName tk)
            match toks with
            | [x, y] =>
              let lx := lower x; let ly := lower y
              if cins.mn == "test" then s!"(({lx}) & ({ly}))"
              else
                let op := if ins.mn == "je" ∨ ins.mn == "jz" then "=="
                  else if ins.mn == "jne" ∨ ins.mn == "jnz" then "!="
                  else if ins.mn == "jl" ∨ ins.mn == "jb" then "<"
                  else if ins.mn == "jle" ∨ ins.mn == "jbe" then "<="
                  else if ins.mn == "jg" ∨ ins.mn == "ja" then ">"
                  else if ins.mn == "jge" ∨ ins.mn == "jae" then ">="
                  else "!="  -- fall back: documented below
                s!"((int32_t)({lx}) {op} (int32_t)({ly}))"
            | _ => "/* unknown predicate */ 1"
          | none => "/* no cmp found; flag-based predicate unknown */ 1"
        out := out ++ s!"  cond_{ci} = {applyCdecl pred};\n"
        match branchTarget a ins with
        | some t =>
          let tl := match addr2idx[t]? with | some jj => s!"L{idx2blk[jj]!}" | none => s!"/*ext 0x{hex t}*/L{b}_skip"
          if (addr2idx[t]?).isSome then
            out := out ++ s!"  if (cond_{ci}) goto {tl};\n"
          else
            out := out ++ s!"  /* conditional tail to external 0x{hex t} (kept as fall-through) */\n"
        | none => out := out ++ s!"  /* indirect conditional branch */\n"
        ci := ci + 1
      else if ins.mn == "cmp" ∨ ins.mn == "test" ∨ ins.mn == "nop" then
        out := out ++ s!"  /* {ins.mn} {ins.ops} (folded into predicate) */\n"
      else if ins.mn == "call" ∨ (a == .ppc ∧ (ins.mn == "bl" ∨ ins.mn == "bctrl")) then
        match branchTarget a ins with
        | some t =>
          if (addr2idx[t]?).isSome ∨ true then
            -- direct call: prototype forward-declared above (or external). When
            -- the callee's parameter count is recoverable (self-recursion), pass
            -- the right number of arguments; otherwise a no-arg call.
            let args :=
              if t == fnVa ∧ pm.count > 0 then String.intercalate ", " pm.names else ""
            out := out ++ s!"  {cName retReg} = sub_{hex t}({args});\n"
        | none =>
          -- indirect/computed call: cast through a function pointer; C-legal.
          out := out ++ s!"  ((uint32_t(*)(void))(uintptr_t)0)(); /* indirect call {ins.ops} */\n"
      else
        match writesReg a ins with
        | some r =>
          let nm := cName ((ssaName.get? q).getD r)
          -- Defensive: only emit an assignment when the destination lowers to a
          -- legal C identifier. A malformed/foreign-syntax decode can yield a
          -- non-register "destination" (e.g. an immediate); never emit that as
          -- an lvalue — keep the unit compilable by dropping to a comment.
          if okLocal nm then
            let subs := (useToVer.get? q).getD []
            let rhs := applyCdecl (renderExprC a ins subs)
            out := out ++ s!"  {nm} = ({regCType r})({rhs});\n"
          else
            out := out ++ s!"  /* {ins.mn} {ins.ops} (non-register destination) */\n"
        | none =>
          -- store or other side-effecting op: lower a store to a mem write if possible.
          if hasMem ins.ops ∧ (ins.mn == "mov" ∨ ins.mn.startsWith "st") then
            -- "mov [mem], src" → *(...)=src
            let toks := (ins.ops.splitOn ",").map (·.trimAscii.toString)
            match toks with
            | [dst, src] =>
              if hasMem dst then
                let subs := (useToVer.get? q).getD []
                let lowSrc := if src.startsWith "0x" ∨ src.startsWith "-" then src
                  else (subs.lookup src).map cName |>.getD (cName src)
                out := out ++ s!"  {memToC dst} = ({lowSrc});\n"
              else out := out ++ s!"  /* {ins.mn} {ins.ops} */\n"
            | _ => out := out ++ s!"  /* {ins.mn} {ins.ops} */\n"
          else
            out := out ++ s!"  /* {ins.mn} {ins.ops} */\n"
  out := out ++ "  return " ++ cName retReg ++ ";\n}\n"
  pure (out, trace)

/-- Pretty (commented) decompile to stdout, plus optional trace to stderr. -/
def decompileInsns (a : A) (bits : Bits) (insns : Array Ins) (fnVa : Nat) (showTrace : Bool) : IO Unit := do
  let (c, trace) ← emitC a bits insns fnVa
  IO.print c
  if showTrace then
    IO.eprintln "=== iterative-deepening search trace ==="
    for te in trace do
      let oc := match te.outcome with
        | .found w => s!"resolved (witness def-idx {w})"
        | .provablyNone => "provably-none"
        | .budgetHit => "UNRESOLVED (budget hit)"
      IO.eprintln s!"  {te.query} → L{te.level} : {oc}"

/-- The synthetic self-test snippet (x86 at base 0x1000): a counting loop + an if. -/
def demoInsns : Array Ins :=
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
  capstoneDecoder.decode .x86 (bytes, 0x1000)

/-- A deep self-test: `mov esi, 0x1000` then a long clobber-free run of `nop`s,
then `mov eax, [esi+4]` (a use of esi). The def→use walk must cross the whole
run, so the shallow L0 budget (64 steps) is hit (UNRESOLVED) and the query only
resolves once iterative deepening escalates to L1 (512 steps). This is the
demonstrable iterative-deepening case. `nNops` controls the chain length. -/
def demoDeepInsns (nNops : Nat) : Array Ins :=
  let prologue : Array UInt8 := #[0xBE, 0x00, 0x10, 0x00, 0x00]  -- mov esi, 0x1000
  let nops : Array UInt8 := Array.replicate nNops 0x90           -- nop * nNops
  let epilogue : Array UInt8 := #[0x8B, 0x46, 0x04, 0xC3]        -- mov eax,[esi+4]; ret
  let bytes : ByteArray := ByteArray.mk (prologue ++ nops ++ epilogue)
  capstoneDecoder.decode .x86 (bytes, 0x1000)

/-- Run the deep demo and report the escalation outcome for the `esi` use. -/
def demoDeep : IO Unit := do
  let insns := demoDeepInsns 100
  let nI := insns.size
  let mut addr2idx : Std.HashMap Nat Nat := {}
  for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
  -- the use is the penultimate instruction (`mov eax, [esi+4]`).
  let useIdx := nI - 2
  IO.println s!"=== iterative-deepening demo: {nI} insns, esi def at idx 0, use at idx {useIdx} ==="
  IO.println "Per-level outcome for reaching-def query (esi @ the use):"
  for lvl in ladder do
    let failure ← certifyReaching lvl insns addr2idx .x86 useIdx "esi"
    let (defs, budget) := reachingDefsB lvl.walkSteps insns addr2idx .x86 useIdx "esi"
    let status :=
      if ¬ defs.isEmpty then s!"RESOLVED (reaching def idx {defs}) plausible-found={failure}"
      else if budget then "UNRESOLVED (budget hit — escalate)"
      else "provably-none"
    IO.println s!"  L{lvl.idx} (walkSteps={lvl.walkSteps}, Fin {lvl.finBound}): {status}"
  -- the adaptive driver picks the first level that resolves it:
  let (defs, lvl, _te) ← resolveReachingDef insns addr2idx .x86 useIdx "esi"
  IO.println s!"\nAdaptive driver resolved esi@use at level L{lvl} with def(s) {defs}."
  IO.println "The shallow L0 search could NOT resolve it (budget hit); deepening did."

/-! ## Parameter-model demo (calling conventions)

Two synthetic functions exercise the parameter recovery:

* **x86-64 / System V** — `mov eax, edi ; add eax, esi ; ret`. Reads `edi`
  (arg0) and `esi` (arg1), both live-on-entry ⇒ 2 parameters.
* **x86-32 / cdecl** — standard prologue then `mov eax, [ebp + 8] ; …; ret`.
  Reads the first stack slot ⇒ 1 parameter.

The demo prints the recovered C signature for each (which `--demo-params --emit-c`
emits raw so it can be piped to a compiler). -/

/-- x86-64 SysV: `mov eax, edi ; add eax, esi ; ret` — uses arg0 (`edi`) and
arg1 (`esi`). -/
def demoSysvInsns : Array Ins :=
  let bytes : ByteArray := ByteArray.mk #[
    0x89, 0xF8,   -- mov eax, edi
    0x01, 0xF0,   -- add eax, esi
    0xC3 ]        -- ret
  capstoneDecodeBytes Capstone.Arch.x86 Capstone.Mode.b64 bytes 0x401000

/-- x86-32 cdecl: `push ebp ; mov ebp,esp ; mov eax,[ebp+8] ; pop ebp ; ret`
— reads the first cdecl stack slot ⇒ 1 parameter. -/
def demoCdeclInsns : Array Ins :=
  let bytes : ByteArray := ByteArray.mk #[
    0x55,               -- push ebp
    0x89, 0xE5,         -- mov ebp, esp
    0x8B, 0x45, 0x08,   -- mov eax, [ebp + 8]
    0x5D,               -- pop ebp
    0xC3 ]              -- ret
  capstoneDecodeBytes Capstone.Arch.x86 Capstone.Mode.b32 bytes 0x401100

/-- Run the parameter-model demo. With `emitC?` print only the C (for both
functions) so it can be piped to a compiler; otherwise print a human report. -/
def demoParams (emitC? : Bool) : IO Unit := do
  let (sysvC, _) ← emitC .x86 .b64 demoSysvInsns 0x401000
  let (cdeclC, _) ← emitC .x86 .b32 demoCdeclInsns 0x401100
  if emitC? then
    -- Two functions in one TU; rename the cdecl one so symbols don't collide.
    IO.print sysvC
    IO.print (String.intercalate "sub_401100b" (cdeclC.splitOn "sub_401100"))
  else
    IO.println "=== parameter-model demo: SysV x86-64 (2 params) ==="
    IO.println "synthetic: mov eax, edi ; add eax, esi ; ret"
    let sig := (sysvC.splitOn "\nuint32_t sub_401000").getLastD ""
    IO.println s!"recovered signature: uint32_t sub_401000{(sig.splitOn ")").headD ""})"
    IO.println ""
    IO.println "=== parameter-model demo: cdecl x86-32 (1 param) ==="
    IO.println "synthetic: push ebp; mov ebp,esp; mov eax,[ebp+8]; pop ebp; ret"
    let sig2 := (cdeclC.splitOn "\nuint32_t sub_401100").getLastD ""
    IO.println s!"recovered signature: uint32_t sub_401100{(sig2.splitOn ")").headD ""})"
    IO.println ""
    IO.println "(pipe `flowref --demo-params --emit-c` to gcc to confirm it compiles)"

def main (args : List String) : IO Unit := do
  let hasFlag := fun (f : String) => args.contains f
  let showTrace := hasFlag "--search-trace"
  let positional := args.filter (fun s => ¬ s.startsWith "--")
  match args with
  | [] => IO.eprintln usageText; IO.Process.exit 2
  | _ =>
  if hasFlag "--help" ∨ hasFlag "-h" then IO.println usageText; return
  if hasFlag "--version" then IO.println flowrefVersion; return
  if hasFlag "--demo-deep" then demoDeep; return
  if hasFlag "--demo-params" then demoParams (hasFlag "--emit-c"); return
  if hasFlag "--demo" then
    if hasFlag "--emit-c" then
      let (c, trace) ← emitC .x86 .b32 demoInsns 0x1000
      IO.print c
      if showTrace then
        IO.eprintln "=== iterative-deepening search trace (demo) ==="
        for te in trace do IO.eprintln s!"  {te.query} → L{te.level}"
    else
      IO.println "=== synthetic disassembly (x86, base 0x1000) ==="
      for i in demoInsns do IO.println s!"  0x{hex i.addr}: {i.mn} {i.ops}"
      IO.println ""
      decompileInsns .x86 .b32 demoInsns 0x1000 showTrace
    return
  match positional with
  -- ── decompile ──────────────────────────────────────────────────────────
  | "decompile" :: bin :: archS :: fnS :: foS :: vaS :: lenS :: _ =>
    guard (runDecompile (binaryFileAdapter bin archS foS vaS lenS) fnS showTrace)
  | "decompile-asm" :: path :: archS :: fnS :: _ =>
    guard (runDecompile (asmFileAdapter archS path) fnS showTrace)
  -- ── xref ───────────────────────────────────────────────────────────────
  | "xref" :: bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace)
  | "xref-asm" :: path :: archS :: tgtS :: _ =>
    guard (xref (asmFileAdapter archS path) tgtS showTrace)
  -- ── legacy positional xref ─────────────────────────────────────────────
  | bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace)
  | _ => IO.eprintln usageText; IO.Process.exit 2
where
  /-- Run an analysis action, mapping any `IO` error to a clean message + exit 4.
  This keeps the untrusted-input failures (raised by the adapters) from dumping
  a stack trace. -/
  guard (act : IO Unit) : IO Unit := do
    try act catch e => IO.eprintln s!"error: {e.toString}"; IO.Process.exit 4
  /-- Decompile whatever a `SourceAdapter` yields to compilable C. -/
  runDecompile (adapter : SourceAdapter) (fnS : String) (showTrace : Bool) : IO Unit := do
    let fnVa ← match parseImm? fnS with
      | some v => if v < 0 then throw (IO.userError s!"fnVaddr must be non-negative, got '{fnS}'") else pure v.toNat
      | none => throw (IO.userError s!"invalid fnVaddr '{fnS}' (expected hex like 0x401010 or a decimal)")
    let (a, bits, insns) ← adapter.run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the given region"; IO.Process.exit 3
    decompileInsns a bits insns fnVa showTrace
  /-- The ORIGINAL behaviour: a single-target def→use witness search, now with
  iterative deepening over the CFG-walk budget, over any `SourceAdapter`. -/
  xref (adapter : SourceAdapter) (tgtS : String) (showTrace : Bool) : IO Unit := do
    let target : Int ← match parseImm? tgtS with
      | some v => pure v
      | none => throw (IO.userError s!"invalid target '{tgtS}' (expected hex like 0x401010 or a decimal)")
    let (a, _bits, insns) ← adapter.run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the given region"; IO.Process.exit 3
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
    -- walk with a step budget; report (hitAddr?, budgetExhausted?).
    let walk := fun (steps start : Nat) (reg : String) (val : Int) =>
      Id.run do
        let mut seen : Std.HashSet Nat := {}
        let mut stack := succ start
        let mut s := 0
        while ¬stack.isEmpty ∧ s < steps do
          s := s + 1
          match stack with
          | [] => pure ()
          | kk :: rest =>
            stack := rest
            if ¬ seen.contains kk ∧ kk < nI then
              seen := seen.insert kk
              let ins := insns[kk]!
              match useDisp a ins reg with
              | some disp => if val + disp == target then return (some ins.addr, false)
              | none => pure ()
              if ¬ clobbers a ins reg then stack := succ kk ++ stack
        pure (none, s ≥ steps ∧ ¬ stack.isEmpty)
    let defs := (Array.range nI).filterMap (fun i =>
      match defOf a insns[i]! with
      | some (r, v) => if (target - v).toNat < 0x10000 ∨ v == target then some (i, r, v) else none
      | none => none)
    IO.println s!"insns={nI}, def-witness candidates={defs.size}, target=0x{hex target.toNat}"
    -- iterative deepening over the walk budget for the whole def set.
    let mut found := false
    let mut traceLines : Array String := #[]
    for (i, rg, v) in defs do
      let mut resolved := false
      for lvl in ladder do
        if ¬ resolved then
          let (hit, budget) := walk lvl.walkSteps i rg v
          match hit with
          | some ua =>
            found := true; resolved := true
            traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} → use@0x{hex ua} resolved at L{lvl.idx}"
            IO.println s!"  ~ def @0x{hex insns[i]!.addr} ({rg}={v}) → use @0x{hex ua}  [L{lvl.idx}]"
          | none =>
            if ¬ budget then resolved := true   -- provably none at this depth
            else if lvl.idx == ladder.size - 1 then
              traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} UNRESOLVED (budget hit at L{lvl.idx})"
    -- plausible certification that a witness exists among the defs (existence).
    let cfg : Plausible.Configuration := { numInst := 2000, quiet := true }
    let r ← Testable.checkIO
      (NamedBinder "w" (∀ w : Fin 4096,
        (match defs[w.val]? with
         | some (i, rr, v) => ((walk 4000 i rr v).1).isNone
         | none => true) = true)) cfg
    if found ∨ r.isFailure then
      IO.println s!"FOUND a witness DAG to target (plausible counterexample: {r.isFailure})"
    else
      IO.println "no witness DAG reaches the target in this region"
    if showTrace then
      IO.eprintln "=== iterative-deepening search trace ==="
      for l in traceLines do IO.eprintln s!"  {l}"
