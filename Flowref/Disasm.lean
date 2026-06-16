/-! # flowref — instruction model (the analysis **kernel**, decoder-agnostic)

This module is the interior of the hexagon: the architecture-neutral
instruction model (`Ins`, `A`, `BB`) and the pattern-based helpers
(def / use / clobber / branch-target) that the data-flow search and the emitter
consume. It is plain structural code with **no I/O and no dependency on
Capstone** — it speaks only the `Ins` model, and never knows whether those
instructions were decoded from machine-code bytes, an objdump listing, or a
dataset row. Turning raw bytes/text into `Ins` is the job of the *decoders*
(`Flowref/Decoders.lean`); fetching the bytes/text is the job of the *adapters*
(`Flowref/Adapters.lean`). See `Flowref/Ports.lean` for the port definitions.
-/

namespace Flowref

/-- Parse a hex (`0x…`) or decimal integer, optionally signed. Best-effort:
invalid characters are skipped. Use this for *disassembler-produced* operand
text, where the input is trusted to be well-formed. For **user-supplied** CLI
arguments use `parseImm?`, which rejects malformed input instead of silently
returning a wrong address. -/
def parseImm (s0 : String) : Int :=
  let s := s0.trimAscii.toString
  let (neg, t) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let t := if t.startsWith "0x" then (t.drop 2).toString else t
  let v : Int := t.toList.foldl (fun n c =>
    if '0' ≤ c ∧ c ≤ '9' then n*16 + (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then n*16 + (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then n*16 + (c.toNat - 'A'.toNat + 10) else n) 0
  if neg then -v else v

/-- Strict parse of a hex (`0x…`/`0X…`) or decimal integer, optionally signed.
Returns `none` on an empty string, a missing digit, or **any** invalid
character — so a mistyped address (`0xZZ`, `10g`, `--`) is rejected at the CLI
boundary rather than silently misinterpreted as the wrong region. -/
def parseImm? (s0 : String) : Option Int :=
  let s := s0.trimAscii.toString
  if s.isEmpty then none else
  let (neg, t0) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let (isHex, t) :=
    if t0.startsWith "0x" ∨ t0.startsWith "0X" then (true, (t0.drop 2).toString) else (false, t0)
  if t.isEmpty then none else
  let base : Nat := if isHex then 16 else 10
  let digit? := fun (c : Char) =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if isHex ∧ 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if isHex ∧ 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  (t.toList.foldl (fun acc c => match acc, digit? c with
    | some n, some d => some (n * base + d)
    | _, _ => none) (some 0)).map (fun n => if neg then -(Int.ofNat n) else Int.ofNat n)

/-- Lower-case hex string of a Nat (no `0x` prefix). -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

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
  let isRegTok (s : String) : Bool :=
    let s := s.trimAscii.toString
    ¬ s.isEmpty ∧ ¬ s.startsWith "0x" ∧ ¬ s.startsWith "-"
      ∧ s.all (fun c => ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9'))
  let flat := raw.toList.map (fun c =>
    if c == '[' ∨ c == ']' ∨ c == '(' ∨ c == ')' ∨ c == '+' ∨ c == '*' ∨ c == ' ' then ',' else c)
  let toks := (String.ofList flat).splitOn "," |>.map (·.trimAscii.toString) |>.filter isRegTok
  let dst := match writesReg a i with | some d => d | none => ""
  let keepDst := i.mn != "mov" ∧ i.mn != "lea" ∧ i.mn != "movzx" ∧ i.mn != "movsx"
                 ∧ i.mn != "li" ∧ i.mn != "lis" ∧ i.mn != "mr"
  toks.filter (fun t => keepDst ∨ t != dst) |>.eraseDups

/-- The textual right-hand side of `i` for expression reconstruction. -/
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

/-- Resolve an arch name to its kernel **pattern family** (the textual
def/use/branch patterns are shared by all x86 widths). `none` ⇒ unsupported.
Pure: the adapters that read bytes/text turn `none` into an `IO.userError`.
The Capstone decode *mode* (32- vs 64-bit) is a separate axis chosen by the
decoder — see `capstoneSpec?` in `Flowref/Decoders.lean`. -/
def archOfString? (s : String) : Option A :=
  match s.trimAscii.toString with
  | "x86" | "x86-32" | "i386" | "x64" | "x86-64" | "amd64" => some .x86
  | "ppc" | "ppc64" => some .ppc
  | _     => none

end Flowref
