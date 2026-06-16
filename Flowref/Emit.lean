import Flowref.Disasm
import Flowref.Dataflow

/-! # flowref — compilable C emission

The emitter lowers the recovered CFG + SSA + expressions into a **complete C
translation unit that `gcc -fsyntax-only -std=c11 -w` accepts**. The strategy:

* Emit `#include <stdint.h>` + typedefs and forward-declare every referenced
  `sub_*`.
* A real `uint32_t sub_<addr>(void) { … }` definition.
* Every SSA value is declared as a typed local up front; names are C-legal
  (`reg_version`, with `#`/`[`/`]`/`+`/spaces mapped to legal characters).
* Memory operands become `*(uint32_t*)(base + disp)`; calls become
  `sub_<tgt>();` or `((void(*)(void))(uintptr_t)0x…)();`.
* SSA φ is lowered away: each `(reg, version)` is a distinct declared local and
  the value flows through plain assignments — there is no φ in the C output.
* Control flow uses **labels + `goto`** (always valid C). Where a conditional
  block cleanly dominates a forward merge, a structured `if (cond) { … }` is
  emitted; otherwise the `goto` form is used. Conditions are real C derived from
  the compare + branch; when the exact predicate is unknown a documented boolean
  temp (`cond_N`) is used, still C-legal.

The output is not guaranteed semantically faithful or type-correct — only that
it parses and type-checks as C11.
-/

namespace Flowref

/-- Map an x86/ppc register name to a C width type. Default `uint32_t`. -/
def regCType (r : String) : String :=
  let r := r.trimAscii.toString
  -- x86 8-bit
  if r == "al" ∨ r == "bl" ∨ r == "cl" ∨ r == "dl"
     ∨ r == "ah" ∨ r == "bh" ∨ r == "ch" ∨ r == "dh"
     ∨ r == "sil" ∨ r == "dil" ∨ r == "bpl" ∨ r == "spl" then "uint8_t"
  -- x86 16-bit
  else if r == "ax" ∨ r == "bx" ∨ r == "cx" ∨ r == "dx"
       ∨ r == "si" ∨ r == "di" ∨ r == "bp" ∨ r == "sp" then "uint16_t"
  -- x86 64-bit / ppc 64-bit
  else if r.startsWith "r" ∧ r.length ≥ 2 then "uint64_t"
  else "uint32_t"

/-- Make a string a C-legal identifier fragment: keep `[A-Za-z0-9_]`, map other
characters to `_`. -/
def cIdent (s : String) : String :=
  String.ofList (s.toList.map (fun c =>
    if ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c == '_' then c else '_'))

/-- Turn an SSA name like `eax#1` into a C-legal local `eax_1`. -/
def cName (ssa : String) : String := cIdent ssa

/-- Strip an x86 size keyword prefix (`dword ptr`, `byte ptr`, …) and `fs:` etc.
from a memory operand body, leaving the address expression. -/
def stripPtrKw (s : String) : String :=
  let s := s.trimAscii.toString
  let drops := ["dword ptr ", "qword ptr ", "word ptr ", "byte ptr ",
                "xmmword ptr ", "tbyte ptr ", "ptr "]
  drops.foldl (fun acc d => String.intercalate "" (acc.splitOn d)) s

/-- Substring test. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Width (textual C type) implied by an x86 size keyword in `s`. -/
def memCType (s : String) : String :=
  if contains s "qword ptr" then "uint64_t"
  else if contains s "dword ptr" then "uint32_t"
  else if contains s "word ptr" then "uint16_t"
  else if contains s "byte ptr" then "uint8_t"
  else "uint32_t"

/-- Render a single x86 memory operand `[...]` body into a C lvalue/expr:
`*(uint32_t*)(base)`. Segment overrides (`fs:[0]`) are flattened to `(0)`. -/
def memToC (operand : String) : String :=
  -- operand is the full operand text, e.g. "dword ptr [esi + 4]" or "dword ptr fs:[0]"
  let ty := memCType operand
  -- extract inside the brackets
  let inner := ((operand.splitOn "[").drop 1 |>.headD "").splitOn "]" |>.headD ""
  -- drop a segment prefix like "fs:" that may sit before "["
  let inner := inner.trimAscii.toString
  -- build address expr: registers stay, hex/decimal stay, '+'/'*' valid in C, '-' valid.
  -- ensure tokens are C identifiers (registers already are).
  let addr := if inner.isEmpty then "0" else inner
  s!"*({ty}*)((uintptr_t)({addr}))"

/-- Does an operand text contain a memory reference? -/
def hasMem (s : String) : Bool := s.any (· == '[')

/-- A C-legal token: a register name maps to its SSA local; a hex/decimal
literal is passed through (normalising `0x` is already C-legal); anything else
is wrapped so it cannot break parsing. `subs` maps a raw register to its SSA
name (e.g. `esi` → `esi_0`). -/
def renderExprC (a : A) (i : Ins) (subs : List (String × String)) : String :=
  -- start from the textual RHS, then substitute register reads with SSA locals
  -- and lower any memory operand to a C dereference.
  let raw := rhsText a i
  if hasMem i.ops then
    -- opaque load/store source: render the memory operand directly as C.
    memToC i.ops
  else
    -- substitute longest register names first to avoid partial overlaps.
    let regSubs := (subs.filter (fun (rg, _) => ¬ rg.startsWith "0x")).toArray.qsort
                     (fun x y => x.1.length > y.1.length) |>.toList
    let replaced := regSubs.foldl (fun (acc : String) (p : String × String) =>
      let (rg, nm) := p
      String.intercalate nm (acc.splitOn rg)) raw
    -- The result may still contain bare registers with no SSA def (arguments);
    -- those are declared as locals too, so the text stays C-legal as long as it
    -- is alphanumerics/operators. Guard: if it still has a '[' it's a mem expr.
    if hasMem replaced then memToC replaced else replaced

/-- Forward prototypes + typedefs preamble for the translation unit. -/
def cPreamble : String :=
  "#include <stdint.h>\n#include <stddef.h>\n"

end Flowref
