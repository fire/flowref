import Flowref.Disasm
import Flowref.Dataflow
import Plausible

/-! # flowref — calling-convention parameter model

A linear/CFG decompiler can recover a function *body*, but without a calling
convention it cannot know the function's **signature**: it falls back to
`uint32_t sub_X(void)`. This module recovers the integer/pointer **parameters**
of a function from the platform calling convention, so the emitter can print a
real C prototype `uint32_t sub_X(uint32_t a0, uint32_t a1, …)` and pass the
right argument count at call sites.

## Conventions modelled

* **x86-64 System V AMD64 ABI** (`Conv.sysv`). The first six integer/pointer
  arguments are passed in registers, in this order:

  ```
  arg0 = rdi   arg1 = rsi   arg2 = rdx   arg3 = rcx   arg4 = r8   arg5 = r9
  ```

  (further integer args, and everything that does not fit the integer class,
  go on the stack — we do not model those). A function *uses* parameter `k`
  exactly when arg-register `k` is **live on entry**: it is *read before it is
  written* on some path from the entry. We take the **highest consecutive**
  arg register that is live-on-entry as the parameter count: a function that
  reads `rdi` and `rdx` but not `rsi` is reported as 1 parameter (`rdi`), since
  a real two-arg-skipping signature is not recoverable from register liveness
  alone — consecutiveness is the honest heuristic.

* **x86-32 cdecl** (`Conv.cdecl`). Integer arguments are passed on the stack.
  After the standard prologue `push ebp ; mov ebp, esp` they are read as
  `[ebp + 8]`, `[ebp + 0xC]`, `[ebp + 0x10]`, … (slot `k` at `ebp + 8 + 4*k`);
  without a frame pointer they are `[esp + 4]`, `[esp + 8]`, … (slot `k` at
  `esp + 4 + 4*k`). A parameter `k` is *used* when the function **reads** its
  stack slot. As with SysV we take the highest consecutive slot that is read.

The convention is selected from the arch/decode width: x86 decoded 64-bit →
SysV; x86 decoded 32-bit → cdecl. PowerPC is left unmodelled (0 params) for now.

## Honest limits

* **Integer/pointer arguments only.** Floating-point/SSE arguments (xmm
  registers under SysV) are not modelled, struct-by-value is not modelled, and
  varargs are not modelled.
* **Param count is a heuristic.** It is the highest *consecutive* arg
  slot/register that is live-on-entry (SysV) or read (cdecl). A function that
  genuinely skips an argument register, or that only conditionally touches a
  later argument, can be under- or mis-counted. This is a recovery aid, not a
  ground-truth signature.

## Plausible reuse

Liveness-on-entry for a candidate SysV arg register is *exactly* the existing
reaching-def query: arg register `r` is a parameter iff some read of `r` has
**no** reaching definition inside the function (its value comes from the
caller). We therefore reuse `resolveReachingDef` (the plausible-driven,
iteratively-deepened witness search) rather than writing a new bespoke
liveness pass — `[]` reaching defs for a real read *is* the live-on-entry
witness.
-/

open Plausible

namespace Flowref

/-- The decode width / bitness, threaded from the decoder (which alone knows
whether Capstone ran in 32- or 64-bit mode) into the parameter model. -/
inductive Bits | b32 | b64 deriving DecidableEq, Repr, Inhabited

/-- A calling convention. -/
inductive Conv | sysv | cdecl | unknown deriving DecidableEq, Repr, Inhabited

/-- Pick the calling convention from the architecture family and decode width.
x86-64 → System V AMD64; x86-32 → cdecl; anything else → unknown. -/
def convOf (a : A) (bits : Bits) : Conv :=
  match a, bits with
  | .x86, .b64 => .sysv
  | .x86, .b32 => .cdecl
  | _,    _    => .unknown

/-- The SysV AMD64 integer-argument registers, in parameter order, each given as
the set of width aliases naming the same physical register (so a function that
takes the value in `edi`/`dil` is still recognised as using arg0). Parameter `k`
is named by any alias in `sysvArgAliases[k]`. -/
def sysvArgAliases : List (List String) :=
  [ ["rdi", "edi", "di", "dil"],
    ["rsi", "esi", "si", "sil"],
    ["rdx", "edx", "dx", "dl"],
    ["rcx", "ecx", "cx", "cl"],
    ["r8",  "r8d", "r8w", "r8b"],
    ["r9",  "r9d", "r9w", "r9b"] ]

/-- The canonical (64-bit) arg registers, in parameter order. -/
def sysvArgRegs : List String := sysvArgAliases.map (·.headD "")

/-- Parameter index `k` whose physical register `r` aliases, if any. -/
def sysvArgIndexOf (r : String) : Option Nat :=
  (List.range sysvArgAliases.length).find? (fun k =>
    ((sysvArgAliases.getD k []).contains r))

/-- A read of arg register `r` is **live on entry** (hence a parameter) iff some
read of `r` in the function has no reaching definition inside the function — its
value must have come from the caller. Reuses the plausible-driven, iteratively
deepened reaching-def search: an empty reaching-def set for a genuine read *is*
the live-on-entry witness.

Returns `true` when `r` is live on entry. -/
def sysvArgLiveOnEntry (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (aliases : List String) : IO Bool := do
  let nI := insns.size
  let mut found := false
  for q in [0:nI] do
    if ¬ found then
      let reads := readsRegs .x86 insns[q]!
      for r in aliases do
        if ¬ found ∧ reads.contains r then
          -- A read of an alias of this arg register with no reaching def inside
          -- the function is fed by the caller ⇒ the parameter is used.
          let (defs, _lvl, _te) ← resolveReachingDef insns addr2idx .x86 q r
          if defs.isEmpty then found := true
  pure found

/-- SysV parameter count: the highest **consecutive** arg register
(`rdi, rsi, rdx, rcx, r8, r9`, any width alias) that is live on entry. -/
def sysvParamCount (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat) : IO Nat := do
  let mut n := 0
  let mut stop := false
  for aliases in sysvArgAliases do
    if ¬ stop then
      let live ← sysvArgLiveOnEntry insns addr2idx aliases
      if live then n := n + 1 else stop := true
  pure n

/-- The cdecl stack slot text that parameter `k` is read through, for both the
frame-pointer (`ebp + …`) and no-frame (`esp + …`) forms. Slot `k` sits at
`ebp + 8 + 4*k` (or `esp + 4 + 4*k`). Returned as the displacement integers the
kernel's `useDisp`/operand text exposes. -/
def cdeclEbpDisp (k : Nat) : Int := 8 + 4 * (k : Int)
def cdeclEspDisp (k : Nat) : Int := 4 + 4 * (k : Int)

/-- Does the function read the cdecl stack slot for parameter `k` — i.e. a
memory operand `[ebp + (8+4k)]` or `[esp + (4+4k)]`? Reuses the kernel's
`useDisp` (the same displacement reader the witness walk uses). -/
def cdeclSlotRead (insns : Array Ins) (k : Nat) : Bool := Id.run do
  let nI := insns.size
  let ebp := cdeclEbpDisp k
  let esp := cdeclEspDisp k
  let mut found := false
  for q in [0:nI] do
    if ¬ found then
      let i := insns[q]!
      match useDisp .x86 i "ebp" with
      | some d => if d == ebp then found := true
      | none => pure ()
      if ¬ found then
        match useDisp .x86 i "esp" with
        | some d => if d == esp then found := true
        | none => pure ()
  pure found

/-- cdecl parameter count: highest **consecutive** stack slot that is read. We
cap the probe at 32 slots (a generous bound for an integer-arg cdecl function). -/
def cdeclParamCount (insns : Array Ins) : Nat := Id.run do
  let mut n := 0
  let mut stop := false
  for k in [0:32] do
    if ¬ stop then
      if cdeclSlotRead insns k then n := n + 1 else stop := true
  pure n

/-- The recovered parameter model for a function. -/
structure ParamModel where
  conv   : Conv
  count  : Nat
  /-- The incoming binding sites: for SysV, `(register, paramName)`; for cdecl,
  the canonical slot operand text → paramName is handled by the emitter. -/
  names  : List String          -- ["a0", "a1", …]
  deriving Repr, Inhabited

/-- Recover the parameter model for a function under the convention chosen by
`(arch, bits)`. -/
def recoverParams (a : A) (bits : Bits) (insns : Array Ins)
    (addr2idx : Std.HashMap Nat Nat) : IO ParamModel := do
  let conv := convOf a bits
  let count ← match conv with
    | .sysv  => sysvParamCount insns addr2idx
    | .cdecl => pure (cdeclParamCount insns)
    | .unknown => pure 0
  let names := (List.range count).map (fun k => s!"a{k}")
  pure { conv, count, names }

/-- The SSA local that the emitter should substitute for a read of arg register
`r` (SysV): if `r` is `sysvArgRegs[k]` and `k < count`, it is parameter `a{k}`. -/
def sysvParamForReg (count : Nat) (r : String) : Option String :=
  match sysvArgIndexOf r with
  | some k => if k < count then some s!"a{k}" else none
  | none   => none

/-- The cdecl parameter name for a memory-operand displacement off `ebp`/`esp`,
if it names an in-range parameter slot. `base` is `"ebp"` or `"esp"`. -/
def cdeclParamForSlot (count : Nat) (base : String) (disp : Int) : Option String := Id.run do
  for k in [0:count] do
    let want := if base == "ebp" then cdeclEbpDisp k else cdeclEspDisp k
    if disp == want then return some s!"a{k}"
  pure none

end Flowref
