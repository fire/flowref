import Flowref.Disasm
import Plausible
import PlausibleWitnessDag

/-! # flowref — plausible-driven data-flow with an iterative-deepening witness DAG

Every data-flow fact is recovered as a **counterexample** to a plausible
property, *not* by a classical worklist / SSA / dominator fixpoint. The original
xref trick — pose `∀ candidate witness, ¬(it is the fact we want)` and read the
counterexample plausible returns — is generalised to reaching definitions,
back-edges, and reachability.

## Iterative deepening (the search DAG)

A single fixed search budget cannot serve both a 10-instruction leaf and a
1000-instruction function: too shallow and a real def→use path is missed; too
deep and every query pays for the worst case. So each query is parameterised by
a **level** `L` (a CFG-walk step budget + a plausible `Fin N` candidate window +
a plausible instance count `numInst`). We run `L0` (cheap, shallow); if a query
is *unresolved* — no witness AND the budget was demonstrably hit (so we cannot
conclude "provably none") — we **escalate** that query to `L1`, then `L2`, up to
a hard cap. Resolved queries never re-run; only the unresolved frontier
deepens. The escalation forms a DAG: a node's resolved result feeds dependents,
and the frontier of unresolved nodes is what deepens. The chain (which query
needed which depth) is recorded and can be printed with `--search-trace`.

This is the project's "chain of conditional witnesses that deepen based on
evidence — a witness DAG" idea, made literal.
-/

open Plausible

namespace Flowref

/-- One rung of the iterative-deepening ladder. Re-exported from the standalone
`fire/plausible-witness-dag` package for existing `Flowref.Dataflow` callers. -/
abbrev Level := PlausibleWitnessDag.Level

/-- The escalation ladder. -/
def ladder : Array Level := PlausibleWitnessDag.ladder

/-- Outcome of one plausible query at a given level. -/
abbrev Outcome := PlausibleWitnessDag.Outcome

/-- A trace entry: which query resolved at which level, with what outcome. -/
abbrev TraceEntry := PlausibleWitnessDag.TraceEntry

/-! ## Instruction-level reachability (the witness walk)

`insReaches steps insns addr2idx a i j r` is true iff there is a CFG path
`i → … → j` along which `r` is never clobbered, found within `steps` budget.
The companion `insReachesBudget` reports whether the walk *exhausted* its budget
(so a `false` result is "ran out", not "none"). -/

private def succI (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat) (a : A) (nI x : Nat) : List Nat :=
  let ins := insns[x]!
  let ft := if isUncondJmp a ins ∨ x+1 ≥ nI then [] else [x+1]
  let bt := match branchTarget a ins with
    | some t => match addr2idx[t]? with | some q => [q] | none => ([] : List Nat)
    | none => ([] : List Nat)
  ft ++ bt

/-- Reaches with a budget; returns (reached?, budgetExhausted?). -/
def insReachesB (steps : Nat) (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (i j : Nat) (r : String) : Bool × Bool :=
  Id.run do
    let nI := insns.size
    let mut seen : Std.HashSet Nat := {}
    let mut stack := succI insns addr2idx a nI i
    let mut s := 0
    while ¬ stack.isEmpty ∧ s < steps do
      s := s + 1
      match stack with
      | [] => pure ()
      | x :: rest =>
        stack := rest
        if ¬ seen.contains x ∧ x < nI then
          seen := seen.insert x
          if x == j then return (true, false)
          if ¬ clobbers a insns[x]! r then stack := succI insns addr2idx a nI x ++ stack
    -- exhausted the frontier (false) vs hit the step cap (budget exhausted).
    pure (false, s ≥ steps ∧ ¬ stack.isEmpty)

/-- Is `i` a reaching def of `(j, r)` within the step budget?
Returns (isReaching?, budgetExhausted?). -/
def isReachingDefB (steps : Nat) (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (i j : Nat) (r : String) : Bool × Bool :=
  if writesReg a insns[i]! != some r then (false, false)
  else if i == j then (true, false)
  else insReachesB steps insns addr2idx a i j r

/-- Deterministic recovery of all reaching defs of `(j,r)` at a given step
budget, with whether any query along the way hit its budget. -/
def reachingDefsB (steps : Nat) (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (j : Nat) (r : String) : List Nat × Bool :=
  Id.run do
    let nI := insns.size
    let mut out : List Nat := []
    let mut budget := false
    for i in [0:nI] do
      if i < j then
        let (rd, b) := isReachingDefB steps insns addr2idx a i j r
        if rd then out := out ++ [i]
        if b then budget := true
    pure (out, budget)

/-! ## Plausible certification, specialised per literal `Fin N`

plausible needs a *literal* `Fin N` bound (it cannot take a variable). We
therefore provide one certifier per ladder bound. Each poses
`∀ w : Fin N, ¬(candidate w is a reaching def)` and lets plausible find the
counterexample; `isFailure` means "a witness exists" (the fact we want). -/

private def candIsReaching (steps : Nat) (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (j : Nat) (r : String) (w : Nat) : Bool :=
  if w < j then (isReachingDefB steps insns addr2idx a w j r).1 else false

/-- Run plausible at one ladder level. Returns the `isFailure` flag
(true ⇒ plausible found a counterexample ⇒ a reaching def exists). -/
def certifyReaching (lvl : Level) (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (j : Nat) (r : String) : IO Bool := do
  let steps := lvl.walkSteps
  PlausibleWitnessDag.certify lvl (fun w => candIsReaching steps insns addr2idx a j r w)

/-! ## The iterative-deepening driver for a single reaching-def query -/

/-- Resolve the reaching defs of `(j, r)`, escalating the ladder only while the
query is unresolved (budget hit, nothing found). Returns the recovered def list,
the level at which it resolved, and a trace entry. -/
def resolveReachingDef (insns : Array Ins) (addr2idx : Std.HashMap Nat Nat)
    (a : A) (j : Nat) (r : String) : IO (List Nat × Nat × TraceEntry) := do
  let qname := s!"reaching-def {r}@0x{hex insns[j]!.addr}"
  PlausibleWitnessDag.resolve qname
    (fun lvl w => candIsReaching lvl.walkSteps insns addr2idx a j r w)
    (fun steps =>
      let (defs, budgetHit) := reachingDefsB steps insns addr2idx a j r
      { value := defs, found := !defs.isEmpty, witnessIdx := defs.headD 0,
        budgetHit := budgetHit })
    ladder

end Flowref
