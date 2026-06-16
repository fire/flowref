---
name: flowref-mvp
description: The minimal viable vertical slice of flowref — the irreducible end-to-end path (bytes → compilable C whose return is provably equal to source) and the invariants/modules that must survive any trim. Use when flowref has grown bloated and you need a north star for what to keep vs cut, or to onboard the core design fast.
---

# flowref — Minimal Viable Vertical Slice

This is the **load-bearing core**. Everything else (below, "Accretion") is a layer
on top of this slice and is trimmable back toward it. When the codebase feels
bloated, trim toward this; do not trim this.

## The one-sentence product

> Raw machine-code **bytes** → a **compilable C** function whose **return value is
> provably equal** to the original source function's.

## The vertical slice (one thin path through every layer)

```
 bytes ─▶ [decode] ─▶ Ins[] ─▶ [kernel: CFG + reaching-defs] ─▶ [emit] ─▶ C ─▶ [verify]
 capstoneDecodeBytes      Disasm + Dataflow                    Emit       gcc / equiv
```

1. **Decode** — `Flowref/Decoders.lean :: capstoneDecodeBytes` : `(arch,mode,bytes,va) → Ins[]`.
   `Ins = {addr, mn, ops}` (`Flowref/Disasm.lean`). That struct is the whole contract
   between the outside world and the kernel.
2. **Kernel / CFG** — `Disasm` carves basic blocks from `branchTarget`/`isUncondJmp`.
3. **Kernel / data-flow** — `Flowref/Dataflow.lean :: reachingDefsB` : the one witness
   search. "Which def of register r reaches instruction j?" This is the plausible-driven
   idea in its smallest form.
4. **Emit** — `Flowref.lean :: emitC` + `Flowref/Emit.lean`: declare each SSA value as a
   typed C local, lower each insn, and crucially **`return <reaching-def of the return
   register>`** (not the zero-initialised base local — that wiring is what makes the
   output semantically meaningful).
5. **Verify** — `gcc -std=c11 -fsyntax-only` (compiles) and the differential equivalence
   oracle (returns the right value).

## The two proof commands (if these pass, the slice is intact)

```bash
flowref --demo --emit-c | gcc -xc -std=c11 -w -fsyntax-only -   # invariant I1: compiles
./decompile-bench/equiv-demo.sh                                 # 4/4 EQUIVALENT (I3)
```

## Invariants (never let a refactor break these)

- **I1 — emitted C always compiles** as C11. The emitter must drop anything it can't
  lower to a comment, never to invalid syntax.
- **I2 — the kernel is pure**: `Disasm`/`Dataflow`/`Emit` have **no I/O and no Capstone
  dependency**. They speak only `Ins`. (This is the hexagon; it is why decoders/arches/
  formats are added without touching analysis.)
- **I3 — `return` = reaching def of the return register** (eax / r3). Drop this and even
  `int f(){return 7;}` decompiles to something returning 0.
- **I4 — ETNF re-encoding is lossless** (`Etnf.lean` verifies `missing = extra = 0`).

## Minimal module set (the slice; keep)

| Module | Irreducible role |
|---|---|
| `Flowref/Disasm.lean` | `Ins` model, `writesReg`/`branchTarget`/CFG carving |
| `Flowref/Dataflow.lean` | `reachingDefsB` — the single witness search |
| `Flowref/Emit.lean` | `cPreamble`, `cName`, type/operand lowering |
| `Flowref.lean :: emitC` | assemble decls + body + return-SSA wiring |
| `Flowref/Decoders.lean :: capstoneDecodeBytes` | one decoder |
| `Flowref/Adapters.lean :: binaryFileAdapter` | one validated input adapter |

## Accretion (valuable, but layered ON the slice — trim here first)

- Iterative-deepening ladder + plausible **certification** (`certifyReaching`, `ladder`,
  `resolveReachingDef`) — the slice only needs `reachingDefsB` at one budget.
- All 23 Capstone arches in `capstoneSpec?` — the slice needs one.
- The objdump **asm-text decoder** + AT&T→Intel normalisation — alternate input format.
- **xref** / `--demo-deep` / `--search-trace` — alternate entrypoints + instrumentation.
- **ETNF / DuckDB** (`Etnf.lean`, dep `lean_duckdb`) — corpus storage, not decompilation.
- The Decompile-Bench equivalence harness beyond `equiv-demo.sh`.

## Known honest gaps (so "missing" isn't mistaken for "broken")

- No parameter / calling-convention model → functions emit `(void)`; equivalence is proven
  only for parameterless register-only **leaf** functions.
- Kernel pattern families are x86 (all widths) + PowerPC; other arches decode but recover
  little until a family is added.

## How to re-derive the slice from a bloated tree

Run the two proof commands. Whatever modules/symbols are in the transitive call graph of
`emitC` + `capstoneDecodeBytes` + `equiv.sh` are the slice. Everything else is Accretion —
safe to gate, feature-flag, or delete if the proofs still pass.
