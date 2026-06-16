# flowref

**Control-flow-aware cross-reference search *and* a plausible-driven decompiler
over machine-code disassembly, in Lean 4.**

A linear disassembler lists instructions but won't tell you *where a constant or
address is actually used* — the value is frequently built in one basic block and
consumed in another, so a straight-line scan loses the connection. `flowref`
recovers it by walking the control-flow graph and tracking constant values
through it. The `decompile` subcommand goes further: it lifts a whole function
into structured pseudo-C.

The defining design choice is that **every data-flow layer is driven by
[`plausible`](https://github.com/leanprover-community/plausible) (property-based
counterexample search), not by a hand-written fixpoint / worklist / dominator
algorithm.** The original xref trick — pose `∀ candidate witness, ¬(it is the
fact we want)` and let plausible hand back a *counterexample* that **is** the
fact — is generalised from one target to every use, every back-edge, every
reachability query. This is a deliberate trade-off (see *limitations*).

## Commands

```
flowref xref      <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>
flowref decompile <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex>
flowref --demo    # synthetic if + counting-loop self-test (no disk needed)
flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>  # legacy xref
```

`arch` ∈ {`x86` (32-bit), `ppc` (64-bit big-endian)}. The file offset and load
address are separate because they differ in most executable formats.

## The idea — a "witness DAG", found by property-based search

- A **def** materialises a constant base `B` into a register `R` at instruction `i`.
- A **use** at instruction `j` forms `R + disp` and equals the target address.
- They're linked by a control-flow path `i → … → j` along which `R` is never
  clobbered — that path is the **witness**.

Instead of writing a bespoke fixpoint analysis, the search is posed as a
property and discharged with [`plausible`](https://github.com/leanprover-community/plausible):

> `∀ candidate def-witness, ¬(it reaches a target-hitting use)`

A **counterexample to that property is exactly a witness** that locates the
cross-block reference. This finds the case a linear constant-propagation pass
misses: a base set in block A and used in block B reachable from A.

Disassembly comes from [Capstone](https://github.com/capstone-engine/capstone),
so the same engine works on every architecture Capstone supports. **x86** (32-bit)
and **PowerPC** (64-bit, big-endian) are wired up here; adding another is a few
lines (`defOf` / `useDisp` / `branchTarget` / `clobbers` / `isUncondJmp`).

## Build

```bash
lake update                                                  # fetch deps (incl. lean-capstone)
.lake/packages/lean-capstone/thirdparty/capstone/build.sh    # build libcapstone.a once
lake build                                                   # builds the `flowref` executable
```

## Usage

```
flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>
```

| arg          | meaning                                                        |
|--------------|----------------------------------------------------------------|
| `binary`     | path to the file to analyse                                    |
| `arch`       | `x86` or `ppc` (default `x86`)                                 |
| `targetHex`  | the address/constant to find references to (e.g. `0x4e54a3`)   |
| `fileOffHex` | start offset of the region to disassemble                      |
| `vaddrHex`   | virtual/load address that `fileOff` maps to                    |
| `lenHex`     | length of the region to disassemble                            |

The file offset and load address are separate arguments because they differ in
most executable formats (sections are mapped to addresses unrelated to their
on-disk position). Read the mapping from the file's section table first.

### Example

```bash
# Find where the address 0x550e70 is referenced within a .text window.
flowref ./program x86 0x550e70 0x1000 0x401000 0x111220
# → FOUND a witness DAG to target … ~ def @0x… (reg=…) → use @0x…
```

It prints the candidate def-witnesses, and for each one that reaches the target
the located `def → use` pair (with addresses), so you can jump straight to the
referencing code.

## How it works (internals)

1. Disassemble the region with Capstone into `(addr, mnemonic, operands)`.
2. Build a successor map (fall-through + branch/call edge) — the CFG.
3. Collect **def** instructions that materialise a constant near the target.
4. For each def, BFS forward over the CFG, preserving the base register until it
   is clobbered, and report a **use** whose `value + displacement == target`.
5. Drive the per-def search with `plausible`'s counterexample mechanism.

## Decompile — the plausible-driven pipeline

`flowref decompile <bin> <arch> <fnVaddr> <fileOff> <vaddr> <len>` lifts the
function in that region to pseudo-C. The pipeline:

1. **CFG (plain structural code).** Disassemble the region, mark block leaders
   (entry, branch targets, instructions after a transfer), carve basic blocks,
   and compute successor edges (fall-through + branch target). This step is not
   data-flow, so it is ordinary code.
2. **Reaching definitions / SSA-lite — *plausible-driven*.** For **every**
   `(use-instruction j, register r)` pair we pose
   `∀ candidate def i, ¬(i writes r ∧ a clobber-free CFG path i→…→j exists)`
   and let plausible search for the counterexample, which is the reaching def.
   Each def site gets a fresh SSA version (`r#0`, `r#1`, …); each use is wired to
   its reaching def's version. Where more than one def reaches a use, a **phi**
   `φ(r#a, r#b)` is recorded. This is the original xref trick applied globally.
3. **Expression reconstruction.** Each SSA value's right-hand side is rebuilt by
   substituting operand-uses with their reaching def's RHS, stopping at memory
   loads, calls, phis, and function arguments (e.g. `eax#1 = eax#0 + 1`).
4. **Control-flow structuring — *plausible-driven*.** Loops are found as
   back-edges via `∀ edge (b→h), ¬(h precedes b ∧ h reaches b)`; the
   counterexample is a back-edge → loop header. If/else is found by locating a
   conditional block whose successors re-merge — the merge point comes from
   reachability witnesses, **not** a dominator algorithm.
5. **Pseudo-C emission.** Walk the structured result and print readable
   pseudo-C: labelled blocks, `if (...) goto`, loop-header annotations,
   SSA-named assignments with reconstructed expressions, `call`s, and `return`.

The emitted pseudo-C is a faithful, readable structured rendering; it is **not**
meant to compile or to be type-correct.

### Example — synthetic self-test

`flowref --demo` hand-assembles a tiny x86 snippet (`i = 0; n = 10; while (i <
n) i++; if (n == 10) r = 1;`) and decompiles it:

```
// 11 insns, 7 basic blocks, 4 SSA defs, 0 phi(s)
// loop headers: [1]   (plausible found back-edge: true)
// if/else conditional blocks: [1, 4]

void sub_1000() {
  L0:
    eax#0 = 0;
    ebx#0 = 0xa;
  // loop header (while keeping cmp eax#0, ebx#0  /* jge */); back-edges close here
  L1:
    if (cmp eax#0, ebx#0  /* jge */) goto L4;
  L2:
    eax#1 = eax#0 + 1;
    goto L1;
  ...
  L4:
    if (cmp ebx#0, 0xa  /* jne */) goto L6;
  L5:
    ecx#0 = 1;
  L6:
    return;
}
```

The counting loop (`eax#1 = eax#0 + 1`, back-edge `L2→L1`) and the `if` on
`ebx == 0xa` are both recovered, with sensible SSA versions.

### Example — a real leaf function

Run on a small leaf in an x86 PE (file offset = vaddr − image base):

```
void sub_401010() {
  L0:
    push esi;
    esi#0 = ecx;
    mov dword ptr [esi], 0x513794;     // store a vtable/const through `this`
    call dword ptr [0x51330c];
    if (test byte ptr [esp + 8], 1  /* je */) goto L2;
  L1:
    push esi;
    call 0x4b44a6;                     // conditional cleanup
    esp#0 = esp + 4;
  L2:
    eax#0 = esi#0;                     // return this
    pop esi;
    return;
}
```

## Status & limitations

- Pattern coverage is intentionally small and conservative (clear, auditable
  rules over Capstone's textual operands rather than a full IR). It is meant as
  a lead-finder for reverse engineering, not a sound decompiler.
- It tracks **register-materialised** constants (`mov`/`lis`+`addi`/…). Values
  loaded *whole* from a table (e.g. a PowerPC TOC pointer) are not yet modelled;
  adding a table-load `defOf` is a natural extension.
- The CFG walk is bounded (depth cap) and ignores indirect branches.

### Decompiler limitations (honest scope)

This is an **MVP decompiler, not Ghidra or Hex-Rays.** It is genuinely useful
for small leaf and lightly-branched functions, and the structure it recovers
(blocks, loops, if/else, SSA assignments, reconstructed arithmetic) is faithful.
But:

- **Bounded plausible search.** Every data-flow query runs plausible with a
  finite instance budget and a candidate window of 4096 indices; the
  deterministic recovery that reads the witness back out is also depth-capped.
  Large or obfuscated functions can therefore be **slow or incomplete** — that
  is the deliberate, declared trade-off of the plausible-driven design, chosen
  over classical worklist/SSA/dominator algorithms by intent.
- **No nested structuring.** Loops and if/else are *detected and annotated*, and
  the body is emitted as labelled blocks with `goto`s, but the renderer does not
  fully nest `while {…}` / `if {…} else {…}` braces around recovered regions.
- **Register-level, textual operand model.** Sub-register aliasing
  (`al`/`ax`/`eax`), flags, memory SSA, and indirect/computed branches are not
  modelled; phis are detected but not minimised. Calling conventions and types
  are not inferred — the pseudo-C does not compile and is not type-correct.
- It reuses the conservative `defOf`/`useDisp`/`clobbers` patterns, so the same
  coverage caveats as the xref pass apply.

## License

`flowref` is MIT-licensed (see `LICENSE`). Disassembly is provided by
[`lean-capstone`](https://github.com/fire/lean-capstone), a separate dependency
that wraps Capstone (BSD-3-Clause, © the Capstone authors).
