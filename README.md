# flowref

**A control-flow-aware cross-reference finder and a plausible-driven decompiler
that emits *compilable* C — over machine-code disassembly, in Lean 4.**

A linear disassembler lists instructions but won't tell you *where a value is
defined versus used*: a value is frequently built in one basic block and
consumed in another, so a straight-line scan loses the connection. `flowref`
recovers it by walking the control-flow graph and tracking values through it.
The `decompile` subcommand goes further: it lifts a whole function into a
**complete C translation unit that `gcc -fsyntax-only -std=c11` accepts**.

The defining design choice is that **every data-flow layer is driven by
[`plausible`](https://github.com/leanprover-community/plausible)
(property-based counterexample search), not by a hand-written
fixpoint / worklist / dominator algorithm.** The core trick — pose
`∀ candidate witness, ¬(it is the fact we want)` and let plausible hand back a
*counterexample* that **is** the fact — is generalised from one cross-reference
target to every use, every back-edge, every reachability query. The searches
are then **iteratively deepened** into a witness DAG (below). This is a
deliberate trade-off (see *Limitations*).

## Commands

| Command | What it does |
|---|---|
| `flowref list <bin>` | List FUNC symbols (name, vaddr, size) and the auto-detected arch. |
| `flowref decompile <bin> <symbol\|0xVaddr>` | Lift a function to compilable C — region read from the ELF headers. |
| `flowref xref <bin> <symbol\|0xVaddr> <target>` | Def→use witnesses for `target` over a function's region. |
| `flowref demo` | List the built-in self-tests. |
| `flowref demo basic [--emit-c]` | Synthetic `if` + counting-loop self-test (no disk). |
| `flowref demo deep` | Demonstrate iterative-deepening escalation. |
| `flowref demo params [--emit-c]` | Calling-convention parameter recovery (SysV x86-64 2-param + cdecl x86-32 1-param). |
| `flowref --help` / `-h` | Full usage. |
| `flowref --version` | Version string. |

For ELF binaries the **arch, file offset, load address and length are read from
the section headers + symbol table** (a self-contained `<elf.h>` FFI shim — no
external library), so you give a symbol
name or a `0x` address instead of computing six hex fields by hand. Start with
`flowref list <bin>` to see what is there. `--arch=<a>` forces the arch if the
ELF machine is misidentified.

When the binary is **not an ELF** (raw blob, stripped region), use the explicit
form, supplying the region yourself:

| Command | What it does |
|---|---|
| `flowref decompile <bin> <arch> <fnVaddr> <fileOff> <vaddr> <len>` | Lift a function to compilable C. |
| `flowref xref <bin> <arch> <target> <fileOff> <vaddr> <len>` | Find def→use witnesses reaching `target`. |
| `flowref <bin> <arch> <target> <fileOff> <vaddr> <len>` | Legacy positional form of `xref`. |

Add `--search-trace` to any analysis command to print the iterative-deepening
escalation chain to stderr. Add `--json` to `list`/`decompile`/`xref` for a
single machine-readable object on stdout (rendered via `Lean.Json`); notes and
traces stay on stderr, so `flowref decompile a.out main --json` is pipe-clean.

Two more commands ingest an **objdump-style assembly listing** directly (no
binary), via the asm-text decoder — handy when only a listing is available:

| Command | What it does |
|---|---|
| `flowref decompile-asm <listing> <arch> <fnVaddr>` | Lift an Intel-syntax `.asm` listing to C. |
| `flowref xref-asm <listing> <arch> <target>` | Def→use witnesses over a listing. |

`arch` accepts **every target the vendored Capstone build supports** —
`x86`, `x64`/`x86-64`, `ppc`/`ppc64`, `arm`, `thumb`, `arm64`, `mips`/`mips64`,
`sparc`, `systemz`, `riscv`/`riscv64`, `m68k`, `sh`, `bpf`, `wasm`, and more
(see `capstoneSpec?` in `Flowref/Decoders.lean`). Decoding is universal; the
data-flow *pattern families* are currently x86 (all widths) and PowerPC, with
other targets decoding into a compilable stub until a family is added. The file
offset and load address are separate arguments because they differ in most
executable formats (sections map to addresses unrelated to their on-disk
position).

## Architecture — hexagonal ports & adapters

flowref is structured so the analysis never knows where its instructions came
from:

```
        adapters (I/O, formats)             decoders (Decoder port)        kernel (pure)
  binary-file · decompile-bench-bins ─────▶ capstone (bytes → Ins) ─┐
  elf-binary (elf.h shim: symbol/addr → region)─▶ capstone ─────────┤
  asm-text (string / file) ──────────────▶ objdump-asm (text → Ins)─┴─▶ Disasm · Dataflow · Emit
```

* **Kernel** — `Flowref/Disasm.lean` (instruction model + per-arch patterns +
  CFG carving), `Flowref/Dataflow.lean` (plausible-driven reaching defs +
  iterative deepening), `Flowref/Emit.lean` (compilable-C lowering). Pure domain
  logic: **no I/O, no Capstone dependency** — it speaks only the `Ins` model.
* **`Decoder` port** (`Flowref/Decoders.lean`) — the *format* boundary:
  `capstoneDecoder` (machine-code bytes) and `asmDecoder` (objdump text).
* **`SourceAdapter` port** (`Flowref/Adapters.lean`) — the *source* boundary and
  the **untrusted-input validation** layer: `binaryFileAdapter`,
  `elfBinaryAdapter` (symbol/address → region, via `Flowref/Elf.lean` over a
  self-contained `<elf.h>` shim — see `ffi/elf_shim.c`, no external library),
  `decompileBenchBinAdapter`,
  `asmStringAdapter`/`asmFileAdapter`.

Adding an architecture is one line in `capstoneSpec?`; adding an input format is
one new adapter — neither touches the kernel. See `Flowref/Ports.lean`.

## Proper C output

`decompile` (and `--demo --emit-c`) emit a self-contained C11 translation unit:

* `#include <stdint.h>` + typedefs, forward prototypes for every called
  `sub_*`, and a real `uint32_t sub_<addr>(…)` definition whose **parameter
  list is recovered from the calling convention** (see below).
* Every SSA value is declared up front as a width-typed local
  (`uint8_t`/`uint16_t`/`uint32_t`/`uint64_t`) with a C-legal name (`reg_version`).
* Memory operands become real C: `*(uint32_t*)((uintptr_t)(esi + 4))`.
* Calls become `sub_<tgt>();` (direct) or a function-pointer cast (indirect).
* SSA φ is lowered away — there is no `φ(...)` in the output; each version is a
  declared local and the value flows through plain assignments.
* Control flow is **labels + `goto`** (always valid C), with conditions built
  from the compare + branch (`if (cond_0) goto L4;`, where `cond_0` is a
  declared, documented boolean temp).

## Parameter recovery (calling conventions)

Without a calling convention a decompiler cannot know a function's *signature*,
so it falls back to `uint32_t sub_X(void)`. `flowref` recovers the
integer/pointer **parameters** from the platform ABI (chosen from the decode
arch/width) and emits a real prototype `uint32_t sub_X(uint32_t a0, uint32_t a1,
…)`, binds the incoming registers/stack-slots to those parameter names in the
SSA body, and — where a callee's arity is recoverable — passes the right number
of arguments at the call site.

* **x86-64 — System V AMD64.** Integer/pointer arguments arrive in
  `rdi, rsi, rdx, rcx, r8, r9` (then the stack, unmodelled). Parameter `k` is
  *used* when that argument register (any width alias: `rdi`/`edi`/`di`/`dil`, …)
  is **live on entry** — read before it is written. This is recovered with the
  *same* plausible-driven, iteratively-deepened reaching-def search the rest of
  the tool uses: an argument-register read with an **empty reaching-def set** is
  fed by the caller, i.e. it *is* a parameter. The count is the highest
  **consecutive** live arg register.

* **x86-32 — cdecl.** Integer arguments live on the stack: `[ebp + 8]`,
  `[ebp + 0xC]`, … after the standard `push ebp; mov ebp, esp` prologue (or
  `[esp + 4]`, `[esp + 8]`, … without a frame pointer). Parameter `k` is *used*
  when its slot is read (via the kernel's `useDisp` displacement reader). The
  count is the highest consecutive slot read.

```bash
$ flowref --demo-params
=== parameter-model demo: SysV x86-64 (2 params) ===
synthetic: mov eax, edi ; add eax, esi ; ret
recovered signature: uint32_t sub_401000(uint32_t a0, uint32_t a1)

=== parameter-model demo: cdecl x86-32 (1 param) ===
synthetic: push ebp; mov ebp,esp; mov eax,[ebp+8]; pop ebp; ret
recovered signature: uint32_t sub_401100(uint32_t a0)

$ flowref --demo-params --emit-c | gcc -xc -std=c11 -w -fsyntax-only -   # exits 0
```

**Honest limits.** Integer/pointer arguments only — no floating-point/SSE
arguments (xmm under SysV), no struct-by-value, no varargs. The parameter count
is a **heuristic**: the highest *consecutive* live-on-entry arg register (SysV)
or read stack slot (cdecl). A function that genuinely skips an argument
register, or only conditionally touches a later argument, can be under- or
mis-counted. Callee arity at a call site is known only for self-recursion;
other callees are declared `(void)`. This is a recovery aid, not a ground-truth
signature.

### Example — verified to compile

```bash
flowref --demo --emit-c | gcc -xc -std=c11 -w -fsyntax-only -   # exit status 0
```

produces, for the synthetic `i = 0; n = 10; while (i < n) i++; if (n == 10) r = 1;`:

```c
#include <stdint.h>
#include <stddef.h>

uint32_t sub_1000(void) {
  uint32_t eax_0 = 0;
  uint32_t ecx_0 = 0;
  uint32_t eax = 0;
  uint32_t eax_1 = 0;
  uint32_t ebx_0 = 0;
  int cond_0 = 0;
  int cond_1 = 0;

L0:;
  eax_0 = (uint32_t)(0);
  ebx_0 = (uint32_t)(0xa);
L1:;
  cond_0 = ((int32_t)(eax_0) >= (int32_t)(ebx_0));
  if (cond_0) goto L4;
L2:;
  eax_1 = (uint32_t)(eax_0 + 1);
  goto L1;
L3:;
L4:;
  cond_1 = ((int32_t)(ebx_0) != (int32_t)(0xa));
  if (cond_1) goto L6;
L5:;
  ecx_0 = (uint32_t)(1);
L6:;
  return eax;
}
```

The counting loop (`eax_1 = eax_0 + 1`, back-edge `L2 → L1`) and the `if` on
`ebx == 0xa` are both recovered, with SSA versions, and the result compiles.

## PPC64 ELFv1 TOC resolution (`r2`-relative addressing)

PowerPC64 ELFv1 code reaches module-level data and string constants **indirectly
through the TOC**: a dedicated register `r2` holds a per-module constant *TOC
base*, and a datum `A` is loaded either as `ld rX, off(r2)` (deref the pointer
cell at `r2+off`, in `.toc1`) or via `addis rX, r2, hi` + `addi`/`ld` (compute
`r2 + (hi<<16) + sext16(lo)`). A linear disassembler cannot follow this — the
referenced address lives in a `.toc1` cell, not in the instruction stream.

`flowref` recovers the module `r2` **authoritatively from `.opd`** (the function
descriptors record the TOC base; we read it, never hardcoding `.toc + 0x8000`),
then resolves both forms against the raw `.toc1` bytes (`Flowref/Toc.lean`):

* **`xref`** (ELF form) reports each `.text` site whose TOC load resolves to the
  searched target — alongside the immediate/`lis`-built (absolute-addressing)
  witnesses the data-flow walk already finds.
* **`decompile`** (ELF form) annotates every TOC-resolved load in the function
  (`@addr: ld rX, off(r2) → 0x…`), to stderr so the C on stdout stays pipe-clean.

```text
$ flowref xref module.elf 0x1000 0x10005000
TOC: recovered r2/TOC base = 0x4000 (from .opd)
TOC: 1 r2-relative reference(s) to 0x10005000:
  @0x1000: ld r3, 0(r2)  → 0x10005000
```

The packed 2×4-byte (`entry`,`toc`) descriptor layout some Cell/PS3 modules use
is recovered as well as the canonical 3-doubleword ELFv1 form: `recoverR2?`
accepts whichever `toc` field is constant and non-zero across the leading
descriptors. Modules compiled with absolute addressing (no live TOC) are
honestly reported as having no resolvable `r2`-relative site for the target.

## The plausible-driven design + iterative-deepening witness DAG

Every data-flow fact is a **counterexample** to a plausible property:

* **reaching definitions / SSA:** for each `(use j, register r)` we pose
  `∀ candidate def i, ¬(i writes r ∧ a clobber-free CFG path i→…→j exists)`;
  the counterexample is the reaching def, which is wired to the use's SSA
  version (φ where several defs reach).
* **loops:** `∀ edge (b→h), ¬(h reaches b ∧ the edge exists)`; the
  counterexample is a back-edge → a loop header.

A single fixed budget cannot serve both a 10-instruction leaf and a
1000-instruction function. So each query carries a **level** `L` — a CFG-walk
step budget, a plausible `Fin N` candidate window, and a plausible instance
count. We run `L0` (cheap, shallow). If a query is *unresolved* — no witness
**and** the budget was demonstrably hit (so we cannot conclude "provably none")
— we **escalate** it to `L1`, then `L2`, up to a hard cap. This is iterative
deepening. Resolved queries never re-run; only the unresolved frontier deepens.
The escalation forms a DAG: each node's resolved result feeds dependents, and
the deepening frontier is the set of still-unresolved nodes. The chain is
recorded and printed with `--search-trace`.

This is the project's "chain of conditional witnesses that deepen based on
evidence — a witness DAG" idea, made literal (see `Flowref/Dataflow.lean`).

### Demonstration

```text
$ flowref --demo-deep
=== iterative-deepening demo: 103 insns, esi def at idx 0, use at idx 101 ===
Per-level outcome for reaching-def query (esi @ the use):
  L0 (walkSteps=64, Fin 256): UNRESOLVED (budget hit — escalate)
  L1 (walkSteps=512, Fin 1024): RESOLVED (reaching def idx [0]) plausible-found=true
  L2 (walkSteps=4000, Fin 4096): RESOLVED (reaching def idx [0]) plausible-found=true

Adaptive driver resolved esi@use at level L1 with def(s) [0].
The shallow L0 search could NOT resolve it (budget hit); deepening did.
```

The def→use path crosses 100 instructions, so the shallow L0 walk hits its step
budget and reports *unresolved*; the deepened L1 walk crosses it and resolves
the query. A purely fixed-budget search would have silently missed it.

## Build

```bash
lake update                                                  # fetch deps (incl. lean-capstone)
.lake/packages/lean-capstone/thirdparty/capstone/build.sh    # build libcapstone.a once
lake build                                                   # builds the flowref executable
```

`lean-capstone` provides the typed Capstone wrapper; its `build.sh` produces the
static `libcapstone.a` that `flowref` links. The first build is slow because
Capstone is compiled from source.

## Test

```bash
./run-tests.sh
```

A single command that builds, runs the demos, pipes the emitted C through `gcc`
(both `-fsyntax-only` and `-c`), checks the iterative-deepening escalation, and
verifies error handling. It exits non-zero on any failure. CI runs the same
script (`.github/workflows/ci.yml`); the cold-cache CI run is slow because it
builds Capstone from source.

## Module layout

| File | Responsibility | Hexagon role |
|---|---|---|
| `Flowref/Disasm.lean` | Instruction model, per-arch patterns, CFG carving. | kernel |
| `Flowref/Dataflow.lean` | Plausible-driven reaching defs + iterative-deepening DAG. | kernel |
| `Flowref/Params.lean` | Calling-convention parameter model (SysV x86-64 + cdecl x86-32). | kernel |
| `Flowref/Emit.lean` | Compilable-C name/type/operand lowering. | kernel |
| `Flowref/Ports.lean` | `Decoder` + `SourceAdapter` port definitions. | ports |
| `Flowref/Decoders.lean` | Capstone byte decoder, objdump-asm text decoder, `capstoneSpec?` (all arches). | adapters |
| `Flowref/Adapters.lean` | Binary-file / decompile-bench / asm-text source adapters + input validation. | adapters |
| `Flowref/Toc.lean` | PPC64 ELFv1 TOC resolution: recover `r2` from `.opd`, resolve `ld off(r2)` / `addis r2,…` to absolute targets. | kernel |
| `Flowref.lean` | CLI, orchestration, C emission, demos. | composition root |
| `Etnf.lean` | `flowref-etnf`: normalise Decompile-Bench → ETNF Parquet (zstd) via DuckDB. | tool (dep `lean_duckdb`) |

## Evaluation — Decompile-Bench equivalence

flowref is evaluated against **Decompile-Bench** (Tan, Tian, Qi, et al., 2025),
a million-scale corpus of binary↔source function pairs. We drive it from the
**released binaries** (so flowref's own disassembler does the lifting) and prove
functional **equivalence** of the recovered C against the dataset's source
`code` by differential execution. A self-contained demonstration:

```text
$ decompile-bench/equiv-demo.sh
  k7 …: EQUIVALENT  (both return 7)
  …
RESULT: 4/4 proven functionally equivalent to their source.
```

This holds today for parameterless register-only leaf functions; the harness
honestly reports `INCOMPARABLE` (distinct from `NOT-EQUIVALENT`) for cases it
cannot yet model — see `decompile-bench/README.md` for the methodology and the
open gaps (chiefly: no parameter/ABI model).

## References

See `CITATIONS.bib`. Principally:

* Tan, H., Tian, X., Qi, H., et al. (2025). *Decompile-Bench: Million-Scale
  Binary-Source Function Pairs for Real-World Binary Decompilation.* arXiv:2505.12668.
  Dataset: <https://huggingface.co/datasets/LLM4Binary/decompile-bench>
  (binaries: `decompile-bench-bins`).

## Limitations (honest scope)

This is a **lead-finder and an MVP decompiler, not Ghidra or Hex-Rays.**

- **Compiles, not semantically perfect.** The emitted C is guaranteed to parse
  and type-check as C11; it is *not* guaranteed to reproduce the original
  behaviour. Calling conventions, types, and flags are not inferred. Control
  flow is rendered with `goto` rather than fully nested `while`/`if` braces.
- **Bounded, deepening plausible search.** Every data-flow query runs plausible
  with a finite instance budget and a bounded CFG walk, escalated by iterative
  deepening up to a hard cap. Very large or obfuscated functions can still be
  slow or hit the cap — that is the deliberate trade-off of the plausible-driven
  design, chosen over classical worklist/SSA/dominator algorithms by intent.
- **Register-level, textual operand model.** Sub-register aliasing
  (`al`/`ax`/`eax`, `eax`⊂`rax`), memory SSA, and indirect/computed branches are
  not modelled; φ nodes are detected and lowered but not minimised. There is no
  parameter / calling-convention model, so emitted functions are `(void)`.
- **Universal decode, two pattern families.** Every Capstone target decodes
  (`capstoneSpec?`), but the data-flow patterns
  (`defOf`/`useDisp`/`clobbers`/`writesReg`) are written for x86 (all widths)
  and PowerPC; other targets lift to a compilable stub until a family is added.
  Adding an arch is one line in `capstoneSpec?`; adding a *pattern family* is a
  kernel change isolated to `Flowref/Disasm.lean`.

## License

`flowref` is MIT-licensed (see `LICENSE`). Disassembly is provided by
[`lean-capstone`](https://github.com/fire/lean-capstone), which wraps Capstone
(BSD-3-Clause, © the Capstone authors).
