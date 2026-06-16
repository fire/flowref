# flowref

**A control-flow-aware cross-reference finder over machine-code disassembly, in
Lean 4.** Point it at a binary and ask *where a value is used*: flowref
disassembles (via [Capstone](https://github.com/fire/lean-capstone)) and walks
the control-flow graph to recover def→use links a linear scan can't see.

```bash
flowref list a.out                       # functions + auto-detected arch
flowref xref a.out main 0x401136         # def→use witnesses reaching 0x401136 in main
```

The defining design choice: **every data-flow fact is a `plausible`
counterexample, not a hand-written fixpoint.** A query is posed as
`∀ candidate witness, ¬(it is the fact we want)`; plausible hands back the
counterexample, which *is* the fact (a reaching def, a back-edge, a reachable
use). The searches are **iteratively deepened** — cheap shallow level first,
escalate only the unresolved frontier — forming a **witness DAG**
(`Flowref/Dataflow.lean`).

> Lifting a function to compilable C is a separate tool:
> **[github.com/fire/flowref-decompiler](https://github.com/fire/flowref-decompiler)**,
> built on this disassembler.

## Commands

| Command | What it does |
|---|---|
| `flowref list <bin>` | List FUNC symbols (name, vaddr, size) and the auto-detected arch. |
| `flowref xref <bin> <symbol\|0xVaddr> <target>` | Def→use witnesses for `target` over a function's region. |
| `flowref xref <bin> <arch> <target> <fileOff> <vaddr> <len>` | Explicit-region form (raw blobs / stripped). |
| `flowref xref-asm <listing> <arch> <target>` | Same, over an objdump-style Intel `.asm` listing. |
| `flowref demo deep` | Iterative-deepening witness-DAG escalation (def→use across 100 nops). |
| `flowref --help` / `--version` | Usage / version. |

For ELF binaries the arch, file offset, address and length are read from the
headers (a self-contained `<elf.h>` FFI shim — no external library), so you give
a symbol or `0x` address. Add `--json` for machine-readable output,
`--search-trace` to watch the deepening.

## How it works

- **Plausible-driven witness DAG.** Reaching-defs, back-edges and reachability
  are all recovered as plausible counterexamples, deepened on demand
  (`Flowref/Dataflow.lean`). `flowref demo deep` shows a def→use that the shallow
  level can't resolve and a deeper level can.
- **Hexagonal.** A pure kernel (`Disasm`/`Dataflow`) speaks only an instruction
  model; **adapters** feed it from an ELF region, raw bytes, or an asm listing,
  and **decoders** (Capstone / objdump-text) do the format step. Decoding covers
  every Capstone target; the data-flow pattern families are x86 (all widths) and
  PowerPC, including PPC64 ELFv1 TOC (`r2`-relative) reference resolution.

## Build & test

```bash
lake update
.lake/packages/lean-capstone/thirdparty/capstone/build.sh   # build libcapstone.a once (slow)
lake build
./run-tests.sh
```

## License

MIT (see `LICENSE`). Disassembly via
[`lean-capstone`](https://github.com/fire/lean-capstone) (Capstone, BSD-3).
