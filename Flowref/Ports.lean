import Flowref.Disasm
import Flowref.Params

/-! # flowref — hexagonal ports (the boundary of the analysis kernel)

flowref is structured as **ports & adapters** (hexagonal architecture):

```
            ┌──────────── adapters (I/O, formats) ────────────┐
            │  binary-file   decompile-bench-bins   asm-text   │
            └───────┬───────────────┬──────────────────┬───────┘
                    │  Decoder port │                  │
            ┌───────▼───────────────▼──────────────────▼───────┐
            │            KERNEL (pure domain, no I/O)           │
            │   Disasm: Ins model + CFG   ·   Dataflow   ·  Emit │
            └───────────────────────────────────────────────────┘
```

* **Kernel** (the hexagon's interior): `Flowref/Disasm.lean` (instruction model
  + per-arch patterns + CFG carving), `Flowref/Dataflow.lean` (plausible-driven
  reaching defs + iterative deepening), `Flowref/Emit.lean` (compilable-C
  lowering). The kernel speaks only the `Ins` model — it has no idea where the
  instructions came from.

* **`Decoder` port** (inbound): turn a *raw source* (`σ`) — machine-code bytes or
  an assembly listing — into the kernel's `Ins` array. A decoder is the *format*
  boundary; it is the only place that knows byte/text layout. Implementations:
  `capstoneDecoder` (bytes), `asmDecoder` (objdump text) in `Decoders.lean`.

* **`SourceAdapter` port** (inbound): yield `(arch, Ins[])` from some external
  source — a binary-file region, a Decompile-Bench binary, an `.asm` listing —
  validating its own inputs and delegating the format step to a `Decoder`.
  Implementations live in `Adapters.lean`.

This separation is why the same dataflow + C-emission kernel can be driven by a
raw PE/ELF file *and* by a Decompile-Bench row without the kernel changing.
-/

namespace Flowref

/-- Inbound **decoder port**, generic over the raw source representation `σ`
(e.g. `ByteArray × vaddr` for machine code, `String` for a listing). A decoder
fixes the *format*; it is pure (`σ → Ins[]`), so it is part of no I/O. -/
structure Decoder (σ : Type) where
  /-- Human label, e.g. `"capstone"`, `"objdump-asm"`. -/
  name   : String
  /-- Decode a raw source for architecture `a` into the kernel's `Ins` array. -/
  decode : A → σ → Array Ins

/-- Inbound **source-adapter port**: produce decoded instructions for the
kernel, hiding *where* the bytes/text came from and validating the request.
A malformed request raises `IO.userError` (the CLI maps it to a non-zero exit)
rather than silently analysing the wrong region. -/
structure SourceAdapter where
  /-- Human label, e.g. `"binary-file"`, `"asm-text"`. -/
  name : String
  /-- Run the adapter: fetch + decode, or fail with a clear `IO.userError`.
  Yields the kernel arch family, the decode **width** (`Bits`, needed by the
  calling-convention parameter model to pick SysV vs cdecl), and the decoded
  instructions. -/
  run  : IO (A × Bits × Array Ins)

end Flowref
