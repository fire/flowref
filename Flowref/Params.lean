/-! # flowref — decode width (`Bits`)

The calling-convention **parameter model** that used to live here (SysV x86-64 /
cdecl x86-32 argument recovery) belongs to the decompiler and has moved to
[`fire/flowref-decompiler`](https://github.com/fire/flowref-decompiler). All that
remains in the disassembler is the decode-width tag the source adapters carry. -/

namespace Flowref

/-- Decode width of a region: 32- or 64-bit. Carried by the `SourceAdapter` port
alongside the architecture and instructions. -/
inductive Bits | b32 | b64 deriving DecidableEq, Repr, Inhabited

end Flowref
