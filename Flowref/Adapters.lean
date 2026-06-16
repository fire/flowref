import Flowref.Decoders
import Flowref.Elf

/-! # flowref — data **adapters** (implementations of the `SourceAdapter` port)

An adapter fetches a raw source and runs a `Decoder` on it, yielding
`(arch, Ins[])` for the kernel. Each adapter validates its own request and
raises `IO.userError` on anything malformed — this is the **untrusted-input
boundary**, kept out of the pure kernel.

* `binaryFileAdapter`     — a file + (arch, fileOff, vaddr, len) region → Capstone.
* `decompileBenchBinAdapter` — the same, for a Decompile-Bench *bins* sample
  (`LLM4Binary/decompile-bench-bins`): a real ELF/PE, so it is decoded by
  Capstone over a supplied function region. A thin, named alias that documents
  intent for the evaluation corpus.
* `asmTextAdapter`        — an objdump-style listing (a string or file) → asm
  decoder. Lets flowref ingest the textual `asm` column of a Decompile-Bench
  row with no binary.
-/

namespace Flowref

/-- Strict, non-negative `Nat` parse of a CLI numeric field, or `IO.userError`. -/
private def field (name s : String) : IO Nat :=
  match parseImm? s with
  | some v =>
    if v < 0 then throw (IO.userError s!"{name} must be non-negative, got '{s}'")
    else pure v.toNat
  | none => throw (IO.userError s!"invalid {name} '{s}' (expected hex like 0x401000 or a decimal)")

/-- Resolve an arch string to `A`, or fail with a clear `IO.userError`. -/
private def archIO (archS : String) : IO A :=
  match archOfString? archS with
  | some a => pure a
  | none   => throw (IO.userError
      s!"unsupported arch '{archS}' (x86 | x64 | ppc | ppc64 | arm | thumb | arm64 | mips | mips64 | sparc | systemz | riscv | riscv64 | m68k | sh | bpf | wasm | … — see capstoneSpec?)")

/-- The decode **width** of a Capstone `Mode`: 64-bit iff the `b64` flag is set,
else 32-bit. (`b16` is treated as 32-bit for parameter-model purposes — there is
no 16-bit calling convention modelled.) Used to pick SysV vs cdecl. -/
def bitsOfMode (m : Capstone.Mode) : Bits :=
  if (m.bits &&& Capstone.Mode.b64.bits) != 0 then .b64 else .b32

/-- Decode width implied by an arch string (via `capstoneSpec?`), defaulting to
32-bit for arch names without a Capstone spec. -/
def bitsOfArchString (s : String) : Bits :=
  match capstoneSpec? s with
  | some (_, m, _) => bitsOfMode m
  | none           => .b32

/-- **Binary-file source adapter.** Validate the request, read the region, decode
with Capstone. Every field is checked before any work: arch supported, numeric
fields parse strictly and are non-negative, and `[fileOff, fileOff+len)` lies
within the actual file — a bad field raises `IO.userError` rather than silently
decoding the wrong bytes. -/
def binaryFileAdapter (bin archS foS vaS lenS : String) : SourceAdapter where
  name := "binary-file"
  run := do
    let (carch, cmode, fam) ← match capstoneSpec? archS with
      | some s => pure s
      | none   => throw (IO.userError
          s!"unsupported arch '{archS}' (x86 | x64 | ppc | ppc64 | arm | thumb | arm64 | mips | mips64 | sparc | systemz | riscv | riscv64 | m68k | sh | bpf | wasm | … — see capstoneSpec?)")
    let fo  ← field "fileOff" foS
    let va  ← field "vaddr"   vaS
    let len ← field "len"     lenS
    if len == 0 then throw (IO.userError "region length is zero")
    let d ← IO.FS.readBinFile (bin : System.FilePath)
    if fo ≥ d.size then
      throw (IO.userError s!"file offset 0x{hex fo} is at/past end of file (size 0x{hex d.size})")
    if fo + len > d.size then
      throw (IO.userError
        s!"region [0x{hex fo}, 0x{hex (fo+len)}) extends past end of file (size 0x{hex d.size})")
    pure (fam, bitsOfMode cmode, capstoneDecodeBytes carch cmode (d.extract fo (fo + len)) va)

/-- **Decompile-Bench bins adapter.** A sample from `decompile-bench-bins` is a
real ELF/PE; decode a supplied function region with Capstone, exactly like
`binaryFileAdapter`. Named separately so evaluation code reads by intent. -/
def decompileBenchBinAdapter (bin archS foS vaS lenS : String) : SourceAdapter :=
  { binaryFileAdapter bin archS foS vaS lenS with name := "decompile-bench-bins" }

/-- **Assembly-text adapter (from a string).** Decode an objdump-style listing
already in memory (e.g. a dataset row's `asm` column). -/
def asmStringAdapter (archS listing : String) : SourceAdapter where
  name := "asm-text"
  run := do
    let a ← archIO archS
    let insns := asmDecoder.decode a listing
    if insns.isEmpty then
      throw (IO.userError "assembly listing decoded to zero instructions (unrecognised format?)")
    pure (a, bitsOfArchString archS, insns)

/-- **Assembly-text adapter (from a file).** Read an objdump-style listing file
and decode it. -/
def asmFileAdapter (archS path : String) : SourceAdapter where
  name := "asm-text-file"
  run := do
    let a ← archIO archS
    let listing ← IO.FS.readFile (path : System.FilePath)
    let insns := asmDecoder.decode a listing
    if insns.isEmpty then
      throw (IO.userError s!"assembly listing '{path}' decoded to zero instructions (unrecognised format?)")
    pure (a, bitsOfArchString archS, insns)

/-- **ELF symbol/address resolution.** Read `bin` as an ELF, resolve `target`
(a FUNC symbol name or a `0x` vaddr) to a `(arch, fileOff, vaddr, len)` region
via the section map + symbol table, so the caller need not supply any of them.
`archOverride?` forces the arch token (for the rare misidentified machine).
Raises `IO.userError` when `bin` is not a readable ELF or `target` cannot be
resolved — the untrusted-input boundary, same as the other adapters. -/
def elfResolveRegion (bin target : String) (archOverride? : Option String) : IO ElfRegion := do
  match ← readElf bin with
  | none =>
    throw (IO.userError (← notElfMessage bin))
  | some info =>
    match info.resolve target with
    | .error msg => throw (IO.userError msg)
    | .ok region => pure { region with arch := archOverride?.getD region.arch }

/-- **ELF-backed source adapter.** Resolve `target` within `bin` via the ELF
headers, then decode that region with Capstone — the two-argument convenience
path (`decompile <bin> <sym|addr>`). The resolved region is also returned by
`elfResolveRegion` for callers that need the function vaddr (e.g. decompile). -/
def elfBinaryAdapter (region : ElfRegion) (bin : String) : SourceAdapter :=
  { binaryFileAdapter bin region.arch
      s!"0x{hex region.fileOff}" s!"0x{hex region.vaddr}" s!"0x{hex region.len}"
    with name := "elf-binary" }

/-- Back-compatible thin wrapper over `binaryFileAdapter` — the historical
`load` entry point, now expressed through the port. -/
def load (bin archS foS vaS lenS : String) : IO (A × Bits × Array Ins) :=
  (binaryFileAdapter bin archS foS vaS lenS).run

end Flowref
