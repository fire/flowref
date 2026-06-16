import Flowref.Disasm

/-! # flowref — ELF parser (FFI over elfutils libelf/gelf)

A thin typed wrapper over `ffi/elf_shim.c`, which uses the system `libelf`
(elfutils) to parse an ELF container — reusing a battle-tested parser instead of
hand-rolling byte-poking in Lean, and mirroring the `lean-capstone` FFI pattern
(one C primitive, TSV transport, typed wrapper here).

The shim returns a TAB-delimited, newline-separated dump:

```
H <machine> <is64> <le> <entryHex>
S <name> <addrHex> <offsetHex> <sizeHex>     (one per section)
F <name> <valueHex> <sizeHex>                 (one per FUNC symbol)
```

This module parses that into `ElfInfo` and provides:

* `archTokenOfMachine` — `e_machine` (+ class/endian) → a flowref arch token
  (`x86`/`x64`/`ppc`/…), so `arch` no longer has to be supplied by hand.
* `ElfInfo.resolve` — a symbol **name** or a **vaddr** → the
  `(arch, fileOff, vaddr, len)` region the binary adapter needs. This is what
  collapses the 6-positional-arg interface to two.

The shim returns `""` on anything that is not a readable ELF; the wrapper maps
that to `none`, so callers can fall back to the explicit-region path. -/

namespace Flowref

/-- FFI: open `path` with libelf and return the TSV dump (`""` on any error —
not an ELF, unreadable, malformed). Pure in the same benign sense as
`Capstone.disasmRaw`: the file is treated as fixed for the run. -/
@[extern "lean_elf_dump"]
opaque elfDumpRaw (path : String) : String

/-- A FUNC symbol: a name, its virtual address, and its size (`0` if the symbol
table did not record one). -/
structure ElfFunc where
  name  : String
  vaddr : Nat
  size  : Nat
  deriving Repr, Inhabited, DecidableEq

/-- A section's address/offset/size — the `vaddr → fileOff` mapping. -/
structure ElfSection where
  name   : String
  addr   : Nat
  offset : Nat
  size   : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Everything the resolver needs from an ELF: header facts, the section map,
and the FUNC symbols. -/
structure ElfInfo where
  machine      : Nat
  is64         : Bool
  littleEndian : Bool
  entry        : Nat
  sections     : Array ElfSection
  funcs        : Array ElfFunc
  deriving Repr, Inhabited

/-- Parse a bare (no `0x`) hex string to `Nat`; `0` on any stray char. -/
private def hexNat (s : String) : Nat :=
  s.trimAscii.toString.toList.foldl (fun n c =>
    let d :=
      if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else 0
    n * 16 + d) 0

/-- Map an ELF `e_machine` (+ class/endian) to a flowref arch token accepted by
`capstoneSpec?`. `""` for machines flowref has no token for (the caller then
asks the user to pass `--arch`). -/
def archTokenOfMachine (machine : Nat) (is64 littleEndian : Bool) : String :=
  match machine with
  | 3   => "x86"                                   -- EM_386
  | 62  => "x64"                                   -- EM_X86_64
  | 20  => "ppc"                                   -- EM_PPC
  | 21  => if littleEndian then "ppc64le" else "ppc64"  -- EM_PPC64
  | 40  => "arm"                                   -- EM_ARM
  | 183 => "arm64"                                 -- EM_AARCH64
  | 8   => if is64 then "mips64" else if littleEndian then "mips" else "mips32be"  -- EM_MIPS
  | 243 => if is64 then "riscv64" else "riscv"     -- EM_RISCV
  | 22  => "systemz"                               -- EM_S390
  | 2   => "sparc"                                 -- EM_SPARC
  | 18  => "sparc"                                 -- EM_SPARC32PLUS
  | 43  => "sparc64"                               -- EM_SPARCV9
  | 4   => "m68k"                                  -- EM_68K
  | _   => ""

/-- The flowref arch token for this ELF (`""` if unmapped). -/
def ElfInfo.arch (e : ElfInfo) : String :=
  archTokenOfMachine e.machine e.is64 e.littleEndian

/-- Parse the shim's TSV dump into `ElfInfo`, or `none` if it is empty / has no
header record (i.e. not a readable ELF). -/
def parseElfDump (dump : String) : Option ElfInfo := Id.run do
  if dump.trimAscii.isEmpty then return none
  let mut machine := 0
  let mut is64 := false
  let mut le := true
  let mut entry := 0
  let mut sawH := false
  let mut secs : Array ElfSection := #[]
  let mut fns : Array ElfFunc := #[]
  for line in dump.splitOn "\n" do
    let f := (line.splitOn "\t").toArray
    match f[0]? with
    | some "H" =>
      sawH := true
      machine := (f[1]?.getD "0").toNat!
      is64    := (f[2]?.getD "0") == "1"
      le      := (f[3]?.getD "1") == "1"
      entry   := hexNat (f[4]?.getD "0")
    | some "S" =>
      secs := secs.push
        { name := f[1]?.getD "", addr := hexNat (f[2]?.getD "0"),
          offset := hexNat (f[3]?.getD "0"), size := hexNat (f[4]?.getD "0") }
    | some "F" =>
      fns := fns.push
        { name := f[1]?.getD "", vaddr := hexNat (f[2]?.getD "0"),
          size := hexNat (f[3]?.getD "0") }
    | _ => pure ()
  if ¬ sawH then return none
  return some { machine, is64, littleEndian := le, entry, sections := secs, funcs := fns }

/-- Read + parse an ELF file. `none` if not a readable ELF. -/
def readElf (path : String) : IO (Option ElfInfo) :=
  pure (parseElfDump (elfDumpRaw path))

/-- The section whose `[addr, addr+size)` (allocated, non-zero addr) contains
`vaddr` — i.e. how a load address maps back to a file offset. -/
def ElfInfo.sectionAt (e : ElfInfo) (vaddr : Nat) : Option ElfSection :=
  e.sections.find? (fun s => s.addr != 0 ∧ s.size != 0 ∧ s.addr ≤ vaddr ∧ vaddr < s.addr + s.size)

/-- Deduplicated FUNC symbols (symtab + dynsym can overlap), preferring the
entry that recorded a non-zero size. Sorted by vaddr for stable `list` output.
Symbol counts are small, so a linear dedup keeps this dependency-free. -/
def ElfInfo.functions (e : ElfInfo) : Array ElfFunc := Id.run do
  let mut acc : Array ElfFunc := #[]
  for fn in e.funcs do
    match acc.findIdx? (·.vaddr == fn.vaddr) with
    | some i =>
      if (acc[i]!).size == 0 ∧ fn.size != 0 then acc := acc.set! i fn
    | none => acc := acc.push fn
  pure (acc.qsort (fun a b => a.vaddr < b.vaddr))

/-- A resolved region for the binary adapter. -/
structure ElfRegion where
  arch     : String
  fileOff  : Nat
  vaddr    : Nat
  len      : Nat
  /-- The matched symbol name, if resolution was by name or hit a known symbol. -/
  symbol   : Option String
  deriving Repr, Inhabited

/-- Resolve a `target` — a symbol **name** or a **vaddr** (`0x…`/decimal/bare
hex via `parseImm?`, falling back to bare hex) — to the region to disassemble.

* Name → its `(vaddr, size)`; offset from the containing section.
* Address → the FUNC symbol at that exact vaddr (for its size) if any, else the
  containing section, with `len` running to the section end.

`Except String` carries a user-facing message on failure (unknown symbol /
address outside any section / no length determinable). The arch token comes from
the ELF header, so the caller never has to pass `--arch`. -/
def ElfInfo.resolve (e : ElfInfo) (target : String) : Except String ElfRegion :=
  let arch := e.arch
  if arch.isEmpty then
    .error s!"unsupported ELF machine {e.machine}; pass an explicit region + arch"
  else
    -- Try a symbol name first (only if it isn't a plain number).
    let asNum := (parseImm? target).filter (· ≥ 0) |>.map Int.toNat
    match e.functions.find? (fun fn => fn.name == target) with
    | some fn => regionFor arch fn.vaddr (if fn.size > 0 then some fn.size else none) (some fn.name)
    | none =>
      match asNum with
      | some va =>
        let symAt := e.functions.find? (fun fn => fn.vaddr == va)
        regionFor arch va (symAt.bind (fun s => if s.size > 0 then some s.size else none))
          (symAt.map (·.name))
      | none =>
        .error s!"no FUNC symbol named '{target}' (try `flowref list <bin>`, or pass a 0x address)"
where
  /-- Build the region for a vaddr, deriving file offset from the section map and
  a length from the symbol size (or section end). -/
  regionFor (arch : String) (va : Nat) (size? : Option Nat) (sym : Option String) :
      Except String ElfRegion :=
    match e.sectionAt va with
    | none => .error s!"address 0x{hex va} is not inside any allocated section"
    | some sec =>
      let fileOff := sec.offset + (va - sec.addr)
      let len := match size? with
        | some n => n
        | none   => (sec.addr + sec.size) - va     -- to end of section
      if len == 0 then
        .error s!"could not determine a length for 0x{hex va} (zero-size symbol at section end)"
      else
        .ok { arch, fileOff, vaddr := va, len, symbol := sym }

end Flowref
