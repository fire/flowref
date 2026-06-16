import Flowref.Disasm
import Flowref.Elf
import Std.Data.HashMap

/-! # flowref — PPC64 ELFv1 TOC (table-of-contents) resolution

PowerPC64 ELFv1 code reaches most module-level data and string constants
**indirectly through the TOC**: the dedicated register `r2` holds a per-module
constant *TOC base*, and a datum `A` is read either as

* `ld rX, off(r2)` — load the 8-byte big-endian pointer stored at `r2+off`
  (that pointer cell lives in `.toc1`); the *stored* value is the referenced
  address `A` (commonly a `.rodata` string).  **The common case.**
* `addis rX, r2, hi` then `addi rX, rX, lo` (or `ld rX, lo(rX)`) — compute the
  address `r2 + ((hi<<16) + sign_extend16(lo))`, and for an `@toc` data pointer
  then dereference it.

A *stripped* ELFv1 binary still carries the authoritative `r2` value in the
**`.opd`** section: each function descriptor records `(entry, toc_base, env)`,
and `toc_base` is exactly the `r2` the module runs with. We recover `r2` from
`.opd` (never hardcoding `.toc + 0x8000`), then resolve the forms above against
the raw `.toc1` / data bytes — all pure, over a `Bytes` view of the file plus
the `ElfInfo` section map.

This module is decoder-agnostic in the same spirit as the rest of the kernel:
it consumes the `Ins` model (textual `disp(rN)` operands, as Capstone prints
PowerPC loads) and a byte/section view; it does no I/O itself. -/

namespace Flowref

/-- A read-only view of the whole file plus the parsed `ElfInfo`, enough to map
a *vaddr* to its on-disk bytes and big-endian-decode pointer cells. -/
structure ElfBytes where
  info  : ElfInfo
  bytes : ByteArray
  deriving Inhabited

/-- Big-endian read of `n` bytes (≤ 8) at file offset `fo`, as a `Nat`. Bytes
past the end read as zero (callers bound-check via the section map first). -/
def beReadAt (b : ByteArray) (fo n : Nat) : Nat := Id.run do
  let mut v : Nat := 0
  for i in [0:n] do
    v := v * 256 + ((b[fo + i]?).getD 0).toNat
  pure v

/-- The file offset of a *vaddr*, via the section map (`none` if `vaddr` is in
no allocated section, or the section has no file backing). -/
def ElfBytes.fileOffOf? (e : ElfBytes) (vaddr : Nat) : Option Nat :=
  match e.info.sectionAt vaddr with
  | some sec => some (sec.offset + (vaddr - sec.addr))
  | none => none

/-- Read an 8-byte **big-endian** pointer stored at virtual address `vaddr`
(e.g. a `.toc1` cell), or `none` if `vaddr` maps to no section. ELFv1 PPC64 is
always big-endian; the byte order is fixed here, not read from the header. -/
def ElfBytes.readPtr64? (e : ElfBytes) (vaddr : Nat) : Option Nat :=
  (e.fileOffOf? vaddr).map (fun fo => beReadAt e.bytes fo 8)

/-- Read a 4-byte **big-endian** word at `vaddr` (the 32-bit pointer cells some
PS3/Cell ELFv1 modules use in `.toc1` / descriptor tables), or `none`. -/
def ElfBytes.readWord32? (e : ElfBytes) (vaddr : Nat) : Option Nat :=
  (e.fileOffOf? vaddr).map (fun fo => beReadAt e.bytes fo 4)

/-! ## Recovering the module TOC base (`r2`) from `.opd`

An ELFv1 function descriptor is canonically three doublewords
`(entry_addr, toc_base, env)`; `toc_base` is the `r2` value, **constant across
the module**. Some Cell/PS3 modules instead pack descriptors as two 32-bit
words `(entry, toc)`. We read `.opd` and pick the field that is (a) constant
across the first several descriptors and (b) plausibly a data address — that is
the TOC base, regardless of which descriptor layout the module used. -/

/-- The `toc` fields of the first up-to-`cap` descriptors under a given layout:
`stride` bytes per descriptor, the `toc` field `tocOff` bytes in, read as
`width` big-endian bytes. -/
private def opdTocSeq (e : ElfBytes) (opdOff opdSize stride tocOff width cap : Nat)
    : List Nat :=
  let n := min cap (opdSize / stride)
  (List.range n).map (fun i => beReadAt e.bytes (opdOff + i * stride + tocOff) width)

/-- A `toc` sequence is a valid TOC base iff it is **non-empty, non-zero, and
constant** across the descriptors (the module TOC is the same for every
function). -/
private def constNonzero (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: rest => if x != 0 ∧ rest.all (· == x) then some x else none

/-- Recover the module TOC base (the `r2` value) from `.opd`, authoritatively —
*not* hardcoded as `.toc + 0x8000`. Tries the canonical ELFv1 3-doubleword
layout (`toc` = 2nd doubleword, 24-byte stride) first, then the packed 2×4-byte
Cell/PS3 layout (`toc` = 2nd word, 8-byte stride), accepting whichever yields a
**constant, non-zero** `toc` across the leading descriptors. `none` if there is
no `.opd`, or no layout produces a constant field. -/
def ElfBytes.recoverR2? (e : ElfBytes) : Option Nat := do
  let opd ← e.info.sections.find? (·.name == ".opd")
  if opd.size == 0 then none else
  -- 3-doubleword ELFv1: entry@+0, toc@+8, env@+16 (24-byte stride, 8-byte toc).
  (constNonzero (opdTocSeq e opd.offset opd.size 24 8 8 4)) <|>
  -- 2-word packed: entry@+0, toc@+4 (8-byte stride, 4-byte toc).
  (constNonzero (opdTocSeq e opd.offset opd.size 8 4 4 4))

/-! ## Resolving a TOC-relative load to its absolute target

Given the recovered `r2`, resolve the two addressing forms to the absolute
address they reference:

* `ld rX, off(r2)` → dereference the pointer cell at `r2+off` (`.toc1`): the
  stored value **is** the target `A`.
* `addis rX, r2, hi` … → the *computed* base `r2 + (hi<<16) + sext16(lo)`. For an
  `@toc` data pointer this base lands in `.toc1` and is then dereferenced. -/

/-- Sign-extend a 16-bit immediate (`disp`/`lo`) to an `Int`. -/
def sext16 (n : Int) : Int :=
  let m := n % 0x10000
  let m := if m < 0 then m + 0x10000 else m
  if m ≥ 0x8000 then m - 0x10000 else m

-- The register-tracking map is a plain `Std.HashMap String Int` (register name
-- → the TOC-derived address that register currently holds, e.g. the result of
-- `addis rX, r2, hi`), threaded through `resolveTocSite`/`scanTocXref`.

/-- Effective address of a `disp(rA)` memory operand given the known value of
`rA`. Returns `none` when the instruction is not a `disp(rA)` load with this
base, or the base value is unknown. The displacement is sign-extended. -/
def effAddrOf? (i : Ins) (baseReg : String) (baseVal : Int) : Option Int :=
  match useDisp .ppc i baseReg with
  | some disp => some (baseVal + sext16 disp)
  | none => none

/-- The *absolute target* a single PPC instruction resolves to through the TOC,
given `r2` and the currently-known TOC-derived register values:

* `ld rX, off(r2)` → `readPtr64?` (or 32-bit) of `r2+off`: the dereferenced
  pointer — the referenced datum.
* `ld rX, lo(rY)` where `rY` is a known `addis r2`-base → `readPtr*?` of that EA.
* `addi rX, rY, lo` / `addis` chaining yields a computed address (no deref);
  reported as the address itself (an `@toc`/`@l` pointer to data).

Returns `(resolvedTarget?, updatedTocRegs)`: the resolved absolute address if
this site references one, plus the register-tracking state threaded forward. -/
def resolveTocSite (eb : ElfBytes) (r2 : Int) (regs : Std.HashMap String Int) (i : Ins)
    : Option Int × Std.HashMap String Int :=
  let toks := (i.ops.splitOn ",").map (·.trimAscii.toString)
  -- addis rD, r2, hi  → rD = r2 + (hi<<16); a TOC-base, tracked for a later ld/addi.
  if i.mn == "addis" then
    match toks with
    | [d, b, hi] =>
      if b == "r2" then (none, regs.insert d (r2 + (parseImm hi) * 0x10000))
      else match regs[b]? with
        | some bv => (none, regs.insert d (bv + (parseImm hi) * 0x10000))
        | none    => (none, regs.erase d)
    | _ => (none, regs)
  -- addi rD, rY, lo  → rD = rY + sext16(lo); for a tracked TOC base this *is* the
  -- referenced address (an @toc/@l data pointer), no deref.
  else if i.mn == "addi" ∨ i.mn == "addic" then
    match toks with
    | [d, b, lo] =>
      match regs[b]? with
      | some bv =>
        let addr := bv + sext16 (parseImm lo)
        (some addr, regs.insert d addr)
      | none => (none, regs.erase d)
    | _ => (none, regs)
  -- ld rD, disp(rA): if rA is r2 or a tracked TOC base, the EA is a .toc1 cell;
  -- dereference it (8-byte BE, falling back to 4-byte) → the referenced datum.
  else if i.mn == "ld" ∨ i.mn.startsWith "lwz" ∨ i.mn.startsWith "lwa" then
    let dst := (toks.headD "").trimAscii.toString
    -- the base register inside disp(rA)
    let baseReg :=
      match i.ops.splitOn "(" with
      | _ :: rest :: _ => (rest.splitOn ")").headD "" |>.trimAscii.toString
      | _ => ""
    let baseVal? : Option Int :=
      if baseReg == "r2" then some r2 else regs[baseReg]?
    match baseVal? with
    | some bv =>
      match effAddrOf? i baseReg bv with
      | some ea =>
        -- Dereference the pointer cell at `ea` (`.toc1`). `ld` reads an 8-byte
        -- doubleword; `lwz`/`lwa` a 4-byte word. For `ld`, if the 8-byte read is
        -- implausibly large (two packed 32-bit cells, as some Cell/PS3 modules
        -- store) fall back to the 4-byte cell.
        let ptr? :=
          if i.mn.startsWith "lwz" ∨ i.mn.startsWith "lwa" then eb.readWord32? ea.toNat
          else match eb.readPtr64? ea.toNat with
            | some p => if p != 0 ∧ p < 0x1_0000_0000_0000 then some p else eb.readWord32? ea.toNat
            | none   => eb.readWord32? ea.toNat
        match ptr? with
        | some p => (some (Int.ofNat p), regs.erase dst)
        | none   => (none, regs.erase dst)
      | none => (none, regs.erase dst)
    | none => (none, regs.erase dst)
  else
    -- any other write to a register invalidates a tracked TOC value.
    match writesReg .ppc i with
    | some d => (none, regs.erase d)
    | none   => (none, regs)

/-- A resolved TOC reference witness: the `.text` site, the instruction text,
and the absolute address it resolves to through the TOC. -/
structure TocWitness where
  vaddr   : Nat
  insn    : String
  resolved : Nat
  deriving Repr, Inhabited

/-- Scan a region's instructions, threading the TOC-derived register state, and
collect every site whose TOC-resolved address equals `target`. This is the xref
half: report each `.text` instruction that — through `r2` and the `.toc1` cells
— references `target`. -/
def scanTocXref (eb : ElfBytes) (r2 : Int) (target : Int) (insns : Array Ins)
    : Array TocWitness := Id.run do
  let mut regs : Std.HashMap String Int := {}
  let mut out : Array TocWitness := #[]
  for i in insns do
    let (res?, regs') := resolveTocSite eb r2 regs i
    regs := regs'
    match res? with
    | some a => if a == target then
        out := out.push { vaddr := i.addr, insn := s!"{i.mn} {i.ops}", resolved := a.toNat }
    | none => pure ()
  pure out

/-- Scan a region and collect **every** TOC-resolved site (regardless of
target) — the `decompile` annotation half: each `ld off(r2)` / `addis r2,…`
load that resolves to a concrete absolute address through the recovered `r2`. -/
def scanTocSites (eb : ElfBytes) (r2 : Int) (insns : Array Ins) : Array TocWitness :=
  Id.run do
    let mut regs : Std.HashMap String Int := {}
    let mut out : Array TocWitness := #[]
    for i in insns do
      let (res?, regs') := resolveTocSite eb r2 regs i
      regs := regs'
      match res? with
      | some a => out := out.push { vaddr := i.addr, insn := s!"{i.mn} {i.ops}", resolved := a.toNat }
      | none => pure ()
    pure out

/-- Read an ELF file fully (bytes + parsed info), or `none` if it is not a
readable ELF — the I/O entry point for the TOC machinery. -/
def readElfBytes (path : String) : IO (Option ElfBytes) := do
  match ← readElf path with
  | none => pure none
  | some info =>
    let bytes ← try IO.FS.readBinFile (path : System.FilePath) catch _ => pure ByteArray.empty
    pure (some { info, bytes })

end Flowref
