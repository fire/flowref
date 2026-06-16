import Flowref.Ports
import Capstone

/-! # flowref — data **decoders** (adapters for the `Decoder` port)

A decoder turns a raw representation into the kernel's `Ins` model. Two formats
are supported:

* `capstoneDecoder` — machine-code **bytes** → `Ins`, via the typed Capstone
  wrapper. This is the primary path (raw PE/ELF, Decompile-Bench *bins*).
* `asmDecoder` — an **objdump-style assembly listing** (text) → `Ins`. This lets
  flowref ingest the textual `asm` column of a dataset row directly, without a
  binary. It is tolerant: unparsable lines are skipped, and AT&T sigils
  (`%`, `$`) are stripped so operands read like the kernel's token model.

Decoders are pure and format-only; fetching the bytes/text is the adapters' job.
-/

open Capstone

namespace Flowref

/-- Resolve an arch name to a Capstone `(arch, mode)` **and** the kernel pattern
family `A`. **Every architecture the vendored Capstone build supports is wired
here** — decoding is universal. The pattern *family* (`A`) only selects which
textual def/use/branch rules the kernel applies: flowref ships real families for
x86 (all widths) and PowerPC; every other target decodes correctly and lifts to
a compilable-but-mostly-commented C stub under the `.x86` default family until a
dedicated family is added (a kernel change, isolated from this decoder). `none`
⇒ unrecognised name. -/
def capstoneSpec? (s : String) : Option (Capstone.Arch × Mode × A) :=
  let le := Mode.littleEndian
  let be := Mode.bigEndian
  match s.trimAscii.toString with
  -- x86 / x86-64 (real pattern family)
  | "x86" | "x86-32" | "x86_32" | "i386" | "ia32"      => some (.x86, Mode.b32, .x86)
  | "x64" | "x86-64" | "x86_64" | "amd64" | "em64t"    => some (.x86, Mode.b64, .x86)
  | "x16" | "real" | "8086"                            => some (.x86, Mode.b16, .x86)
  -- PowerPC (real pattern family)
  | "ppc" | "ppc32" | "powerpc"                        => some (.ppc, Mode.b32 ||| be, .ppc)
  | "ppc64" | "ppc64be" | "powerpc64"                  => some (.ppc, Mode.b64 ||| be, .ppc)
  | "ppc64le"                                          => some (.ppc, Mode.b64 ||| le, .ppc)
  -- ARM
  | "arm" | "arm32" | "armle" | "armel"                => some (.arm, le, .x86)
  | "armbe" | "armeb"                                  => some (.arm, be, .x86)
  | "thumb" | "thumb2"                                 => some (.arm, Mode.thumb, .x86)
  | "armv8" | "arm32v8"                                => some (.arm, Mode.v8, .x86)
  -- AArch64
  | "aarch64" | "arm64" | "arm64le"                    => some (.aarch64, le, .x86)
  | "arm64be"                                          => some (.aarch64, be, .x86)
  -- MIPS
  | "mips" | "mips32"                                  => some (.mips, Mode.b32 ||| le, .x86)
  | "mips32be"                                         => some (.mips, Mode.b32 ||| be, .x86)
  | "mips64"                                           => some (.mips, Mode.b64 ||| le, .x86)
  | "mips64be"                                         => some (.mips, Mode.b64 ||| be, .x86)
  -- SPARC
  | "sparc"                                            => some (.sparc, be, .x86)
  | "sparc64" | "sparcv9"                              => some (.sparc, Mode.v9 ||| be, .x86)
  -- SystemZ / s390x
  | "systemz" | "sysz" | "s390x"                       => some (.systemz, be, .x86)
  -- RISC-V
  | "riscv" | "riscv32"                                => some (.riscv, Mode.riscv32, .x86)
  | "riscv64"                                          => some (.riscv, Mode.riscv64, .x86)
  -- everything else Capstone enables: one canonical name each
  | "m68k" | "68k"                                     => some (.m68k, be, .x86)
  | "m680x"                                            => some (.m680x, le, .x86)
  | "tms320c64x" | "c64x"                              => some (.tms320c64x, be, .x86)
  | "evm"                                              => some (.evm, le, .x86)
  | "mos65xx" | "6502" | "65xx"                        => some (.mos65xx, le, .x86)
  | "wasm"                                             => some (.wasm, le, .x86)
  | "bpf" | "ebpf"                                     => some (.bpf, le, .x86)
  | "sh" | "superh"                                    => some (.sh, be, .x86)
  | "tricore"                                          => some (.tricore, le, .x86)
  | "alpha"                                            => some (.alpha, le, .x86)
  | "hppa" | "parisc"                                  => some (.hppa, be, .x86)
  | "loongarch" | "loongarch64" | "la64"               => some (.loongarch, Mode.b64, .x86)
  | "xtensa"                                           => some (.xtensa, le, .x86)
  | "arc"                                              => some (.arc, le, .x86)
  | "xcore"                                            => some (.xcore, be, .x86)
  | _ => none

/-- Decode raw bytes with an explicit Capstone `(arch, mode)` at load addr `va`. -/
def capstoneDecodeBytes (carch : Capstone.Arch) (cmode : Mode)
    (bytes : ByteArray) (va : Nat) : Array Ins :=
  (disasm carch cmode bytes va).map
    (fun x => ({ addr := x.addr, mn := x.mnemonic, ops := x.ops } : Ins))

/-- **Capstone byte decoder** for the `Decoder` port. Used by the built-in
32-bit-x86 demos (`decode .x86`); the binary adapter uses `capstoneSpec?` to
reach every wired width/target. -/
def capstoneDecoder : Decoder (ByteArray × Nat) where
  name := "capstone"
  decode := fun a (bytes, va) =>
    let (carch, cmode) :=
      if a == .ppc then (Capstone.Arch.ppc, Mode.b64 ||| Mode.bigEndian)
      else (Capstone.Arch.x86, Mode.b32)
    capstoneDecodeBytes carch cmode bytes va

/-! ## objdump / assembly-listing text decoder -/

/-- Value of a single hex digit, or `none`. -/
private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Read a leading hex address (optional `0x`), returning `(value, rest)`. -/
private def leadingHex? (s0 : String) : Option (Nat × String) :=
  let s := s0.trimAscii.toString
  let s := if s.startsWith "0x" ∨ s.startsWith "0X" then (s.drop 2).toString else s
  let chars := s.toList
  let ds := chars.takeWhile (fun c => (hexDigit? c).isSome)
  if ds.isEmpty then none
  else
    let n := ds.foldl (fun n c => n * 16 + (hexDigit? c).getD 0) 0
    some (n, String.ofList (chars.dropWhile (fun c => (hexDigit? c).isSome)))

/-- Strip AT&T sigils (`%rbp`→`rbp`, `$0x1`→`0x1`) so the kernel's textual,
Intel-ish operand patterns have a chance of matching. Memory parens are kept
(the PowerPC path reads `disp(rN)`). -/
private def deAtt (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c != '%' ∧ c != '$'))

private def isSpace (c : Char) : Bool := c == ' ' ∨ c == '\t'

/-! ### AT&T → Intel normalisation (decoder-local; the kernel is Intel-only)

The Decompile-Bench `asm` column (and `objdump` default) is **AT&T**: operand
order is reversed (`src, dst`), immediates carry `$`, registers `%`, memory is
`disp(base, index, scale)`, and mnemonics carry size suffixes (`movl`, `addq`).
flowref's kernel patterns are Intel/no-suffix, so we normalise here — entirely
inside the decoder, so nothing in the kernel changes. -/

/-- Split an operand list on **top-level** commas (commas inside `(...)` — the
AT&T memory `base,index,scale` — are kept). -/
private def splitTopComma (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur : String := ""
  let mut depth : Nat := 0
  for c in s.toList do
    if c == '(' then depth := depth + 1; cur := cur.push c
    else if c == ')' then depth := depth - 1; cur := cur.push c
    else if c == ',' ∧ depth == 0 then out := out ++ [cur]; cur := ""
    else cur := cur.push c
  pure (out ++ [cur])

/-- Convert one AT&T operand to Intel. Memory `disp(base,index,scale)` becomes
`[base+index*scale+disp]`; registers/immediates pass through (sigils already
stripped by `deAtt`). -/
private def attMemToIntel (op0 : String) : String :=
  let op := op0.trimAscii.toString
  match op.splitOn "(" with
  | [_] => op                              -- no '(' ⇒ register / immediate / disp
  | disp :: rest =>
    let inner := ((String.intercalate "(" rest).splitOn ")").headD ""
    let parts := (inner.splitOn ",").map (·.trimAscii.toString)
    let base := parts.getD 0 ""
    let index := parts.getD 1 ""
    let scale := parts.getD 2 ""
    let d := disp.trimAscii.toString
    let e0 := base
    -- Emit Capstone-Intel-style *spaced* operators (`[rip - 0x34]`, `[rbp + rax*4]`)
    -- so the kernel's `readsRegs` (which splits on spaces/`+`/`*`) extracts every
    -- base/index register and declares it. Unspaced `rip-0x34` would hide `rip`.
    let e1 := if index ≠ "" then
        (if e0 == "" then index else e0 ++ " + " ++ index) ++
        (if scale ≠ "" ∧ scale ≠ "1" then "*" ++ scale else "")
      else e0
    let e2 := if d == "" then e1
      else if d.startsWith "-" then
        (if e1 == "" then d else e1 ++ " - " ++ (d.drop 1).toString)
      else (if e1 == "" then d else e1 ++ " + " ++ d)
    "[" ++ e2 ++ "]"
  | [] => op

/-- x86 mnemonic stems that take an AT&T size suffix (`b`/`w`/`l`/`q`). -/
private def attStems : List String :=
  ["mov","add","sub","adc","sbb","and","or","xor","cmp","test","lea","imul",
   "mul","idiv","div","inc","dec","neg","not","shl","shr","sar","sal","push",
   "pop","call","ret","xchg"]

/-- Strip an AT&T size suffix from a mnemonic, mapping the sign/zero-extend forms
to the kernel's `movsx`/`movzx`. Jumps (`j…`) keep their condition letters. -/
private def stripSuffix (mn : String) : String :=
  if mn.startsWith "j" then mn
  else if mn.startsWith "movz" then "movzx"
  else if mn.startsWith "movs" ∧ mn.length > 4 then "movsx"
  else match mn.toList.getLast? with
    | some c =>
      if c == 'b' ∨ c == 'w' ∨ c == 'l' ∨ c == 'q' then
        let stem := (mn.dropEnd 1).toString
        if attStems.contains stem then stem else mn
      else mn
    | none => mn

/-- Normalise an AT&T `(mnemonic, operands)` to Intel form: strip the suffix,
reverse operand order, and lower memory operands. -/
private def attToIntel (mn ops : String) : String × String :=
  let parts := (splitTopComma ops).map (·.trimAscii.toString) |>.filter (· ≠ "")
  let intel := parts.reverse.map attMemToIntel
  (stripSuffix mn, String.intercalate ", " intel)

/-- Parse one assembly-listing line into an `Ins`, or `none` if it carries no
address + mnemonic. Accepts the common shapes:

* `  4005a0:\t55\tpush   %rbp`   objdump: addr `:` (hex-bytes col) mnemonic ops
* `4005a0: push rbp`             addr `:` mnemonic ops
* `0x4005a0 push rbp`            addr whitespace mnemonic ops

Blank lines and `#`/`;` comments are skipped. -/
def parseAsmLine (ln0 : String) : Option Ins := do
  let ln := ln0.trimAscii.toString
  if ln.isEmpty ∨ ln.startsWith "#" ∨ ln.startsWith ";" then failure
  -- Skip objdump label / section headers — they end in ':' and carry no insn
  -- (e.g. `0000000000401000 <foo>:`, `Disassembly of section .text:`).
  if ln.endsWith ":" then failure
  let (addr, rest0) ← leadingHex? ln
  let rest1 := rest0.trimAscii.toString
  -- After the address, objdump writes `:` then (often) a tab-separated hex-byte
  -- column before the mnemonic. Take the LAST tab field as `mnemonic operands`.
  let body :=
    if rest1.startsWith ":" then
      let afterColon := (rest1.drop 1).toString
      let fields := (afterColon.splitOn "\t").map (·.trimAscii.toString) |>.filter (¬ ·.isEmpty)
      (fields.getLastD (afterColon.trimAscii.toString))
    else rest1
  -- Strip a trailing AT&T comment (`# imm = 0x…`, `# 0x…`) — objdump/Capstone
  -- annotate immediates this way; the `#` is not part of the operand.
  let body := ((body.splitOn "#").headD body).trimAscii.toString
  if body.isEmpty then failure
  let chars := body.toList
  let mnRaw := String.ofList (chars.takeWhile (fun c => ¬ isSpace c))
  if mnRaw.isEmpty then failure
  let opsRaw := (String.ofList (chars.dropWhile (fun c => ¬ isSpace c))).trimAscii.toString
  -- AT&T is detected by a `%` register sigil; normalise it to Intel in-decoder.
  let isAtt := opsRaw.any (· == '%')
  let ops0 := deAtt opsRaw
  let (mn, ops) := if isAtt then attToIntel mnRaw ops0 else (mnRaw, ops0)
  pure { addr := addr, mn := mn, ops := ops }

/-- Parse a whole assembly listing into `Ins[]`, skipping unparsable lines. -/
def parseAsmListing (text : String) : Array Ins :=
  (text.splitOn "\n").foldl
    (fun acc ln => match parseAsmLine ln with | some i => acc.push i | none => acc) #[]

/-- **objdump/asm text decoder.** A listing → `Ins[]`. -/
def asmDecoder : Decoder String where
  name   := "objdump-asm"
  decode := fun _a text => parseAsmListing text

end Flowref
