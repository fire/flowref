import Flowref.Disasm
import Flowref.Dataflow
import Flowref.Ports
import Flowref.Decoders
import Flowref.Adapters
import Flowref.Toc
import Plausible
import Lean.Data.Json

/-! # flowref — a control-flow-aware cross-reference finder over disassembly

A linear disassembler tells you the instructions; it does *not* tell you where
a value is **defined** vs **used**, because a value is built in one basic block
and consumed in another. `flowref` disassembles a binary (via Capstone) and
recovers those def→use links by walking the control-flow graph.

**The engine is `plausible`, not a hand-written fixpoint.** Every data-flow
query is posed as `∀ candidate witness, ¬(it is the fact we want)` and plausible
hands back the counterexample, which *is* the fact (reaching def, back-edge, …).
The searches are **iteratively deepened**: cheap level first, escalate only the
unresolved frontier — a witness DAG (see `Flowref/Dataflow.lean`).

The decompiler (lifting a function to compilable C) lives in a separate repo,
[`fire/flowref-decompiler`](https://github.com/fire/flowref-decompiler), built on
this disassembler.
-/

open Plausible Flowref
open Lean (Json toJson)

/-- Version string. -/
def flowrefVersion : String :=
  "flowref 2.0.0 — control-flow-aware xref over disassembly, with a " ++
  "plausible-driven iterative-deepening witness DAG"

/-- `--json` output uses `Lean.Json` (toolchain `Lean.Data.Json`) so string
escaping and rendering are the library's, not ours. `jn` is a small alias for
turning a `Nat` into a JSON number. -/
def jn (n : Nat) : Json := toJson n

/-- Full usage text. -/
def usageText : String :=
  "flowref — control-flow-aware cross-reference finder over machine-code disassembly\n\n" ++
  "USAGE (ELF — arch, file offset, vaddr & length read from the headers):\n" ++
  "  flowref list  <binary>                                       (functions + detected arch)\n" ++
  "  flowref xref  <binary>  <symbol|0xVaddr> <targetHex> [--arch=<a>] [--search-trace]\n\n" ++
  "USAGE (explicit region — for raw blobs / stripped binaries):\n" ++
  "  flowref xref      <binary>  <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex> [--search-trace]\n" ++
  "  flowref xref-asm  <listing> <arch> <targetHex>  [--search-trace]   (objdump-style .asm text)\n\n" ++
  "DEMOS:\n" ++
  "  flowref demo         list the demos\n" ++
  "  flowref demo deep    iterative-deepening witness-DAG escalation\n\n" ++
  "MISC:\n" ++
  "  flowref <binary> <arch> <targetHex> <fileOffHex> <vaddrHex> <lenHex>   (legacy xref)\n" ++
  "  flowref --help | -h | --version\n\n" ++
  "ARGS:\n" ++
  "  arch        x86 (32-bit) | x64 (x86-64) | ppc | ppc64 | … (see capstoneSpec?)\n" ++
  "  targetHex   address/constant to find references to\n" ++
  "  fileOffHex  start offset of the region in the file\n" ++
  "  vaddrHex    virtual/load address that fileOff maps to\n" ++
  "  lenHex      length of the region to disassemble\n\n" ++
  "FLAGS:\n" ++
  "  --search-trace  print the iterative-deepening escalation chain to stderr\n" ++
  "  --arch=<a>      force the arch for the ELF short forms (else read from header)\n" ++
  "  --json          machine-readable output for list / xref (stdout)\n" ++
  "  --help, -h      this help\n" ++
  "  --version       version string\n\n" ++
  "Lifting a function to C is a separate tool: github.com/fire/flowref-decompiler\n"


/-- A deep self-test: `mov esi, 0x1000` then a long clobber-free run of `nop`s,
then `mov eax, [esi+4]` (a use of esi). The def→use walk must cross the whole
run, so the shallow L0 budget (64 steps) is hit (UNRESOLVED) and the query only
resolves once iterative deepening escalates to L1 (512 steps). This is the
demonstrable iterative-deepening case. `nNops` controls the chain length. -/
def demoDeepInsns (nNops : Nat) : Array Ins :=
  let prologue : Array UInt8 := #[0xBE, 0x00, 0x10, 0x00, 0x00]  -- mov esi, 0x1000
  let nops : Array UInt8 := Array.replicate nNops 0x90           -- nop * nNops
  let epilogue : Array UInt8 := #[0x8B, 0x46, 0x04, 0xC3]        -- mov eax,[esi+4]; ret
  let bytes : ByteArray := ByteArray.mk (prologue ++ nops ++ epilogue)
  capstoneDecoder.decode .x86 (bytes, 0x1000)

/-- Run the deep demo and report the escalation outcome for the `esi` use. -/
def demoDeep : IO Unit := do
  let insns := demoDeepInsns 100
  let nI := insns.size
  let mut addr2idx : Std.HashMap Nat Nat := {}
  for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
  -- the use is the penultimate instruction (`mov eax, [esi+4]`).
  let useIdx := nI - 2
  IO.println s!"=== iterative-deepening demo: {nI} insns, esi def at idx 0, use at idx {useIdx} ==="
  IO.println "Per-level outcome for reaching-def query (esi @ the use):"
  for lvl in ladder do
    let failure ← certifyReaching lvl insns addr2idx .x86 useIdx "esi"
    let (defs, budget) := reachingDefsB lvl.walkSteps insns addr2idx .x86 useIdx "esi"
    let status :=
      if ¬ defs.isEmpty then s!"RESOLVED (reaching def idx {defs}) plausible-found={failure}"
      else if budget then "UNRESOLVED (budget hit — escalate)"
      else "provably-none"
    IO.println s!"  L{lvl.idx} (walkSteps={lvl.walkSteps}, Fin {lvl.finBound}): {status}"
  -- the adaptive driver picks the first level that resolves it:
  let (defs, lvl, _te) ← resolveReachingDef insns addr2idx .x86 useIdx "esi"
  IO.println s!"\nAdaptive driver resolved esi@use at level L{lvl} with def(s) {defs}."
  IO.println "The shallow L0 search could NOT resolve it (budget hit); deepening did."


/-- Help for the `demo` subcommand family. -/
def demoHelp : String :=
  "flowref demo — built-in self-tests (no disk needed)\n\n" ++
  "  flowref demo deep    iterative-deepening witness-DAG escalation (def→use across 100 nops)\n"

/-- `flowref list <bin>` — read the ELF and print the detected arch plus the
FUNC symbols (name, vaddr, size). This is the discovery menu you pick from for
`xref <bin> <name> <target>`. Fails cleanly if `bin` is not an ELF. -/
def runList (bin : String) (json : Bool := false) : IO Unit := do
  match ← readElf bin with
  | none =>
    let msg ← notElfMessage bin
    if json then IO.println (Json.mkObj [("error", Json.str msg)]).compress
    else IO.eprintln s!"error: {msg}"
    IO.Process.exit 3
  | some info =>
    let archTok := info.arch
    let cls := if info.is64 then "ELF64" else "ELF32"
    let endian := if info.littleEndian then "LE" else "BE"
    let fns := info.functions
    if json then
      let fnsJson := fns.map (fun fn => Json.mkObj
        [("name", Json.str fn.name), ("vaddr", jn fn.vaddr), ("size", jn fn.size)])
      IO.println (Json.mkObj [("file", Json.str bin), ("class", Json.str cls),
        ("endian", Json.str endian), ("arch", Json.str archTok),
        ("entry", jn info.entry), ("functionCount", jn fns.size),
        ("functions", Json.arr fnsJson)]).compress
      return
    let archShow := if archTok.isEmpty then s!"unknown (e_machine={info.machine})" else archTok
    IO.println s!"{bin}: {cls} {endian}  arch={archShow}  entry=0x{hex info.entry}  functions={fns.size}"
    if fns.isEmpty then
      IO.println "  (no FUNC symbols — binary may be stripped; use the explicit-region form)"
    else
      IO.println "  VADDR       SIZE    NAME"
      for fn in fns do
        IO.println s!"  0x{hex fn.vaddr}  {fn.size}\t{fn.name}"

def main (args : List String) : IO Unit := do
  let hasFlag := fun (f : String) => args.contains f
  let showTrace := hasFlag "--search-trace"
  let asJson := hasFlag "--json"
  -- `--arch=<tok>` forces the arch for the ELF-resolved short forms (rare:
  -- a misidentified e_machine). Otherwise the arch comes from the ELF header.
  let archOverride? := (args.find? (·.startsWith "--arch=")).map (·.drop 7 |>.toString)
  let positional := args.filter (fun s => ¬ s.startsWith "--")
  match args with
  | [] => IO.eprintln usageText; IO.Process.exit 2
  | _ =>
  if hasFlag "--help" ∨ hasFlag "-h" then IO.println usageText; return
  if hasFlag "--version" then IO.println flowrefVersion; return
  -- Legacy `--demo-deep` flag kept as an alias for `demo deep`.
  if hasFlag "--demo-deep" then demoDeep; return
  match positional with
  -- ── demo subcommand ─────────────────────────────────────────────────────
  | ["demo"] => IO.println demoHelp
  | "demo" :: "deep" :: _ => demoDeep
  | "demo" :: name :: _ =>
    IO.eprintln s!"unknown demo '{name}' (try: deep)"; IO.Process.exit 2
  -- ── list (ELF discovery) ────────────────────────────────────────────────
  | "list" :: bin :: _ => guard (runList bin asJson)
  -- ── xref ───────────────────────────────────────────────────────────────
  -- ELF short form: <bin> <fnSym|fnAddr> <targetHex> — region from the ELF,
  -- target is what to find references to.
  | ["xref", bin, fnTarget, tgtS] =>
    guard (xrefElf bin fnTarget tgtS archOverride? showTrace asJson)
  | "xref" :: bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace asJson)
  | "xref-asm" :: path :: archS :: tgtS :: _ =>
    guard (xref (asmFileAdapter archS path) tgtS showTrace asJson)
  -- ── legacy positional xref ─────────────────────────────────────────────
  | bin :: archS :: tgtS :: foS :: vaS :: lenS :: _ =>
    guard (xref (binaryFileAdapter bin archS foS vaS lenS) tgtS showTrace asJson)
  | _ => IO.eprintln usageText; IO.Process.exit 2
where
  /-- Run an analysis action, mapping any `IO` error to a clean message + exit 4.
  This keeps the untrusted-input failures (raised by the adapters) from dumping
  a stack trace. -/
  guard (act : IO Unit) : IO Unit := do
    try act catch e => IO.eprintln s!"error: {e.toString}"; IO.Process.exit 4
  /-- ELF-resolved xref: resolve a function region from `(bin, fnTarget)`, then
  search it for def→use witnesses reaching `tgtS`. -/
  xrefElf (bin fnTarget tgtS : String) (archOverride? : Option String)
      (showTrace json : Bool) : IO Unit := do
    let r ← elfResolveRegion bin fnTarget archOverride?
    let symNote := match r.symbol with | some s => s!" ({s})" | none => ""
    IO.eprintln s!"resolved region{symNote}: arch={r.arch} vaddr=0x{hex r.vaddr} fileOff=0x{hex r.fileOff} len=0x{hex r.len}"
    -- PPC64 ELFv1: also resolve TOC-relative (`r2`) references. The module `r2`
    -- is recovered authoritatively from `.opd`; a `ld off(r2)` / `addis r2,…`
    -- site that lands on `target` is a reference the immediate-only walk cannot
    -- see (the address is in a `.toc1` cell, not built by `lis/addi`).
    runTocXref bin r.arch tgtS r json
    xref (elfBinaryAdapter r bin) tgtS showTrace json
  /-- PPC64 TOC-relative reference search. Recover the module `r2` from `.opd`,
  then scan the resolved region for `ld off(r2)` / `addis r2,…` sites whose
  TOC-resolved address equals `target`. Witnesses (and the recovered `r2`) are
  printed; in `--json` mode they go to stderr so the JSON stdout object from the
  immediate-walk `xref` stays a single clean record. A no-op for non-PPC. -/
  runTocXref (bin arch tgtS : String) (r : Flowref.ElfRegion) (json : Bool) : IO Unit := do
    if arch != "ppc64" ∧ arch != "ppc64be" ∧ arch != "ppc64le" ∧ arch != "ppc" then return
    let target : Int ← match parseImm? tgtS with
      | some v => pure v
      | none   => return            -- xref proper will report the bad target
    match ← Flowref.readElfBytes bin with
    | none => return
    | some eb =>
      match eb.recoverR2? with
      | none =>
        IO.eprintln "TOC: no .opd TOC base recovered (module may not use a TOC); skipping TOC resolution"
      | some r2 =>
        IO.eprintln s!"TOC: recovered r2/TOC base = 0x{hex r2} (from .opd)"
        -- decode the resolved region and scan it for TOC references to target.
        let (_a, _bits, insns) ← (elfBinaryAdapter r bin).run
        let wits := Flowref.scanTocXref eb (Int.ofNat r2) target insns
        if wits.isEmpty then
          IO.eprintln s!"TOC: no r2-relative site in this region resolves to 0x{hex target.toNat}"
        else
          let hdr := s!"TOC: {wits.size} r2-relative reference(s) to 0x{hex target.toNat}:"
          if json then IO.eprintln hdr else IO.println hdr
          for w in wits do
            let line := s!"  @0x{hex w.vaddr}: {w.insn}  → 0x{hex w.resolved}"
            if json then IO.eprintln line else IO.println line
  /-- A single-target def→use witness search, with
  iterative deepening over the CFG-walk budget, over any `SourceAdapter`. -/
  xref (adapter : SourceAdapter) (tgtS : String) (showTrace json : Bool) : IO Unit := do
    let target : Int ← match parseImm? tgtS with
      | some v => pure v
      | none => throw (IO.userError s!"invalid target '{tgtS}' (expected hex like 0x401010 or a decimal)")
    let (a, _bits, insns) ← adapter.run
    if insns.isEmpty then IO.eprintln "error: empty disassembly for the given region"; IO.Process.exit 3
    let nI := insns.size
    let mut addr2idx : Std.HashMap Nat Nat := {}
    for i in [0:nI] do addr2idx := addr2idx.insert insns[i]!.addr i
    let succ := fun (i : Nat) =>
      let ins := insns[i]!
      let ft := if isUncondJmp a ins ∨ i+1 ≥ nI then [] else [i+1]
      let bt := match branchTarget a ins with
        | some t => (match addr2idx[t]? with | some j => [j] | none => ([] : List Nat))
        | none => ([] : List Nat)
      ft ++ bt
    -- walk with a step budget; report (hitAddr?, budgetExhausted?).
    let walk := fun (steps start : Nat) (reg : String) (val : Int) =>
      Id.run do
        let mut seen : Std.HashSet Nat := {}
        let mut stack := succ start
        let mut s := 0
        while ¬stack.isEmpty ∧ s < steps do
          s := s + 1
          match stack with
          | [] => pure ()
          | kk :: rest =>
            stack := rest
            if ¬ seen.contains kk ∧ kk < nI then
              seen := seen.insert kk
              let ins := insns[kk]!
              match useDisp a ins reg with
              | some disp => if val + disp == target then return (some ins.addr, false)
              | none => pure ()
              if ¬ clobbers a ins reg then stack := succ kk ++ stack
        pure (none, s ≥ steps ∧ ¬ stack.isEmpty)
    let defs := (Array.range nI).filterMap (fun i =>
      match defOf a insns[i]! with
      | some (r, v) => if (target - v).toNat < 0x10000 ∨ v == target then some (i, r, v) else none
      | none => none)
    if ¬ json then
      IO.println s!"insns={nI}, def-witness candidates={defs.size}, target=0x{hex target.toNat}"
    -- iterative deepening over the walk budget for the whole def set.
    let mut found := false
    let mut traceLines : Array String := #[]
    let mut witnesses : Array Json := #[]   -- witness records (for --json)
    for (i, rg, v) in defs do
      let mut resolved := false
      for lvl in ladder do
        if ¬ resolved then
          let (hit, budget) := walk lvl.walkSteps i rg v
          match hit with
          | some ua =>
            found := true; resolved := true
            traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} → use@0x{hex ua} resolved at L{lvl.idx}"
            witnesses := witnesses.push
              (Json.mkObj [("def", jn insns[i]!.addr), ("reg", Json.str rg),
                ("val", jn v.toNat), ("use", jn ua), ("level", jn lvl.idx)])
            if ¬ json then
              IO.println s!"  ~ def @0x{hex insns[i]!.addr} ({rg}={v}) → use @0x{hex ua}  [L{lvl.idx}]"
          | none =>
            if ¬ budget then resolved := true   -- provably none at this depth
            else if lvl.idx == ladder.size - 1 then
              traceLines := traceLines.push s!"def {rg}@0x{hex insns[i]!.addr} UNRESOLVED (budget hit at L{lvl.idx})"
    -- plausible certification that a witness exists among the defs (existence).
    let cfg : Plausible.Configuration := { numInst := 2000, quiet := true }
    let r ← Testable.checkIO
      (NamedBinder "w" (∀ w : Fin 4096,
        (match defs[w.val]? with
         | some (i, rr, v) => ((walk 4000 i rr v).1).isNone
         | none => true) = true)) cfg
    let foundAny := found || r.isFailure
    if json then
      IO.println (Json.mkObj [("insns", jn nI), ("candidates", jn defs.size),
        ("target", jn target.toNat), ("found", Json.bool foundAny),
        ("witnesses", Json.arr witnesses)]).compress
    else
      if foundAny then
        IO.println s!"FOUND a witness DAG to target (plausible counterexample: {r.isFailure})"
      else
        IO.println "no witness DAG reaches the target in this region"
      if showTrace then
        IO.eprintln "=== iterative-deepening search trace ==="
        for l in traceLines do IO.eprintln s!"  {l}"
