import Lake
open Lake DSL System

package flowref where
  -- moreLeancArgs / moreLinkArgs left default

/-! ## ELF parser FFI (self-contained — no external library).
    `ffi/elf_shim.c` parses ELF directly using the standard `<elf.h>` struct
    definitions (libc header-only): it returns a TSV dump (header
    machine/class/endian, sections, FUNC symbols) that `Flowref/Elf.lean` parses.
    Mirrors the lean-capstone shim pattern. Crucially there is **no library to
    link** — no libelf/gelf, no pkg-config, no CI package, no runtime `.so`. The
    `elfshim` static glue is linked transitively as an `extern_lib`. -/

target elfShimO pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "elf_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / "elf_shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc" getLeanTrace

extern_lib libelfshim pkg := do
  let name := nameToStaticLib "elfshim"
  let oJob ← elfShimO.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.30.0"

-- Multi-arch disassembler (typed Capstone wrapper). Provides the `Capstone`
-- module + the C glue; the static `libcapstone.a` is linked below.
require «lean-capstone» from git
  "https://github.com/fire/lean-capstone" @ "main"

@[default_target] lean_lib Flowref where
  -- pick up Flowref.lean and every Flowref/*.lean submodule.
  globs := #[.one `Flowref, .submodules `Flowref]

@[default_target] lean_exe flowref where
  root := `Flowref
  -- Link the multi-arch Capstone static archive vendored by lean-capstone.
  -- Grouped so the shim's cs_* symbols resolve against libcapstone.a.
  -- After `lake update`, run the dep's build.sh once to produce the archive:
  --   .lake/packages/lean-capstone/thirdparty/capstone/build.sh
  moreLinkArgs := #[
    "-Wl,--start-group",
    ".lake/packages/lean-capstone/thirdparty/capstone/lib/libcapstone.a",
    "-Wl,--end-group"]
    -- The ELF parser is the self-contained `<elf.h>` shim (`libelfshim` extern_lib,
    -- linked transitively) — no external library.
