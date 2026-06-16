import Lake
open Lake DSL System

package flowref where
  -- moreLeancArgs / moreLinkArgs left default

/-! ## ELF parser FFI (elfutils libelf/gelf).
    `ffi/elf_shim.c` is C glue over the system `libelf` (elfutils): it returns a
    TSV dump (header machine/class/endian, sections, FUNC symbols) that
    `Flowref/Elf.lean` parses. Mirrors the lean-capstone shim pattern. The
    `elfshim` static glue is linked transitively as an `extern_lib`; the `flowref`
    exe additionally links the system `-lelf`. -/

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

-- DuckDB binding: Parquet (+ zstd) read/write and SQL, used to normalise the
-- Decompile-Bench corpus into ETNF relations (see `Etnf.lean`). `lake update`
-- runs the dep's post_update hook, which vendors `libduckdb.so` into
-- `.lake/packages/lean_duckdb/vendor/` (linked by `flowref-etnf` below).
require lean_duckdb from git
  "https://github.com/v-sekai-multiplayer-fabric/lean-duckdb" @ "main"

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
    "-Wl,--end-group",
    -- elfutils libelf, for the ELF parser shim (ffi/elf_shim.c). Referenced by
    -- full path (like the capstone archive above) so we don't add a system-wide
    -- -L that would shadow the toolchain libc. Matches `pkg-config --libs libelf`.
    "/home/linuxbrew/.linuxbrew/lib/libelf.so"]

-- ETNF normaliser: reads Decompile-Bench rows (ndjson) and writes redundancy-free
-- Parquet relations (zstd) via DuckDB. Links the vendored libduckdb.so (Lake does
-- not propagate a dependency's moreLinkArgs, so we repeat them here per the
-- lean-duckdb README).
lean_exe «flowref-etnf» where
  root := `Etnf
  moreLinkArgs := #[
    "-L.lake/packages/lean_duckdb/vendor", "-lduckdb",
    "-Wl,-rpath,$ORIGIN/../../packages/lean_duckdb/vendor"]
