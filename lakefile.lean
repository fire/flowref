import Lake
open Lake DSL System

package flowref where
  -- moreLeancArgs / moreLinkArgs left default

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
    "-Wl,--end-group"]

-- ETNF normaliser: reads Decompile-Bench rows (ndjson) and writes redundancy-free
-- Parquet relations (zstd) via DuckDB. Links the vendored libduckdb.so (Lake does
-- not propagate a dependency's moreLinkArgs, so we repeat them here per the
-- lean-duckdb README).
lean_exe «flowref-etnf» where
  root := `Etnf
  moreLinkArgs := #[
    "-L.lake/packages/lean_duckdb/vendor", "-lduckdb",
    "-Wl,-rpath,$ORIGIN/../../packages/lean_duckdb/vendor"]
