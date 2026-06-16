import LeanDuckDB

/-! # flowref-etnf — normalise Decompile-Bench into ETNF Parquet (zstd)

Decompile-Bench ships a flat relation `R{name, code, asm, file}` (one row per
binary↔source function pair). That shape is redundant: a `file` path repeats for
every function in it, and identical `code`/`asm` bodies (templates, inlined or
re-emitted code) repeat across rows.

We decompose `R` into **Essential Tuple Normal Form** — a lossless-join
decomposition in which every explicit join dependency has a component that is a
superkey, so no tuple is spurious and none is stored redundantly:

```
  etnf_file(file_id PK, path)                     -- distinct file paths
  etnf_source(code_id PK, code)                   -- distinct source bodies
  etnf_asm(asm_id PK, asm)                         -- distinct assembly bodies
  etnf_function(func_id PK, file_id→, name, code_id→, asm_id→)   -- the fact table
```

IDs are content hashes (`md5`), so the dimension tables are dictionaries that
each store a value once. `R` is recovered by the natural join
`etnf_function ⋈ etnf_file ⋈ etnf_source ⋈ etnf_asm`; because `etnf_function`'s
key `func_id` is a superkey of that JD, the decomposition is in ETNF.

Everything is done through DuckDB (lean-duckdb): each relation is one
self-contained `COPY (...) TO '...parquet' (FORMAT PARQUET, COMPRESSION ZSTD)`
over the source `ndjson`, and a final query verifies the join is lossless.

Usage:  `flowref-etnf <rows.ndjson> <out-dir>`
-/

open DuckDB

/-- Single-quote a string for a SQL literal. -/
def sqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

/-- A scalar query → first cell of the first row (or `""`). -/
def scalar (sql : String) : IO String := do
  let t ← query sql
  pure ((t.rows[0]?.bind (·[0]?)).getD "")

def main (args : List String) : IO Unit := do
  match args with
  | [src, outDir] =>
    IO.FS.createDirAll outDir
    -- Fresh in-memory DB per call, so every statement re-reads the source.
    -- read_json_auto detects the newline-delimited object-per-line layout.
    let reader := s!"read_json_auto({sqlLit src}, format='newline_delimited')"
    let path := fun (n : String) => s!"{outDir}/{n}.parquet"

    let copyRel := fun (name body : String) => do
      let _ ← query s!"COPY ({body}) TO {sqlLit (path name)} (FORMAT PARQUET, COMPRESSION ZSTD)"
      let n ← rowCount (path name)
      IO.println s!"  wrote {name}.parquet  ({n} rows)"

    IO.println s!"== ETNF-normalising {src} → {outDir}/ =="
    let total ← scalar s!"SELECT count(*) FROM {reader}"
    IO.println s!"source rows: {total}"

    -- The four ETNF relations. DISTINCT on the dimensions is the dedup; the fact
    -- table carries only keys + the one essential non-key attribute (name).
    copyRel "etnf_file"
      s!"SELECT DISTINCT md5(file) AS file_id, file AS path FROM {reader}"
    copyRel "etnf_source"
      s!"SELECT DISTINCT md5(code) AS code_id, code FROM {reader}"
    copyRel "etnf_asm"
      s!"SELECT DISTINCT md5(asm) AS asm_id, asm FROM {reader}"
    copyRel "etnf_function"
      (s!"SELECT DISTINCT md5(concat_ws('␟', file, name, code, asm)) AS func_id, " ++
       s!"md5(file) AS file_id, name, md5(code) AS code_id, md5(asm) AS asm_id FROM {reader}")

    -- Redundancy report: how much the dictionaries saved.
    let dF ← rowCount (path "etnf_file")
    let dS ← rowCount (path "etnf_source")
    let dA ← rowCount (path "etnf_asm")
    IO.println s!"dedup: {total} rows → {dF} files, {dS} sources, {dA} asm bodies"

    -- Lossless-join verification: reconstruct R and diff (set semantics) against
    -- the DISTINCT original. missing = extra = 0 ⇒ the decomposition is faithful.
    let pFn := path "etnf_function"; let pFile := path "etnf_file"
    let pSrc := path "etnf_source";  let pAsm := path "etnf_asm"
    let rpFn := s!"read_parquet({sqlLit pFn})"
    let rpFile := s!"read_parquet({sqlLit pFile})"
    let rpSrc := s!"read_parquet({sqlLit pSrc})"
    let rpAsm := s!"read_parquet({sqlLit pAsm})"
    let verify :=
      s!"WITH recon AS (" ++
      s!"  SELECT fn.name, f.path AS file, s.code, a.asm" ++
      s!"  FROM {rpFn} fn" ++
      s!"  JOIN {rpFile} f USING(file_id)" ++
      s!"  JOIN {rpSrc} s USING(code_id)" ++
      s!"  JOIN {rpAsm} a USING(asm_id))," ++
      s!"orig AS (SELECT DISTINCT name, file, code, asm FROM {reader}) " ++
      s!"SELECT (SELECT count(*) FROM (SELECT * FROM orig EXCEPT SELECT * FROM recon)) AS missing, " ++
      s!"       (SELECT count(*) FROM (SELECT * FROM recon EXCEPT SELECT * FROM orig)) AS extra"
    let t ← query verify
    let missing := (t.column "missing")[0]?.getD "?"
    let extra   := (t.column "extra")[0]?.getD "?"
    if missing == "0" ∧ extra == "0" then
      IO.println s!"lossless-join verified: reconstruction == original (missing=0, extra=0) ✓"
    else
      IO.eprintln s!"ETNF VERIFY FAILED: missing={missing} extra={extra}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "usage: flowref-etnf <rows.ndjson> <out-dir>"
    IO.Process.exit 2
