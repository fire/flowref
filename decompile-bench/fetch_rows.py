#!/usr/bin/env python3
"""Fetch a sample of Decompile-Bench function pairs as newline-delimited JSON.

Uses the HuggingFace datasets-server `/rows` REST API (no `datasets` library, no
bulk download), paging 100 rows at a time. Output feeds `flowref-etnf`, which
normalises the rows into ETNF Parquet (zstd).

    python3 fetch_rows.py --n 500 --out sample.ndjson
    flowref-etnf sample.ndjson etnf/        # → etnf_{file,source,asm,function}.parquet
"""
import argparse, json, sys, urllib.request

API = ("https://datasets-server.huggingface.co/rows"
       "?dataset=LLM4Binary/decompile-bench&config=default&split=train")

def get(url):
    req = urllib.request.Request(url, headers={"User-Agent": "flowref"})
    return json.load(urllib.request.urlopen(req, timeout=30))

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=500)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--out", default="sample.ndjson")
    args = ap.parse_args()

    written = 0
    with open(args.out, "w") as f:
        off = args.offset
        while written < args.n:
            take = min(100, args.n - written)
            rows = get(f"{API}&offset={off}&length={take}").get("rows", [])
            if not rows:
                break
            for r in rows:
                rr = r["row"]
                f.write(json.dumps({k: rr[k] for k in ("name", "code", "asm", "file")}) + "\n")
                written += 1
            off += len(rows)
    print(f"wrote {written} rows to {args.out}", file=sys.stderr)
    return 0 if written else 2

if __name__ == "__main__":
    raise SystemExit(main())
