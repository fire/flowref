#!/usr/bin/env python3
"""Fetch a small sample of Decompile-Bench (binary side) paired with its source.

We PREFER the *binary* release so flowref's own disassembler does the lifting:

    LLM4Binary/decompile-bench-bins   # released ELF/PE binaries
    LLM4Binary/decompile-bench        # {name, code, asm, file} function pairs

This script streams a handful of rows (no full 8 GB download), writes each
binary to ``out/<i>.bin`` and the reference source to ``out/<i>.c``, and prints
the function symbol so you can run the equivalence oracle:

    python3 fetch_pairs.py --n 5 --out ./out
    # then, per pair, locate the function region (readelf) and:
    ./equiv.sh out/0.bin x86 <fnVaddr> <fileOff> <vaddr> <len> out/0.c <symbol>

Requires ``datasets`` and network access; it is intentionally NOT part of CI.
The exact column names in the *bins* config can vary — this script prints the
dataset ``features`` first so you can adapt the field extraction below.
"""
import argparse, os, sys

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=5)
    ap.add_argument("--out", default="./out")
    ap.add_argument("--dataset", default="LLM4Binary/decompile-bench-bins")
    ap.add_argument("--split", default="train")
    args = ap.parse_args()

    try:
        from datasets import load_dataset
    except ImportError:
        print("error: pip install datasets", file=sys.stderr)
        return 1

    os.makedirs(args.out, exist_ok=True)
    ds = load_dataset(args.dataset, split=args.split, streaming=True)
    print(f"dataset features: {getattr(ds, 'features', '<streaming: features unknown>')}",
          file=sys.stderr)

    written = 0
    for i, row in enumerate(ds):
        if written >= args.n:
            break
        # Heuristic field extraction — adapt to the printed features. We look for
        # a bytes-like binary blob and a source-code string.
        binblob = next((row[k] for k in ("binary", "bin", "elf", "bytes", "content")
                        if k in row and isinstance(row[k], (bytes, bytearray))), None)
        source = next((row[k] for k in ("code", "source", "func", "c")
                       if k in row and isinstance(row[k], str)), None)
        name = row.get("name") or row.get("func_name") or f"fn_{i}"
        if binblob is None or source is None:
            if i == 0:
                print(f"row keys: {list(row.keys())}", file=sys.stderr)
            continue
        with open(os.path.join(args.out, f"{written}.bin"), "wb") as f:
            f.write(binblob)
        with open(os.path.join(args.out, f"{written}.c"), "w") as f:
            f.write(source)
        print(f"{written}.bin  symbol={name}")
        written += 1

    if written == 0:
        print("no usable rows extracted — inspect the printed features/keys and "
              "adapt fetch_pairs.py's field names.", file=sys.stderr)
        return 2
    print(f"wrote {written} pair(s) to {args.out}", file=sys.stderr)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
