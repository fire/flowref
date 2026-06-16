# flowref ⇆ Decompile-Bench

Evaluating flowref against **Decompile-Bench** (Tan, Tian, Qi, et al., 2025 —
see `../CITATIONS.bib`), a million-scale corpus of real-world binary↔source
function pairs.

* Function pairs: <https://huggingface.co/datasets/LLM4Binary/decompile-bench>
  — `{name, code, asm, file}`.
* **Released binaries** (preferred): <https://huggingface.co/datasets/LLM4Binary/decompile-bench-bins>.

## Why the binary side

flowref has its own disassembler (lean-capstone). So we drive evaluation from
the **released binaries**, not the dataset's textual `asm` column, and let
flowref do every disassembly itself — `objdump` is never used (it is denied in
`../.claude/settings.json`). The dataset's `code` column is the **reference**
(ground truth) we pair each binary function against.

```
  decompile-bench-bins ──▶ flowref decompile (lean-capstone) ──▶ candidate C
  decompile-bench.code ───────────────────────────────────────▶ reference C
                              equiv.sh: compile both, run, compare → verdict
```

(The textual-`asm` path still exists — `flowref decompile-asm` via the
`asmDecoder` — as a fallback for when only a listing is available; it expects
**Intel**-syntax objdump output, the kernel's native form.)

## The equivalence oracle — `equiv.sh`

> *"If you are able to prove equivalence to their code, you win."*

`equiv.sh` decides whether flowref's recovered C is **functionally equivalent**
to the reference source by differential execution: it compiles
`flowref`'s `sub_<addr>()` and the reference function, calls both, and compares
the returned values.

```
EQUIVALENT       same value(s) returned
NOT-EQUIVALENT   they differ
INCOMPARABLE     can't be compared yet (unresolved call to another sub, or a
                 non-void signature flowref cannot model — see Limits)
```

## Demonstration — `equiv-demo.sh` (runnable now, no network)

```text
$ ./equiv-demo.sh
== flowref equivalence demo (binary side ⇆ source side; flowref disasm only) ==
  k7     (...): EQUIVALENT  (both return 7)
  kshift (...): EQUIVALENT  (both return 16)
  kxor   (...): EQUIVALENT  (both return 240)
  kchain (...): EQUIVALENT  (both return 12)

RESULT: 4/4 proven functionally equivalent to their source.
```

Each function is compiled to an object (the binary side), flowref's own
disassembler lifts its byte region, and the recovered C is proven to return the
same value as the source. This is the full methodology end-to-end on a class
flowref can model today.

## Honest limits (what "win" does *not* yet cover)

The proof currently holds for **parameterless, register-only leaf functions**.
Three real gaps stand between this and equivalence on arbitrary Decompile-Bench
rows — each is a concrete next step, not hand-waving:

1. **No parameter / calling-convention model.** flowref emits `sub_(void)`, so
   functions that take arguments are `INCOMPARABLE` (the oracle cannot feed them
   inputs). Modelling the SysV/cdecl ABI would let the oracle randomised-
   differential-test input→output. *This is the main blocker.*
2. **x86 / PowerPC pattern families.** Decoding is universal — `x64` and every
   other Capstone target are wired (`capstoneSpec?`), so the bins decode
   natively. But the kernel's def/use/return *patterns* are written for x86 and
   PowerPC; other targets decode + emit a compilable stub but recover little
   data-flow until a pattern family is added. Sub-register aliasing
   (`eax`⊂`rax`) is also not yet modelled, so some x64 returns fall back to the
   base local.
3. **Leaf functions only.** A call to another `sub_` is `INCOMPARABLE` until the
   callee is provided or stubbed.

The verdict vocabulary is deliberately honest: `INCOMPARABLE` is reported
distinctly from `NOT-EQUIVALENT`, so the harness never overstates a "win."

## Fetching real pairs — `fetch_pairs.py`

Best-effort streaming loader (needs `datasets` + network; not in CI). It prints
the dataset `features` so you can adapt field extraction, then writes
`out/<i>.bin` + `out/<i>.c` pairs to feed `equiv.sh`.
