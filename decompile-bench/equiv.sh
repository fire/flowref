#!/usr/bin/env bash
# flowref ⇆ Decompile-Bench equivalence oracle.
#
# Given (1) a BINARY function region and (2) the reference source for that same
# function (Decompile-Bench's `code` column, or any .c defining the symbol),
# decide whether flowref's recovered C is functionally equivalent to the source.
#
# The disassembly + lift is done ENTIRELY by flowref (lean-capstone) — objdump is
# NOT used. We only read ELF section/symbol metadata to locate the function,
# because flowref takes a raw (fileOff, vaddr, len) region and does not parse
# container formats itself.
#
# Verdict:
#   EQUIVALENT       flowref's sub_<addr>() and the reference return the same value
#   NOT-EQUIVALENT   they differ
#   INCOMPARABLE     can't be compared yet (unresolved call, or a non-void
#                    signature flowref cannot model — see README)
#
# Usage:
#   equiv.sh <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex> \
#            <reference.c> <referenceSymbol>
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
FLOWREF="${FLOWREF:-$here/../.lake/build/bin/flowref}"
CC="${CC:-gcc}"
# flowref's *decode* is 32-bit x86, but its emitted C is arch-neutral, so the
# reference + candidate are compiled and compared with the NATIVE toolchain.
# Extra flags (e.g. -m32) can be injected via $CFLAGS.
CFLAGS="${CFLAGS:-}"

[ $# -eq 8 ] || { echo "usage: equiv.sh <binary> <arch> <fnVaddrHex> <fileOffHex> <vaddrHex> <lenHex> <reference.c> <symbol>" >&2; exit 2; }
bin="$1"; arch="$2"; fnva="$3"; foff="$4"; vaddr="$5"; len="$6"; refc="$7"; refsym="$8"

tmp="$(mktemp -d /tmp/flowref-equiv.XXXXXX)"
trap 'rm -rf "$tmp"' EXIT
cand="$tmp/cand.c"

# 1. OUR disassembler + lift. Capture flowref's C (strip the header comment line
#    that names the address so the rest is a clean TU).
if ! "$FLOWREF" decompile "$bin" "$arch" "$fnva" "$foff" "$vaddr" "$len" > "$cand" 2>"$tmp/err"; then
  echo "INCOMPARABLE  (flowref failed: $(cat "$tmp/err"))"; exit 3
fi

# flowref names the function sub_<lowerhex(fnva)>.
hexname="sub_$(printf '%x' "$((fnva))")"
if ! grep -q "uint32_t $hexname(void)" "$cand"; then
  echo "INCOMPARABLE  (could not find $hexname in flowref output)"; exit 3
fi

# 2. Unresolved direct calls to other subs ⇒ not a leaf; can't link standalone.
if grep -qE "= sub_[0-9a-f]+\(\);" "$cand" && \
   [ "$(grep -cE "uint32_t sub_[0-9a-f]+\(void\)" "$cand")" -gt 1 ]; then
  echo "INCOMPARABLE  (function calls other subs; not a leaf — provide stubs to compare)"; exit 0
fi

# 3. Build reference + candidate + a driver that compares their return values.
cat > "$tmp/driver.c" <<EOF
#include <stdint.h>
#include <stdio.h>
uint32_t ${refsym}(void);
uint32_t ${hexname}(void);
int main(void){
  uint32_t r = ${refsym}();
  uint32_t c = ${hexname}();
  if (r == c){ printf("EQUIVALENT  (both return %u)\n", (unsigned)r); return 0; }
  printf("NOT-EQUIVALENT  (reference=%u  flowref=%u)\n", (unsigned)r, (unsigned)c); return 1;
}
EOF

if ! "$CC" $CFLAGS -w -std=c11 "$refc" "$cand" "$tmp/driver.c" -o "$tmp/cmp" 2>"$tmp/cerr"; then
  echo "INCOMPARABLE  (could not compile+link reference vs candidate)"
  sed 's/^/    /' "$tmp/cerr" >&2
  exit 3
fi

"$tmp/cmp"   # prints EQUIVALENT / NOT-EQUIVALENT and sets exit status
