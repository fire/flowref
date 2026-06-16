#!/usr/bin/env bash
# flowref test runner — builds, runs the demos, and verifies the emitted C
# compiles with gcc. Exits non-zero on ANY failure.
set -euo pipefail

cd "$(dirname "$0")"

# Make the Lean toolchain visible if Homebrew installed it.
if [ -d /home/linuxbrew/.linuxbrew/bin ]; then
  export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
fi

GCC="${GCC:-gcc}"
BIN=".lake/build/bin/flowref"
fail() { echo "FAIL: $*" >&2; exit 1; }
pass() { echo "ok: $*"; }

echo "== 1. lake build =="
lake build || fail "lake build failed"
pass "build clean"

echo "== 2. --version / --help =="
"$BIN" --version    | grep -q "flowref" || fail "--version"
"$BIN" --help       | grep -q "USAGE"  || fail "--help"
pass "version/help"

echo "== 3. --demo runs =="
"$BIN" --demo > /dev/null || fail "--demo crashed"
pass "demo runs"

echo "== 4. --demo --emit-c compiles with gcc -fsyntax-only =="
"$BIN" --demo --emit-c | "$GCC" -xc -std=c11 -w -fsyntax-only - \
  || fail "demo C does not compile"
pass "demo C compiles (-fsyntax-only)"

echo "== 5. --demo --emit-c compiles to an object (gcc -c) =="
tmpc="$(mktemp /tmp/flowref-demo.XXXXXX.c)"
tmpo="$(mktemp /tmp/flowref-demo.XXXXXX.o)"
"$BIN" --demo --emit-c > "$tmpc"
"$GCC" -xc -std=c11 -w -c "$tmpc" -o "$tmpo" || fail "demo C does not compile to .o"
rm -f "$tmpc" "$tmpo"
pass "demo C compiles to object"

echo "== 6. iterative-deepening escalation demonstrated =="
out="$("$BIN" --demo-deep)"
echo "$out"
echo "$out" | grep -q "L0 (walkSteps=64.*UNRESOLVED" || fail "L0 should be unresolved"
echo "$out" | grep -q "L1 (walkSteps=512.*RESOLVED"   || fail "L1 should resolve"
pass "shallow L0 unresolved; deepened L1 resolves"

echo "== 7. real-function decompile compiles (if test binary present) =="
REALBIN="${FLOWREF_REALBIN:-/tmp/hdkout/app/dev/bin/HUBAtgiToAnim.exe}"
if [ -f "$REALBIN" ]; then
  "$BIN" decompile "$REALBIN" x86 0x401010 0x1010 0x401010 0x2c 2>/dev/null \
    | "$GCC" -xc -std=c11 -w -fsyntax-only - || fail "real-function C does not compile"
  pass "real-function C compiles (-fsyntax-only)"
else
  echo "skip: real test binary not present ($REALBIN)"
fi

echo "== 8. error handling: unreadable file exits non-zero =="
if "$BIN" decompile /nonexistent-file x86 0x1 0x1 0x1 0x1 2>/dev/null; then
  fail "expected non-zero exit on missing file"
fi
pass "missing file yields non-zero exit"

echo "== 9. input validation: malformed args rejected (untrusted boundary) =="
# A real, readable file so we reach the field-validation logic, not the open error.
PROBE="$(mktemp /tmp/flowref-probe.XXXXXX)"
head -c 64 /dev/zero > "$PROBE" 2>/dev/null || printf '%64s' '' > "$PROBE"
reject() { # description, then the args to decompile
  local desc="$1"; shift
  if "$BIN" decompile "$PROBE" "$@" 2>/dev/null; then
    rm -f "$PROBE"; fail "expected rejection: $desc"
  fi
  pass "rejected: $desc"
}
reject "unsupported arch"        nonsensearch 0x0 0x0 0x0 0x10
reject "non-hex fnVaddr"         x86 0xZZ 0x0 0x0 0x10
reject "non-hex fileOff"         x86 0x0  0xGG 0x0 0x10
reject "zero-length region"      x86 0x0  0x0 0x0 0x0
reject "region past end of file" x86 0x0  0x0 0x0 0xFFFF
reject "offset past end of file" x86 0x0  0x999 0x0 0x10
# xref target is also validated.
if "$BIN" xref "$PROBE" x86 0xGG 0x0 0x0 0x4 2>/dev/null; then
  rm -f "$PROBE"; fail "expected rejection: non-hex xref target"
fi
pass "rejected: non-hex xref target"
rm -f "$PROBE"

echo "== 10. multi-arch decode (ports/adapters: every Capstone target wired) =="
# aarch64 `mov w0,#7; ret` and arm `mov r0,#7; bx lr` must both decode to 2 insns.
A64="$(mktemp /tmp/flowref-a64.XXXXXX)"; printf '\xe0\x00\x80\x52\xc0\x03\x5f\xd6' > "$A64"
"$BIN" xref "$A64" arm64 0x0 0x0 0x0 0x8 2>/dev/null | grep -q "insns=2" || { rm -f "$A64"; fail "aarch64 decode"; }
"$BIN" xref "$A64" riscv64 0x0 0x0 0x0 0x8 2>/dev/null | grep -q "^insns=" || { rm -f "$A64"; fail "riscv64 arch not wired"; }
rm -f "$A64"
# x64 must decode a REX.W mov that x86 (32-bit) would misread.
REX="$(mktemp /tmp/flowref-rex.XXXXXX)"; printf '\x48\xc7\xc0\x07\x00\x00\x00\xc3' > "$REX"
"$BIN" decompile "$REX" x64 0x0 0x0 0x0 0x8 2>/dev/null | grep -q "rax_0 = (uint64_t)(7)" || { rm -f "$REX"; fail "x64 REX.W decode"; }
rm -f "$REX"
pass "arm64 / riscv64 / x64 decode through the Capstone adapter"

echo "== 11. asm-text decoder path emits compilable C =="
LST="$(mktemp /tmp/flowref-lst.XXXXXX.asm)"
cat > "$LST" <<'ASM'
0000000000401000 <foo>:
  401000:	b8 00 00 00 00       	mov    eax,0x0
  401005:	bb 0a 00 00 00       	mov    ebx,0xa
  40100a:	39 d8                	cmp    eax,ebx
  40100c:	7d 03                	jge    0x401011
  40100e:	83 c0 01             	add    eax,0x1
  401011:	c3                   	ret
ASM
"$BIN" decompile-asm "$LST" x86 0x401000 | "$GCC" -xc -std=c11 -w -fsyntax-only - \
  || { rm -f "$LST"; fail "asm-text C does not compile"; }
rm -f "$LST"
pass "objdump-style asm listing → compilable C"

echo "== 12. Decompile-Bench equivalence oracle (return-SSA wiring) =="
if "$GCC" -O1 -fcf-protection=none -c -xc /dev/null -o /tmp/flowref-cc-probe.o 2>/dev/null; then
  rm -f /tmp/flowref-cc-probe.o
  ./decompile-bench/equiv-demo.sh | tee /tmp/flowref-equiv.out
  grep -q "RESULT: 4/4 proven" /tmp/flowref-equiv.out || fail "equivalence demo regressed"
  rm -f /tmp/flowref-equiv.out
  pass "flowref C proven functionally equivalent to source (4/4 leaf functions)"
else
  echo "skip: C compiler cannot build the equivalence demo"
fi

echo
echo "ALL TESTS PASSED"
