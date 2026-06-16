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

echo "== 6b. calling-convention parameter model (SysV x86-64 + cdecl x86-32) =="
pout="$("$BIN" --demo-params)"
echo "$pout"
echo "$pout" | grep -q "uint32_t sub_401000(uint32_t a0, uint32_t a1)" \
  || fail "SysV x86-64 demo should recover a 2-parameter signature"
echo "$pout" | grep -q "uint32_t sub_401100(uint32_t a0)" \
  || fail "cdecl x86-32 demo should recover a 1-parameter signature"
pass "recovered 2-param SysV + 1-param cdecl signatures"
# the emitted C (both functions) must compile.
"$BIN" --demo-params --emit-c | "$GCC" -xc -std=c11 -w -fsyntax-only - \
  || fail "parameter-model demo C does not compile (-fsyntax-only)"
# and the body must actually bind the incoming arg to the parameter name.
"$BIN" --demo-params --emit-c | grep -q "eax_0 = (uint32_t)(a0)" \
  || fail "parameter binding (a0) not threaded into the SSA body"
pass "parameter-model C compiles and binds args to a0/a1"

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

echo "== 13. ETNF Parquet(zstd) normaliser (lean-duckdb) =="
DUCKLIB=".lake/packages/lean_duckdb/vendor/libduckdb.so"
if [ -f "$DUCKLIB" ]; then
  lake build flowref-etnf || fail "flowref-etnf build"
  ETOUT="$(mktemp -d /tmp/flowref-etnf.XXXXXX)"
  ./.lake/build/bin/flowref-etnf decompile-bench/fixture.ndjson "$ETOUT" | tee "$ETOUT/log"
  grep -q "lossless-join verified" "$ETOUT/log" || { rm -rf "$ETOUT"; fail "ETNF lossless verification"; }
  for rel in etnf_file etnf_source etnf_asm etnf_function; do
    test -f "$ETOUT/$rel.parquet" || { rm -rf "$ETOUT"; fail "missing $rel.parquet"; }
  done
  rm -rf "$ETOUT"
  pass "ETNF relations written + lossless-join verified"
else
  echo "skip: libduckdb not vendored ($DUCKLIB) — run 'lake update lean_duckdb'"
fi

echo "== 14. ELF resolution (self-contained FFI): list + symbol/address short forms =="
# The flowref binary is itself an ELF — use it as a self-contained fixture.
SELF="$BIN"
# 14a. list detects arch and finds FUNC symbols.
"$BIN" list "$SELF" > /tmp/flowref-list.$$ 2>&1 || fail "list exited non-zero"
grep -qE "arch=x(86-)?64|arch=x64" /tmp/flowref-list.$$ || fail "list did not auto-detect x64"
grep -q "_start" /tmp/flowref-list.$$ || fail "list did not find _start symbol"
pass "list: ELF parsed, arch auto-detected, symbols enumerated"
# 14b. decompile by symbol name resolves region from headers and emits C.
"$BIN" decompile "$SELF" _start 2>/dev/null | grep -q "sub_" || fail "decompile by symbol produced no C function"
pass "decompile <bin> _start (symbol → region via ELF headers)"
# 14c. decompile by address resolves the same region (and back-maps to symbol).
"$BIN" decompile "$SELF" _start 2>&1 >/dev/null | grep -q "resolved (_start)" || fail "address/symbol resolution note missing"
pass "resolution note reports symbol + derived region"
# 14d. clean errors: non-ELF and unknown symbol exit non-zero with a message.
if "$BIN" list run-tests.sh 2>/dev/null; then fail "expected non-ELF rejection"; fi
pass "rejected: non-ELF file"
if "$BIN" decompile "$SELF" no_such_symbol_xyz 2>/dev/null; then fail "expected unknown-symbol rejection"; fi
pass "rejected: unknown symbol"
rm -f /tmp/flowref-list.$$

echo "== 15. --json machine-readable output (valid JSON, C round-trips) =="
if command -v python3 >/dev/null 2>&1; then
  "$BIN" list "$SELF" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert d["arch"], "arch"; assert d["functionCount"]>0, "funcs"; assert d["functions"][0]["name"]' \
    || fail "list --json invalid or missing fields"
  pass "list --json is valid JSON with arch + functions"
  "$BIN" decompile "$SELF" _start --json 2>/dev/null | python3 -c '
import json,sys,subprocess
d=json.load(sys.stdin)
assert d["signature"].startswith("uint32_t sub_"), "signature"
open("/tmp/fr-json.c","w").write(d["c"])
subprocess.run(["gcc","-xc","-std=c11","-w","-fsyntax-only","/tmp/fr-json.c"],check=True)' \
    || fail "decompile --json invalid, or embedded C does not compile"
  pass "decompile --json valid; embedded C compiles (gcc -fsyntax-only)"
  rm -f /tmp/fr-json.c
  "$BIN" xref "$SELF" _start 0x1 --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert "insns" in d and "witnesses" in d and "found" in d' \
    || fail "xref --json invalid or missing fields"
  pass "xref --json is valid JSON with insns/witnesses/found"
else
  echo "skip: python3 not available for JSON validation"
fi

echo "== 16. ELF byte-swap path + non-ELF container messaging =="
if command -v python3 >/dev/null 2>&1; then
  # Generate a minimal big-endian (PPC64) ELF and its little-endian (x86-64) twin,
  # each with one FUNC symbol myfunc @ 0x1000 size 0x20. The shim must recover the
  # SAME vaddr/size from both — that exercises the rd16/rd32/rd64 byte-swap.
  GEN="$(mktemp /tmp/flowref-mkelf.XXXXXX.py)"
  cat > "$GEN" <<'PY'
import struct, sys
def build(endian, machine):
    E=endian
    shstr=b'\0.text\0.symtab\0.strtab\0.shstrtab\0'
    soff=lambda n: shstr.index(b'\0'+n+b'\0')+1
    strtab=b'\0myfunc\0'
    symtab=struct.pack(E+'IBBHQQ',0,0,0,0,0,0)+struct.pack(E+'IBBHQQ',1,(1<<4)|2,0,1,0x1000,0x20)
    EHSZ=64; SHSZ=64; nsh=5; sh_off=EHSZ
    text_off=sh_off+nsh*SHSZ; symtab_off=text_off; strtab_off=symtab_off+len(symtab); shstr_off=strtab_off+len(strtab)
    sh=lambda name,typ,addr,off,size,link=0,ent=0: struct.pack(E+'IIQQQQIIQQ',name,typ,0,addr,off,size,link,0,1,ent)
    shdrs=sh(0,0,0,0,0)+sh(soff(b'.text'),1,0x1000,text_off,0)+sh(soff(b'.symtab'),2,0,symtab_off,len(symtab),3,24)+sh(soff(b'.strtab'),3,0,strtab_off,len(strtab))+sh(soff(b'.shstrtab'),3,0,shstr_off,len(shstr))
    ei=bytes([0x7f,69,76,70,2,(2 if endian=='>' else 1),1,0,0,0,0,0,0,0,0,0])
    eh=ei+struct.pack(E+'HHIQQQIHHHHHH',2,machine,1,0x1000,0,sh_off,0,EHSZ,0,0,SHSZ,nsh,4)
    return eh+shdrs+symtab+strtab+shstr
open(sys.argv[3],'wb').write(build('>' if sys.argv[1]=='be' else '<', int(sys.argv[2])))
PY
  BE="$(mktemp /tmp/flowref-be.XXXXXX)"; LE="$(mktemp /tmp/flowref-le.XXXXXX)"
  python3 "$GEN" be 21 "$BE"; python3 "$GEN" le 62 "$LE"
  "$BIN" list "$BE" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert d["endian"]=="BE" and d["arch"]=="ppc64", d; f=d["functions"][0]; assert f["name"]=="myfunc" and f["vaddr"]==0x1000 and f["size"]==0x20, f' \
    || { rm -f "$GEN" "$BE" "$LE"; fail "big-endian ELF parse (byte-swap) wrong"; }
  pass "big-endian ELF parsed correctly (byte-swap: ppc64 BE, myfunc @0x1000)"
  "$BIN" list "$LE" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); f=d["functions"][0]; assert d["endian"]=="LE" and f["vaddr"]==0x1000 and f["size"]==0x20, d' \
    || { rm -f "$GEN" "$BE" "$LE"; fail "little-endian twin parse wrong"; }
  pass "little-endian twin recovers identical vaddr/size (no-swap path)"
  rm -f "$GEN" "$BE" "$LE"
else
  echo "skip: python3 not available for ELF fixture generation"
fi
# Non-ELF containers get a kind-specific message (PE / Mach-O / archive).
# `list` exits non-zero here, so capture with `|| true` (set -o pipefail).
printf 'MZ\x90\x00' > /tmp/flowref-pe.$$
PEMSG="$("$BIN" list /tmp/flowref-pe.$$ 2>&1 || true)"
rm -f /tmp/flowref-pe.$$
case "$PEMSG" in
  *PE/COFF*) pass "non-ELF container identified by kind (PE/COFF) in the error" ;;
  *) fail "PE not identified in message: $PEMSG" ;;
esac

echo "== 17. PPC64 ELFv1 TOC resolution (r2 from .opd, ld off(r2) deref) =="
if command -v python3 >/dev/null 2>&1; then
  # Build a tiny big-endian PPC64 ELFv1 fixture exercising the TOC path:
  #   .text  @0x1000 : a single `ld r3, DS(r2)` whose effective address (r2+DS)
  #                    lands on a .toc1 pointer cell.
  #   .toc1  @0x4000 : an 8-byte BE pointer cell holding the TARGET (0x10005000).
  #   .opd   @0x5000 : one ELFv1 descriptor (entry, toc_base, env); toc_base is r2.
  #   .rodata@0x10005000 : the referenced datum (a string).
  # The recovered r2 must equal the .opd toc_base, and `xref` must report the
  # `ld` site as resolving to the target through the .toc1 cell.
  GEN="$(mktemp /tmp/flowref-toc.XXXXXX.py)"
  cat > "$GEN" <<'PY'
import struct,sys
E='>'  # big-endian PPC64 ELFv1
R2=0x4000             # module TOC base (points into .toc1)
TGT=0x10005000        # the referenced datum (a .rodata string)
TOC1=0x4000           # .toc1 cell vaddr (== r2 here, so DS=0)
DS=(TOC1-R2)          # 0
# .text: ld r3, DS(r2)  -> opcode 58, rD=3, rA=2, DS-form (low 2 bits xo=0)
ld=(58<<26)|(3<<21)|(2<<16)|(DS&0xfffc)
text=struct.pack(E+'I',ld)+struct.pack(E+'I',0x4e800020)  # + blr
# .toc1: 8-byte BE pointer to TGT
toc1=struct.pack(E+'Q',TGT)
# .opd: one descriptor (entry=0x1000, toc=R2, env=0)
opd=struct.pack(E+'QQQ',0x1000,R2,0)
# .rodata
rod=b'FpAnimClip.cpp\x00'
shstr=b'\0.text\0.toc1\0.opd\0.rodata\0.shstrtab\0'
def soff(n): return shstr.index(b'\0'+n+b'\0')+1
EHSZ=64;SHSZ=64;nsh=6;sh_off=EHSZ
# section file offsets laid out after the section header table
base=sh_off+nsh*SHSZ
text_off=base; toc1_off=text_off+len(text); opd_off=toc1_off+len(toc1)
rod_off=opd_off+len(opd); shstr_off=rod_off+len(rod)
def sh(name,typ,addr,off,size,ent=0):
    return struct.pack(E+'IIQQQQIIQQ',name,typ,0,addr,off,size,0,0,1,ent)
shdrs=(sh(0,0,0,0,0)
  +sh(soff(b'.text'),1,0x1000,text_off,len(text))
  +sh(soff(b'.toc1'),1,TOC1,toc1_off,len(toc1))
  +sh(soff(b'.opd'),1,0x5000,opd_off,len(opd))
  +sh(soff(b'.rodata'),1,TGT,rod_off,len(rod))
  +sh(soff(b'.shstrtab'),3,0,shstr_off,len(shstr)))
ei=bytes([0x7f,69,76,70,2,2,1,0,0,0,0,0,0,0,0,0])  # ELF64 BE
eh=ei+struct.pack(E+'HHIQQQIHHHHHH',2,21,1,0x1000,0,sh_off,0,EHSZ,0,0,SHSZ,nsh,5)
open(sys.argv[1],'wb').write(eh+shdrs+text+toc1+opd+rod+shstr)
PY
  TOCELF="$(mktemp /tmp/flowref-tocelf.XXXXXX)"
  python3 "$GEN" "$TOCELF"
  # r2 recovery + TOC deref reaching the target string at 0x10005000.
  TOCOUT="$("$BIN" xref "$TOCELF" 0x1000 0x10005000 2>&1 || true)"
  echo "$TOCOUT" | grep -q "recovered r2/TOC base = 0x4000" \
    || { rm -f "$GEN" "$TOCELF"; fail "TOC r2 recovery wrong: $TOCOUT"; }
  pass "TOC base r2=0x4000 recovered from .opd (not hardcoded .toc+0x8000)"
  echo "$TOCOUT" | grep -q "0x1000:.*ld.*(r2).*→ 0x10005000" \
    || { rm -f "$GEN" "$TOCELF"; fail "TOC ld(r2) did not resolve to target: $TOCOUT"; }
  pass "ld off(r2) resolved through .toc1 cell to target 0x10005000"
  rm -f "$GEN" "$TOCELF"
else
  echo "skip: python3 not available for TOC fixture generation"
fi

echo
echo "ALL TESTS PASSED"
