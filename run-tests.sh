#!/usr/bin/env bash
# flowref test runner — builds and exercises the disassembler + control-flow xref
# + the plausible iterative-deepening witness DAG. Exits non-zero on ANY failure.
set -euo pipefail

cd "$(dirname "$0")"

# Make the Lean toolchain visible if Homebrew installed it.
if [ -d /home/linuxbrew/.linuxbrew/bin ]; then
  export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
fi

BIN=".lake/build/bin/flowref"
fail() { echo "FAIL: $*" >&2; exit 1; }
pass() { echo "ok: $*"; }

echo "== 1. lake build =="
lake build || fail "lake build failed"
pass "build clean"

echo "== 2. --version / --help =="
"$BIN" --version | grep -q "flowref" || fail "--version"
"$BIN" --help    | grep -q "USAGE"  || fail "--help"
pass "version/help"

echo "== 3. iterative-deepening witness DAG (demo deep) =="
out="$("$BIN" demo deep)"
echo "$out"
echo "$out" | grep -q "L0 (walkSteps=64.*UNRESOLVED" || fail "L0 should be unresolved"
echo "$out" | grep -q "L1 (walkSteps=512.*RESOLVED"   || fail "L1 should resolve"
pass "shallow L0 unresolved; deepened L1 resolves (witness DAG escalation)"

echo "== 4. error handling: unreadable file exits non-zero =="
if "$BIN" xref /nonexistent-file x86 0x1 0x1 0x1 0x4 2>/dev/null; then
  fail "expected non-zero exit on missing file"
fi
pass "missing file yields non-zero exit"

echo "== 5. input validation: malformed args rejected (untrusted boundary) =="
PROBE="$(mktemp /tmp/flowref-probe.XXXXXX)"
head -c 64 /dev/zero > "$PROBE" 2>/dev/null || printf '%64s' '' > "$PROBE"
reject() { local desc="$1"; shift
  if "$BIN" xref "$PROBE" "$@" 2>/dev/null; then rm -f "$PROBE"; fail "expected rejection: $desc"; fi
  pass "rejected: $desc"; }
reject "unsupported arch"        nonsensearch 0x0 0x0 0x0 0x10
reject "non-hex target"          x86 0xZZ 0x0 0x0 0x10
reject "non-hex fileOff"         x86 0x0  0xGG 0x0 0x10
reject "zero-length region"      x86 0x0  0x0 0x0 0x0
reject "region past end of file" x86 0x0  0x0 0x0 0xFFFF
reject "offset past end of file" x86 0x0  0x999 0x0 0x10
rm -f "$PROBE"

echo "== 6. multi-arch decode (ports/adapters: every Capstone target wired) =="
# aarch64 `mov w0,#7; ret` decodes to 2 insns; riscv64 is also wired.
A64="$(mktemp /tmp/flowref-a64.XXXXXX)"; printf '\xe0\x00\x80\x52\xc0\x03\x5f\xd6' > "$A64"
"$BIN" xref "$A64" arm64   0x0 0x0 0x0 0x8 2>/dev/null | grep -q "insns=2"  || { rm -f "$A64"; fail "aarch64 decode"; }
"$BIN" xref "$A64" riscv64 0x0 0x0 0x0 0x8 2>/dev/null | grep -q "^insns=" || { rm -f "$A64"; fail "riscv64 not wired"; }
rm -f "$A64"
# x64 REX.W mov decodes (a 32-bit reader would mis-split these 8 bytes).
REX="$(mktemp /tmp/flowref-rex.XXXXXX)"; printf '\x48\xc7\xc0\x07\x00\x00\x00\xc3' > "$REX"
"$BIN" xref "$REX" x64 0x0 0x0 0x0 0x8 2>/dev/null | grep -q "insns=2" || { rm -f "$REX"; fail "x64 REX.W decode"; }
rm -f "$REX"
pass "arm64 / riscv64 / x64 decode through the Capstone adapter"

echo "== 7. ELF resolution (self-contained <elf.h> FFI): list + symbol xref =="
SELF="$BIN"
"$BIN" list "$SELF" > /tmp/flowref-list.$$ 2>&1 || fail "list exited non-zero"
grep -qE "arch=x(86-)?64|arch=x64" /tmp/flowref-list.$$ || fail "list did not auto-detect x64"
grep -q "_start" /tmp/flowref-list.$$ || fail "list did not find _start symbol"
pass "list: ELF parsed, arch auto-detected, symbols enumerated"
# xref by symbol resolves the region from the headers (note on stderr).
"$BIN" xref "$SELF" _start 0x1 2>&1 >/dev/null | grep -q "resolved region (_start)" \
  || fail "symbol→region resolution note missing"
pass "xref <bin> _start <target>: region resolved from ELF headers"
# clean errors: non-ELF and unknown symbol exit non-zero with a message.
if "$BIN" list run-tests.sh 2>/dev/null; then fail "expected non-ELF rejection"; fi
pass "rejected: non-ELF file"
if "$BIN" xref "$SELF" no_such_symbol_xyz 0x1 2>/dev/null; then fail "expected unknown-symbol rejection"; fi
pass "rejected: unknown symbol"
rm -f /tmp/flowref-list.$$

echo "== 8. --json machine-readable output (list / xref) =="
if command -v python3 >/dev/null 2>&1; then
  "$BIN" list "$SELF" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert d["arch"] and d["functionCount"]>0 and d["functions"][0]["name"]' \
    || fail "list --json invalid or missing fields"
  pass "list --json is valid JSON with arch + functions"
  "$BIN" xref "$SELF" _start 0x1 --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert "insns" in d and "witnesses" in d and "found" in d' \
    || fail "xref --json invalid or missing fields"
  pass "xref --json is valid JSON with insns/witnesses/found"
else
  echo "skip: python3 not available for JSON validation"
fi

echo "== 9. ELF byte-swap path + non-ELF container messaging =="
if command -v python3 >/dev/null 2>&1; then
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
  "$BIN" list "$BE" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); assert d["endian"]=="BE" and d["arch"]=="ppc64"; f=d["functions"][0]; assert f["name"]=="myfunc" and f["vaddr"]==0x1000 and f["size"]==0x20' \
    || { rm -f "$GEN" "$BE" "$LE"; fail "big-endian ELF parse (byte-swap) wrong"; }
  pass "big-endian ELF parsed correctly (byte-swap: ppc64 BE, myfunc @0x1000)"
  "$BIN" list "$LE" --json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); f=d["functions"][0]; assert d["endian"]=="LE" and f["vaddr"]==0x1000 and f["size"]==0x20' \
    || { rm -f "$GEN" "$BE" "$LE"; fail "little-endian twin parse wrong"; }
  pass "little-endian twin recovers identical vaddr/size (no-swap path)"
  rm -f "$GEN" "$BE" "$LE"
else
  echo "skip: python3 not available for ELF fixture generation"
fi
printf 'MZ\x90\x00' > /tmp/flowref-pe.$$
PEMSG="$("$BIN" list /tmp/flowref-pe.$$ 2>&1 || true)"
rm -f /tmp/flowref-pe.$$
case "$PEMSG" in
  *PE/COFF*) pass "non-ELF container identified by kind (PE/COFF) in the error" ;;
  *) fail "PE not identified in message: $PEMSG" ;;
esac

echo "== 10. PPC64 ELFv1 TOC resolution (r2 from .opd, ld off(r2) → target) =="
if command -v python3 >/dev/null 2>&1; then
  GEN="$(mktemp /tmp/flowref-toc.XXXXXX.py)"
  cat > "$GEN" <<'PY'
import struct,sys
E='>'; R2=0x4000; TGT=0x10005000; TOC1=0x4000; DS=(TOC1-R2)
ld=(58<<26)|(3<<21)|(2<<16)|(DS&0xfffc)
text=struct.pack(E+'I',ld)+struct.pack(E+'I',0x4e800020)
toc1=struct.pack(E+'Q',TGT); opd=struct.pack(E+'QQQ',0x1000,R2,0); rod=b'FpAnimClip.cpp\x00'
shstr=b'\0.text\0.toc1\0.opd\0.rodata\0.shstrtab\0'
def soff(n): return shstr.index(b'\0'+n+b'\0')+1
EHSZ=64;SHSZ=64;nsh=6;sh_off=EHSZ; base=sh_off+nsh*SHSZ
text_off=base; toc1_off=text_off+len(text); opd_off=toc1_off+len(toc1); rod_off=opd_off+len(opd); shstr_off=rod_off+len(rod)
def sh(name,typ,addr,off,size,ent=0): return struct.pack(E+'IIQQQQIIQQ',name,typ,0,addr,off,size,0,0,1,ent)
shdrs=(sh(0,0,0,0,0)+sh(soff(b'.text'),1,0x1000,text_off,len(text))+sh(soff(b'.toc1'),1,TOC1,toc1_off,len(toc1))
  +sh(soff(b'.opd'),1,0x5000,opd_off,len(opd))+sh(soff(b'.rodata'),1,TGT,rod_off,len(rod))+sh(soff(b'.shstrtab'),3,0,shstr_off,len(shstr)))
ei=bytes([0x7f,69,76,70,2,2,1,0,0,0,0,0,0,0,0,0])
eh=ei+struct.pack(E+'HHIQQQIHHHHHH',2,21,1,0x1000,0,sh_off,0,EHSZ,0,0,SHSZ,nsh,5)
open(sys.argv[1],'wb').write(eh+shdrs+text+toc1+opd+rod+shstr)
PY
  TOCELF="$(mktemp /tmp/flowref-tocelf.XXXXXX)"
  python3 "$GEN" "$TOCELF"
  TOCOUT="$("$BIN" xref "$TOCELF" 0x1000 0x10005000 2>&1 || true)"
  echo "$TOCOUT" | grep -q "recovered r2/TOC base = 0x4000" || { rm -f "$GEN" "$TOCELF"; fail "TOC r2 recovery wrong: $TOCOUT"; }
  pass "TOC base r2=0x4000 recovered from .opd (not hardcoded .toc+0x8000)"
  echo "$TOCOUT" | grep -q "0x1000:.*ld.*(r2).*→ 0x10005000" || { rm -f "$GEN" "$TOCELF"; fail "TOC ld(r2) did not resolve to target: $TOCOUT"; }
  pass "ld off(r2) resolved through .toc1 cell to target 0x10005000"
  rm -f "$GEN" "$TOCELF"
else
  echo "skip: python3 not available for TOC fixture generation"
fi

echo
echo "ALL TESTS PASSED"
