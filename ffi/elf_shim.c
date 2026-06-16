/* flowref FFI shim — parse an ELF container via elfutils' libelf/gelf.

   Exposes one primitive to Lean: `lean_elf_dump`, which opens an ELF file and
   returns a newline-separated, TAB-delimited dump that the Lean side parses.
   This reuses a battle-tested ELF parser (elfutils) instead of hand-rolling
   byte-poking in Lean — mirroring the lean-capstone FFI pattern (one C
   primitive, TSV transport, typed wrapper on the Lean side).

   Transport grammar (one record per line, fields TAB-separated):
     H <machine> <is64:0|1> <littleEndian:0|1> <entryHex>
     S <name> <addrHex> <offsetHex> <sizeHex>            (one per section)
     F <name> <valueHex> <sizeHex>                       (one per FUNC symbol)

   `machine` is the raw `e_machine` (EM_*) so the Lean side owns the
   arch-token mapping. Empty string on any open/parse error (Lean treats that
   as "not an ELF / unreadable"). gelf_* normalises ELF32 vs ELF64 and
   endianness, so this one path covers every class/byte-order. */

#include <lean/lean.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include <libelf.h>
#include <gelf.h>

/* A tiny growable char buffer (same shape as the capstone shim's accumulator). */
typedef struct { char *p; size_t len, cap; } buf_t;

static void buf_init(buf_t *b) { b->cap = 8192; b->len = 0; b->p = (char *)malloc(b->cap); b->p[0] = '\0'; }
static void buf_add(buf_t *b, const char *s) {
  size_t m = strlen(s);
  if (b->len + m + 1 > b->cap) { while (b->len + m + 1 > b->cap) b->cap *= 2; b->p = (char *)realloc(b->p, b->cap); }
  memcpy(b->p + b->len, s, m);
  b->len += m;
  b->p[b->len] = '\0';
}

LEAN_EXPORT lean_obj_res lean_elf_dump(b_lean_obj_arg path_obj) {
  const char *path = lean_string_cstr(path_obj);
  buf_t b; buf_init(&b);

  if (elf_version(EV_CURRENT) == EV_NONE) return lean_mk_string("");

  int fd = open(path, O_RDONLY);
  if (fd < 0) { free(b.p); return lean_mk_string(""); }

  Elf *e = elf_begin(fd, ELF_C_READ, NULL);
  if (!e || elf_kind(e) != ELF_K_ELF) {
    if (e) elf_end(e);
    close(fd);
    free(b.p);
    return lean_mk_string("");
  }

  GElf_Ehdr ehdr;
  if (gelf_getehdr(e, &ehdr) == NULL) {
    elf_end(e); close(fd); free(b.p); return lean_mk_string("");
  }
  int cls = gelf_getclass(e);                 /* ELFCLASS32=1, ELFCLASS64=2 */
  int data = ehdr.e_ident[EI_DATA];           /* ELFDATA2LSB=1, ELFDATA2MSB=2 */

  char line[1024];
  snprintf(line, sizeof line, "H\t%u\t%d\t%d\t%llx\n",
           (unsigned)ehdr.e_machine,
           cls == ELFCLASS64 ? 1 : 0,
           data == ELFDATA2LSB ? 1 : 0,
           (unsigned long long)ehdr.e_entry);
  buf_add(&b, line);

  size_t shstrndx = 0;
  elf_getshdrstrndx(e, &shstrndx);

  Elf_Scn *scn = NULL;
  while ((scn = elf_nextscn(e, scn)) != NULL) {
    GElf_Shdr sh;
    if (gelf_getshdr(scn, &sh) != &sh) continue;
    const char *snm = elf_strptr(e, shstrndx, sh.sh_name);
    if (!snm) snm = "";
    snprintf(line, sizeof line, "S\t%s\t%llx\t%llx\t%llx\n",
             snm,
             (unsigned long long)sh.sh_addr,
             (unsigned long long)sh.sh_offset,
             (unsigned long long)sh.sh_size);
    buf_add(&b, line);

    if (sh.sh_type == SHT_SYMTAB || sh.sh_type == SHT_DYNSYM) {
      Elf_Data *d = elf_getdata(scn, NULL);
      if (d && sh.sh_entsize > 0) {
        size_t n = (size_t)(sh.sh_size / sh.sh_entsize);
        for (size_t i = 0; i < n; i++) {
          GElf_Sym sym;
          if (gelf_getsym(d, (int)i, &sym) != &sym) continue;
          if (GELF_ST_TYPE(sym.st_info) != STT_FUNC) continue;
          if (sym.st_value == 0) continue;     /* undefined / imported */
          const char *fnm = elf_strptr(e, sh.sh_link, sym.st_name);
          if (!fnm || fnm[0] == '\0') continue;
          snprintf(line, sizeof line, "F\t%s\t%llx\t%llx\n",
                   fnm,
                   (unsigned long long)sym.st_value,
                   (unsigned long long)sym.st_size);
          buf_add(&b, line);
        }
      }
    }
  }

  elf_end(e);
  close(fd);

  lean_object *s = lean_mk_string(b.p);
  free(b.p);
  return s;
}
