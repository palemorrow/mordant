#include "mordant.h"

#include <stdlib.h>
#include <string.h>

static void put_u16(unsigned char *b, unsigned v) {
  b[0] = (unsigned char)(v & 0xff);
  b[1] = (unsigned char)((v >> 8) & 0xff);
}

static void put_u32(unsigned char *b, mord_u32 v) {
  b[0] = (unsigned char)(v & 0xff);
  b[1] = (unsigned char)((v >> 8) & 0xff);
  b[2] = (unsigned char)((v >> 16) & 0xff);
  b[3] = (unsigned char)((v >> 24) & 0xff);
}

static unsigned get_u16(const unsigned char *b) {
  return (unsigned)b[0] | ((unsigned)b[1] << 8);
}

static mord_u32 get_u32(const unsigned char *b) {
  return (mord_u32)b[0] | ((mord_u32)b[1] << 8) | ((mord_u32)b[2] << 16) |
         ((mord_u32)b[3] << 24);
}

int mord_program_write_file(FILE *f, const mord_program *prog,
                            mord_diaglist *diags) {
  if (prog->count > MORDANT_MAX_INSNS) {
    mord_diag_add(diags, 0, 0, "refusing to write oversized program");
    return -1;
  }
  unsigned char header[16];
  put_u32(header, MORDANT_FILTER_MAGIC);
  put_u32(header + 4, MORDANT_FILTER_VERSION);
  put_u32(header + 8, prog->arch);
  put_u32(header + 12, (mord_u32)prog->count);
  if (fwrite(header, 1, sizeof(header), f) != sizeof(header)) {
    mord_diag_add(diags, 0, 0, "write error");
    return -1;
  }
  for (size_t i = 0; i < prog->count; i++) {
    unsigned char rec[8];
    put_u16(rec, prog->insns[i].code);
    rec[2] = prog->insns[i].jt;
    rec[3] = prog->insns[i].jf;
    put_u32(rec + 4, prog->insns[i].k);
    if (fwrite(rec, 1, sizeof(rec), f) != sizeof(rec)) {
      mord_diag_add(diags, 0, 0, "write error");
      return -1;
    }
  }
  return 0;
}

int mord_program_read_file(FILE *f, mord_program *out, mord_diaglist *diags) {
  out->insns = NULL;
  out->count = 0;
  out->arch = 0;
  unsigned char header[16];
  if (fread(header, 1, sizeof(header), f) != sizeof(header)) {
    mord_diag_add(diags, 0, 0, "short read on filter header");
    return -1;
  }
  if (get_u32(header) != MORDANT_FILTER_MAGIC) {
    mord_diag_add(diags, 0, 0, "bad filter magic");
    return -1;
  }
  if (get_u32(header + 4) != MORDANT_FILTER_VERSION) {
    mord_diag_add(diags, 0, 0, "unsupported filter version %u",
                  get_u32(header + 4));
    return -1;
  }
  mord_u32 count = get_u32(header + 12);
  if (count == 0 || count > MORDANT_MAX_INSNS) {
    mord_diag_add(diags, 0, 0, "filter instruction count %u out of range",
                  count);
    return -1;
  }
  mord_insn *insns = calloc(count, sizeof(*insns));
  if (!insns) {
    mord_diag_add(diags, 0, 0, "out of memory reading filter");
    return -1;
  }
  for (mord_u32 i = 0; i < count; i++) {
    unsigned char rec[8];
    if (fread(rec, 1, sizeof(rec), f) != sizeof(rec)) {
      free(insns);
      mord_diag_add(diags, 0, 0, "short read on filter body");
      return -1;
    }
    insns[i].code = (uint16_t)get_u16(rec);
    insns[i].jt = rec[2];
    insns[i].jf = rec[3];
    insns[i].k = get_u32(rec + 4);
  }
  out->insns = insns;
  out->count = count;
  out->arch = get_u32(header + 8);
  return 0;
}

int mord_program_write(const mord_program *prog, const char *path,
                       mord_diaglist *diags) {
  FILE *f = fopen(path, "wb");
  if (!f) {
    mord_diag_add(diags, 0, 0, "cannot open '%s' for writing", path);
    return -1;
  }
  int rc = mord_program_write_file(f, prog, diags);
  if (fclose(f) != 0 && rc == 0) {
    mord_diag_add(diags, 0, 0, "error closing '%s'", path);
    rc = -1;
  }
  return rc;
}

int mord_program_read(const char *path, mord_program *out,
                      mord_diaglist *diags) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    mord_diag_add(diags, 0, 0, "cannot open '%s'", path);
    return -1;
  }
  int rc = mord_program_read_file(f, out, diags);
  fclose(f);
  return rc;
}
