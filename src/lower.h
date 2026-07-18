#ifndef MORDANT_LOWER_H
#define MORDANT_LOWER_H

#include "mordant.h"

typedef enum {
  MOP_LD_ABS,
  MOP_LD_IMM,
  MOP_AND_IMM,
  MOP_JEQ,
  MOP_JGT,
  MOP_JGE,
  MOP_JA,
  MOP_RET,
  MOP_LABEL
} mop_kind;

typedef struct {
  mop_kind op;
  mord_u32 k;
  int label;
  int tlabel;
  int flabel;
} mop;

typedef struct {
  mop *ops;
  size_t n;
  size_t cap;
  int next_label;
} mopbuf;

void mopbuf_init(mopbuf *b);
void mopbuf_free(mopbuf *b);
int mop_new_label(mopbuf *b);
int mop_mark(mopbuf *b, int label);
int mop_emit(mopbuf *b, mop_kind op, mord_u32 k, int label, int tlabel,
             int flabel);

int mord_lower(const mord_policy *p, mopbuf *out, mord_diaglist *diags);
int mord_resolve(const mopbuf *in, mord_program *out, mord_diaglist *diags);

#endif
