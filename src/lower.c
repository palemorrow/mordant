#include "lower.h"
#include "private.h"

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

void mopbuf_init(mopbuf *b) {
  b->ops = NULL;
  b->n = 0;
  b->cap = 0;
  b->next_label = 0;
}

void mopbuf_free(mopbuf *b) {
  free(b->ops);
  b->ops = NULL;
  b->n = 0;
  b->cap = 0;
}

int mop_new_label(mopbuf *b) { return b->next_label++; }

int mop_emit(mopbuf *b, mop_kind op, mord_u32 k, int label, int tlabel,
             int flabel) {
  if (b->n == b->cap) {
    size_t cap = b->cap ? b->cap * 2 : 32;
    mop *ops = realloc(b->ops, cap * sizeof(*ops));
    if (!ops)
      return -1;
    b->ops = ops;
    b->cap = cap;
  }
  mop *m = &b->ops[b->n++];
  m->op = op;
  m->k = k;
  m->label = label;
  m->tlabel = tlabel;
  m->flabel = flabel;
  return 0;
}

int mop_mark(mopbuf *b, int label) {
  return mop_emit(b, MOP_LABEL, 0, label, -1, -1);
}

static mord_u32 arg_lo(unsigned arg) {
  return (mord_u32)(offsetof(struct seccomp_data, args) + 8u * arg);
}

static mord_u32 arg_hi(unsigned arg) {
  return (mord_u32)(offsetof(struct seccomp_data, args) + 8u * arg + 4u);
}

static int emit_eq(mopbuf *b, unsigned arg, mord_u64 value, int t, int f) {
  mord_u32 c_hi = (mord_u32)(value >> 32);
  mord_u32 c_lo = (mord_u32)value;
  int nxt = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_hi(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_hi, -1, nxt, f) != 0)
    return -1;
  if (mop_mark(b, nxt) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_lo(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_lo, -1, t, f) != 0)
    return -1;
  return 0;
}

static int emit_lt(mopbuf *b, unsigned arg, mord_u64 value, int t, int f) {
  mord_u32 c_hi = (mord_u32)(value >> 32);
  mord_u32 c_lo = (mord_u32)value;
  int nxt = mop_new_label(b);
  int low = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_hi(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_hi, -1, f, nxt) != 0)
    return -1;
  if (mop_mark(b, nxt) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_hi, -1, low, t) != 0)
    return -1;
  if (mop_mark(b, low) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_lo(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGE, c_lo, -1, f, t) != 0)
    return -1;
  return 0;
}

static int emit_le(mopbuf *b, unsigned arg, mord_u64 value, int t, int f) {
  mord_u32 c_hi = (mord_u32)(value >> 32);
  mord_u32 c_lo = (mord_u32)value;
  int nxt = mop_new_label(b);
  int low = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_hi(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_hi, -1, f, nxt) != 0)
    return -1;
  if (mop_mark(b, nxt) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_hi, -1, low, t) != 0)
    return -1;
  if (mop_mark(b, low) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_lo(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_lo, -1, f, t) != 0)
    return -1;
  return 0;
}

static int emit_gt(mopbuf *b, unsigned arg, mord_u64 value, int t, int f) {
  mord_u32 c_hi = (mord_u32)(value >> 32);
  mord_u32 c_lo = (mord_u32)value;
  int nxt = mop_new_label(b);
  int low = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_hi(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_hi, -1, t, nxt) != 0)
    return -1;
  if (mop_mark(b, nxt) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_hi, -1, low, f) != 0)
    return -1;
  if (mop_mark(b, low) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_lo(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_lo, -1, t, f) != 0)
    return -1;
  return 0;
}

static int emit_ge(mopbuf *b, unsigned arg, mord_u64 value, int t, int f) {
  mord_u32 c_hi = (mord_u32)(value >> 32);
  mord_u32 c_lo = (mord_u32)value;
  int nxt = mop_new_label(b);
  int low = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_hi(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGT, c_hi, -1, t, nxt) != 0)
    return -1;
  if (mop_mark(b, nxt) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, c_hi, -1, low, f) != 0)
    return -1;
  if (mop_mark(b, low) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_lo(arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JGE, c_lo, -1, t, f) != 0)
    return -1;
  return 0;
}

static int emit_mask(mopbuf *b, const mord_pred *p, int t, int f) {
  mord_u32 m_hi = (mord_u32)(p->mask >> 32);
  mord_u32 m_lo = (mord_u32)p->mask;
  mord_u32 v_hi = (mord_u32)(p->value >> 32);
  mord_u32 v_lo = (mord_u32)p->value;
  int hi = mop_new_label(b);
  if (mop_emit(b, MOP_LD_ABS, arg_lo(p->arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_AND_IMM, m_lo, -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, v_lo, -1, hi, f) != 0)
    return -1;
  if (mop_mark(b, hi) != 0)
    return -1;
  if (mop_emit(b, MOP_LD_ABS, arg_hi(p->arg), -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_AND_IMM, m_hi, -1, -1, -1) != 0)
    return -1;
  if (mop_emit(b, MOP_JEQ, v_hi, -1, t, f) != 0)
    return -1;
  return 0;
}

static int emit_pred(mopbuf *b, const mord_pred *p, int t, int f) {
  if (!p || p->kind == MORD_P_TRUE)
    return mop_emit(b, MOP_JA, 0, t, -1, -1);
  switch (p->kind) {
  case MORD_P_EQ:
    return emit_eq(b, p->arg, p->value, t, f);
  case MORD_P_NE:
    return emit_eq(b, p->arg, p->value, f, t);
  case MORD_P_LT:
    return emit_lt(b, p->arg, p->value, t, f);
  case MORD_P_LE:
    return emit_le(b, p->arg, p->value, t, f);
  case MORD_P_GT:
    return emit_gt(b, p->arg, p->value, t, f);
  case MORD_P_GE:
    return emit_ge(b, p->arg, p->value, t, f);
  case MORD_P_MASK_ZERO:
  case MORD_P_MASK_EQ:
    return emit_mask(b, p, t, f);
  case MORD_P_AND: {
    int mid = mop_new_label(b);
    if (emit_pred(b, p->left, mid, f) != 0)
      return -1;
    if (mop_mark(b, mid) != 0)
      return -1;
    return emit_pred(b, p->right, t, f);
  }
  case MORD_P_OR: {
    int mid = mop_new_label(b);
    if (emit_pred(b, p->left, t, mid) != 0)
      return -1;
    if (mop_mark(b, mid) != 0)
      return -1;
    return emit_pred(b, p->right, t, f);
  }
  default:
    return -1;
  }
}

int mord_lower(const mord_policy *p, mopbuf *out, mord_diaglist *diags) {
  (void)diags;
  mopbuf_init(out);
  int arch_ok = mop_new_label(out);
  int rules = mop_new_label(out);
  int kill_lbl = mop_new_label(out);

  if (mop_emit(out, MOP_LD_ABS, (mord_u32)offsetof(struct seccomp_data, arch),
               -1, -1, -1) != 0)
    goto oom;
  if (mop_emit(out, MOP_JEQ, AUDIT_ARCH_X86_64, -1, arch_ok, kill_lbl) != 0)
    goto oom;
  if (mop_mark(out, arch_ok) != 0)
    goto oom;
  if (mop_emit(out, MOP_LD_ABS, (mord_u32)offsetof(struct seccomp_data, nr), -1,
               -1, -1) != 0)
    goto oom;
  if (mop_emit(out, MOP_AND_IMM, MORDANT_X32_SYSCALL_BIT, -1, -1, -1) != 0)
    goto oom;
  if (mop_emit(out, MOP_JEQ, 0, -1, rules, kill_lbl) != 0)
    goto oom;
  if (mop_mark(out, rules) != 0)
    goto oom;

  for (size_t i = 0; i < p->nrules; i++) {
    const mord_rule *r = &p->rules[i];
    int pred_lbl = mop_new_label(out);
    int nxt = mop_new_label(out);
    int act_lbl = mop_new_label(out);
    if (mop_emit(out, MOP_LD_ABS, (mord_u32)offsetof(struct seccomp_data, nr),
                 -1, -1, -1) != 0)
      goto oom;
    if (mop_emit(out, MOP_JEQ, r->nr, -1, pred_lbl, nxt) != 0)
      goto oom;
    if (mop_mark(out, pred_lbl) != 0)
      goto oom;
    if (emit_pred(out, r->pred, act_lbl, nxt) != 0)
      goto oom;
    if (mop_mark(out, act_lbl) != 0)
      goto oom;
    if (mop_emit(out, MOP_RET, r->action.ret, -1, -1, -1) != 0)
      goto oom;
    if (mop_mark(out, nxt) != 0)
      goto oom;
  }

  if (mop_emit(out, MOP_RET, p->default_action.ret, -1, -1, -1) != 0)
    goto oom;
  if (mop_mark(out, kill_lbl) != 0)
    goto oom;
  if (mop_emit(out, MOP_RET, mord_action_kill_process(), -1, -1, -1) != 0)
    goto oom;
  return 0;

oom:
  mord_diag_add(diags, 0, 0, "out of memory during lowering");
  mopbuf_free(out);
  return -1;
}

int mord_compile(const mord_policy *p, mord_program *out, mord_diaglist *diags) {
  mopbuf buf;
  if (mord_lower(p, &buf, diags) != 0)
    return -1;
  int rc = mord_resolve(&buf, out, diags);
  mopbuf_free(&buf);
  if (rc == 0)
    out->arch = p->has_arch ? p->arch : 0;
  return rc;
}
