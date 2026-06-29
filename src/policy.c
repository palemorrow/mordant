#define _GNU_SOURCE
#include "mordant.h"

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

void mord_diags_init(mord_diaglist *d) {
  d->items = NULL;
  d->count = 0;
  d->cap = 0;
}

void mord_diags_free(mord_diaglist *d) {
  free(d->items);
  d->items = NULL;
  d->count = 0;
  d->cap = 0;
}

void mord_diag_add(mord_diaglist *d, unsigned line, unsigned col,
                   const char *fmt, ...) {
  if (d->count == d->cap) {
    size_t cap = d->cap ? d->cap * 2 : 8;
    mord_diag *items = realloc(d->items, cap * sizeof(*items));
    if (!items)
      return;
    d->items = items;
    d->cap = cap;
  }
  mord_diag *item = &d->items[d->count++];
  item->line = line;
  item->col = col;
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(item->message, sizeof(item->message), fmt, ap);
  va_end(ap);
}

mord_pred *mord_pred_new(mord_pred_kind kind) {
  mord_pred *p = calloc(1, sizeof(*p));
  if (p)
    p->kind = kind;
  return p;
}

void mord_pred_free(mord_pred *p) {
  if (!p)
    return;
  mord_pred_free(p->left);
  mord_pred_free(p->right);
  free(p);
}

void mord_policy_free(mord_policy *p) {
  if (!p)
    return;
  for (size_t i = 0; i < p->nrules; i++)
    mord_pred_free(p->rules[i].pred);
  free(p->rules);
  p->rules = NULL;
  p->nrules = 0;
}

int mord_is_supported_action(mord_u32 ret) {
  mord_u32 act = ret & SECCOMP_RET_ACTION_FULL;
  return act == SECCOMP_RET_ALLOW || act == SECCOMP_RET_ERRNO ||
         act == SECCOMP_RET_KILL_PROCESS;
}

mord_u32 mord_action_allow(void) { return SECCOMP_RET_ALLOW; }

mord_u32 mord_action_kill_process(void) { return SECCOMP_RET_KILL_PROCESS; }

mord_u32 mord_action_errno(mord_u32 err) {
  return SECCOMP_RET_ERRNO | (err & SECCOMP_RET_DATA);
}

static int pred_eval(const mord_pred *p, const mord_u64 *args) {
  if (!p)
    return 1;
  mord_u64 a;
  switch (p->kind) {
  case MORD_P_TRUE:
    return 1;
  case MORD_P_EQ:
    return args[p->arg] == p->value;
  case MORD_P_NE:
    return args[p->arg] != p->value;
  case MORD_P_LT:
    return args[p->arg] < p->value;
  case MORD_P_LE:
    return args[p->arg] <= p->value;
  case MORD_P_GT:
    return args[p->arg] > p->value;
  case MORD_P_GE:
    return args[p->arg] >= p->value;
  case MORD_P_MASK_ZERO:
    return (args[p->arg] & p->mask) == 0;
  case MORD_P_MASK_EQ:
    a = args[p->arg] & p->mask;
    return a == p->value;
  case MORD_P_AND:
    return pred_eval(p->left, args) && pred_eval(p->right, args);
  case MORD_P_OR:
    return pred_eval(p->left, args) || pred_eval(p->right, args);
  }
  return 0;
}

int mord_eval_policy(const mord_policy *p, const mord_context *ctx,
                     mord_u32 *action) {
  mord_u32 nr = (mord_u32)ctx->nr;
  if (!p->has_arch || ctx->arch != p->arch) {
    *action = mord_action_kill_process();
    return 0;
  }
  if (nr & MORDANT_X32_SYSCALL_BIT) {
    *action = mord_action_kill_process();
    return 0;
  }
  for (size_t i = 0; i < p->nrules; i++) {
    const mord_rule *r = &p->rules[i];
    if (r->nr == nr && pred_eval(r->pred, ctx->args)) {
      *action = r->action.ret;
      return 0;
    }
  }
  *action = p->default_action.ret;
  return 0;
}
