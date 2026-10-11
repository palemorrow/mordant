#define _GNU_SOURCE
#include "mordant.h"

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))

static uint64_t sm_state;

static uint64_t sm_next(void) {
  uint64_t z = (sm_state += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

static const uint64_t BOUNDARY[] = {
    0ULL,
    1ULL,
    2ULL,
    3ULL,
    0xffULL,
    0x100ULL,
    0xffffffffULL,
    0x100000000ULL,
    0x100000001ULL,
    0x100000002ULL,
    0xfffffffffffffffeULL,
    0xffffffffffffffffULL,
};

static uint64_t rnd_val(void) {
  switch (sm_next() % 4) {
  case 0:
    return BOUNDARY[sm_next() % ARRAY_LEN(BOUNDARY)];
  case 1:
    return sm_next() & 0xffffULL;
  case 2:
    return 0x300000000ULL + (sm_next() & 0xffffULL);
  default:
    return sm_next();
  }
}

static const mord_u32 REAL[] = {0, 1, 2, 3, 9, 10, 16, 39, 60, 231};

static mord_u32 rnd_syscall(void) {
  if ((sm_next() % 5) == 0)
    return (mord_u32)(sm_next() % 400);
  return REAL[sm_next() % ARRAY_LEN(REAL)];
}

static mord_u32 rnd_action_ret(void) {
  uint32_t r = (uint32_t)(sm_next() % 3);
  if (r == 0)
    return mord_action_allow();
  if (r == 1)
    return mord_action_kill_process();
  return mord_action_errno((mord_u32)(1 + sm_next() % 65535));
}

static mord_pred *rnd_pred(int depth) {
  mord_pred *p = calloc(1, sizeof(*p));
  if (!p) {
    fprintf(stderr, "diff_gen: out of memory\n");
    exit(1);
  }
  if (depth <= 0 || (sm_next() % 3) == 0) {
    p->arg = (unsigned)(sm_next() % 6);
    if ((sm_next() % 4) == 0) {
      static const uint64_t masks[] = {0x1ULL,  0x2ULL,      0x4ULL,
                                       0xffULL, 0xff00ULL,   0xffffffffULL,
                                       0x100000004ULL, 0x100000000ULL};
      p->mask = masks[sm_next() % ARRAY_LEN(masks)];
      p->value = sm_next() & p->mask;
      p->kind = (p->value == 0) ? MORD_P_MASK_ZERO : MORD_P_MASK_EQ;
    } else {
      static const mord_pred_kind kinds[] = {MORD_P_EQ, MORD_P_NE, MORD_P_LT,
                                             MORD_P_LE, MORD_P_GT, MORD_P_GE};
      p->kind = kinds[sm_next() % ARRAY_LEN(kinds)];
      p->value = rnd_val();
    }
    return p;
  }
  p->kind = (sm_next() & 1) ? MORD_P_AND : MORD_P_OR;
  p->left = rnd_pred(depth - 1);
  p->right = rnd_pred(depth - 1);
  return p;
}

static void ap(char *buf, size_t cap, size_t *off, const char *fmt, ...) {
  if (*off >= cap)
    return;
  va_list args;
  va_start(args, fmt);
  int n = vsnprintf(buf + *off, cap - *off, fmt, args);
  va_end(args);
  if (n < 0)
    return;
  if ((size_t)n >= cap - *off)
    *off = cap - 1;
  else
    *off += (size_t)n;
}

static void agda_w64(char *buf, size_t cap, size_t *off, mord_u64 v) {
  ap(buf, cap, off, "(w64 %u %u)", (unsigned)(v >> 32), (unsigned)v);
}

static void agda_fin6(char *buf, size_t cap, unsigned n) {
  size_t off = 0;
  if (n == 0) {
    ap(buf, cap, &off, "zero");
    return;
  }
  for (unsigned i = 0; i < n; i++)
    ap(buf, cap, &off, "suc (");
  ap(buf, cap, &off, "zero");
  for (unsigned i = 0; i < n; i++)
    ap(buf, cap, &off, ")");
}

static void agda_pred(char *buf, size_t cap, size_t *off, const mord_pred *p) {
  char fin[64];
  agda_fin6(fin, sizeof(fin), p->arg);
  switch (p->kind) {
  case MORD_P_TRUE:
    ap(buf, cap, off, "ptrue");
    break;
  case MORD_P_EQ:
    ap(buf, cap, off, "peq (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_NE:
    ap(buf, cap, off, "pne (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_LT:
    ap(buf, cap, off, "plt (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_LE:
    ap(buf, cap, off, "ple (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_GT:
    ap(buf, cap, off, "pgt (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_GE:
    ap(buf, cap, off, "pge (%s) ", fin);
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_MASK_ZERO:
    ap(buf, cap, off, "pmaskzero (%s) ", fin);
    agda_w64(buf, cap, off, p->mask);
    break;
  case MORD_P_MASK_EQ:
    ap(buf, cap, off, "pmaskeq (%s) ", fin);
    agda_w64(buf, cap, off, p->mask);
    ap(buf, cap, off, " ");
    agda_w64(buf, cap, off, p->value);
    break;
  case MORD_P_AND:
    ap(buf, cap, off, "pand (");
    agda_pred(buf, cap, off, p->left);
    ap(buf, cap, off, ") (");
    agda_pred(buf, cap, off, p->right);
    ap(buf, cap, off, ")");
    break;
  case MORD_P_OR:
    ap(buf, cap, off, "por (");
    agda_pred(buf, cap, off, p->left);
    ap(buf, cap, off, ") (");
    agda_pred(buf, cap, off, p->right);
    ap(buf, cap, off, ")");
    break;
  }
}

static void agda_action(char *out, size_t cap, mord_u32 ret) {
  mord_u32 act = ret & SECCOMP_RET_ACTION_FULL;
  if (act == SECCOMP_RET_ALLOW)
    snprintf(out, cap, "actAllow");
  else if (act == SECCOMP_RET_KILL_PROCESS)
    snprintf(out, cap, "actKillProcess");
  else
    snprintf(out, cap, "actErrno %u", (unsigned)(ret & SECCOMP_RET_DATA));
}

int main(int argc, char **argv) {
  int count = 200;
  const char *dir = "build";
  if (argc >= 2) {
    int v = atoi(argv[1]);
    if (v > 0)
      count = v;
    else
      dir = argv[1];
  }
  if (argc >= 3)
    dir = argv[2];

  mkdir(dir, 0777);

  char sub[4096];
  snprintf(sub, sizeof(sub), "%s/Mordant", dir);
  mkdir(sub, 0777);

  char apath[4096];
  char cpath[4096];
  snprintf(apath, sizeof(apath), "%s/Mordant/Fixtures.agda", dir);
  snprintf(cpath, sizeof(cpath), "%s/c_diff.txt", dir);
  FILE *af = fopen(apath, "w");
  FILE *cf = fopen(cpath, "w");
  if (!af || !cf) {
    fprintf(stderr, "diff_gen: cannot open output files in '%s'\n", dir);
    return 1;
  }

  fprintf(af, "module Mordant.Fixtures where\n");
  fprintf(af, "open import Data.Nat using (ℕ)\n");
  fprintf(af, "open import Data.Fin using (zero; suc)\n");
  fprintf(af, "open import Data.List using (List; []; _∷_)\n");
  fprintf(af, "open import Data.Product using (_,_)\n");
  fprintf(af, "open import Mordant.Policy\n");
  fprintf(af, "open import Mordant.Word using (Word64; w64)\n");

  for (int i = 0; i < count; i++) {
    mord_policy pol;
    memset(&pol, 0, sizeof(pol));
    pol.has_arch = 1;
    pol.arch = (mord_u32)AUDIT_ARCH_X86_64;
    pol.has_default = 1;
    pol.default_action.ret = rnd_action_ret();
    unsigned nrules = (unsigned)(sm_next() % 7);
    pol.nrules = nrules;
    if (nrules) {
      pol.rules = calloc(nrules, sizeof(*pol.rules));
      if (!pol.rules) {
        fprintf(stderr, "diff_gen: out of memory\n");
        return 1;
      }
    }
    for (unsigned r = 0; r < nrules; r++) {
      pol.rules[r].nr = rnd_syscall();
      pol.rules[r].pred = rnd_pred(3);
      pol.rules[r].action.ret = rnd_action_ret();
    }

    mord_u32 farch = ((sm_next() % 8) == 0) ? (mord_u32)sm_next()
                                            : (mord_u32)AUDIT_ARCH_X86_64;
    int64_t fnr = ((sm_next() % 16) == 0)
                      ? (int64_t)(0x40000000u | (sm_next() & 0xffffu))
                      : (int64_t)(sm_next() % 320);
    mord_u64 args[6];
    for (int j = 0; j < 6; j++)
      args[j] = rnd_val();

    long action = -1;
    mord_diaglist d;
    mord_diags_init(&d);
    mord_program prog;
    if (mord_compile(&pol, &prog, &d) == 0) {
      if (mord_validate(&prog, &d) == 0) {
        mord_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.arch = farch;
        ctx.nr = fnr;
        for (int j = 0; j < 6; j++)
          ctx.args[j] = args[j];
        mord_u32 act;
        if (mord_eval_program(&prog, &ctx, &act, &d) == 0)
          action = (long)act;
      }
      mord_program_free(&prog);
    }
    mord_diags_free(&d);

    fprintf(cf, "%d %ld\n", i, action);

    char def[64];
    char pred[1024];
    char astat[32];
    agda_action(def, sizeof(def), pol.default_action.ret);

    fprintf(af, "f%d : Fixture\n", i);
    fprintf(af, "f%d = record { fArch = 0x%08X ; fNr = %lld ; fArgs = ", i,
            (unsigned)farch, (long long)fnr);
    for (int j = 0; j < 6; j++) {
      fprintf(af, "w64 %u %u", (unsigned)(args[j] >> 32), (unsigned)args[j]);
      if (j < 5)
        fprintf(af, " , ");
    }
    fprintf(af, " ; fPolicy = policy 0x%08X (%s) ", (unsigned)pol.arch, def);
    if (nrules == 0) {
      fprintf(af, "[]");
    } else {
      fprintf(af, "(");
      for (unsigned r = 0; r < nrules; r++) {
        size_t off = 0;
        pred[0] = '\0';
        agda_pred(pred, sizeof(pred), &off, pol.rules[r].pred);
        agda_action(astat, sizeof(astat), pol.rules[r].action.ret);
        fprintf(af, "rule %u (%s) (%s) ∷ ", (unsigned)pol.rules[r].nr, pred, astat);
      }
      fprintf(af, "[])");
    }
    fprintf(af, " }\n");

    mord_policy_free(&pol);
  }

  fprintf(af, "fixtures : List Fixture\n");
  fprintf(af, "fixtures = ");
  if (count == 0) {
    fprintf(af, "[]\n");
  } else {
    for (int i = 0; i < count; i++)
      fprintf(af, "f%d ∷ ", i);
    fprintf(af, "[]\n");
  }

  if (fclose(af) != 0 || fclose(cf) != 0) {
    fprintf(stderr, "diff_gen: write error\n");
    return 1;
  }
  return 0;
}
