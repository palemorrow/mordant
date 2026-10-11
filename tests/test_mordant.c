#define _GNU_SOURCE
#include "mordant.h"

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <linux/filter.h>

#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))

static int g_failed;

static void group(const char *name, int ok) {
  printf("%s %s\n", ok ? "pass" : "fail", name);
  if (!ok)
    g_failed = 1;
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

static int parse_fails(const char *src) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  int rc = mord_parse_string(src, "<test>", &p, &d);
  int ok = (rc != 0) && (d.count > 0);
  mord_policy_free(&p);
  mord_diags_free(&d);
  return ok;
}

static int build(const char *src, mord_policy *p, mord_program *prog) {
  mord_diaglist d;
  mord_diags_init(&d);
  if (mord_parse_string(src, "<test>", p, &d) != 0) {
    mord_diags_free(&d);
    return -1;
  }
  if (mord_compile(p, prog, &d) != 0) {
    mord_policy_free(p);
    mord_diags_free(&d);
    return -1;
  }
  if (mord_validate(prog, &d) != 0) {
    mord_program_free(prog);
    mord_policy_free(p);
    mord_diags_free(&d);
    return -1;
  }
  mord_diags_free(&d);
  return 0;
}

static const char *EXAMPLE =
    "arch x86_64\n"
    "\n"
    "default errno 1\n"
    "\n"
    "allow read\n"
    "allow write\n"
    "allow close\n"
    "allow exit\n"
    "allow exit_group\n"
    "\n"
    "allow mmap if arg2 & 0x4 == 0\n"
    "\n"
    "allow mprotect if arg2 & 0x4 == 0\n"
    "\n"
    "allow ioctl if arg1 == 0x5401\n";

static int test_parser_accept(void) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  int rc = mord_parse_string(EXAMPLE, "example.mdt", &p, &d);
  int ok = rc == 0 && p.has_arch && p.has_default && p.nrules == 8 &&
           p.arch == (mord_u32)AUDIT_ARCH_X86_64;
  if (!ok)
    printf("  example policy: rc=%d nrules=%zu arch=0x%08x\n", rc, p.nrules,
           (unsigned)p.arch);
  mord_policy_free(&p);
  mord_diags_free(&d);
  return ok;
}

static int test_parser_reject(void) {
  static const struct {
    const char *label;
    const char *src;
  } cases[] = {
      {"unknown-syscall",
       "arch x86_64\ndefault allow\nallow not_a_syscall\n"},
      {"errno-zero", "arch x86_64\ndefault errno 0\n"},
      {"errno-too-big", "arch x86_64\ndefault errno 70000\n"},
      {"arg9", "arch x86_64\ndefault allow\nallow read if arg9 == 0\n"},
      {"missing-arch", "default allow\n"},
      {"duplicate-arch", "arch x86_64\narch x86_64\ndefault allow\n"},
      {"malformed-hex", "arch x86_64\ndefault allow\nallow read if arg0 == 0x\n"},
      {"x32-bit", "arch x86_64\ndefault allow\nallow 0x40000000\n"},
      {"ambiguous-mixed",
       "arch x86_64\ndefault allow\n"
       "allow read if arg0 == 1 && arg1 == 2 || arg2 == 3\n"},
      {"unsupported-arch", "arch arm64\ndefault allow\n"},
      {"mask-outside",
       "arch x86_64\ndefault allow\nallow read if arg0 & 0xff == 0x100\n"},
  };
  int ok = 1;
  for (size_t i = 0; i < ARRAY_LEN(cases); i++) {
    if (!parse_fails(cases[i].src)) {
      printf("  case '%s' was accepted or produced no diagnostic\n",
             cases[i].label);
      ok = 0;
    }
  }
  return ok;
}

static int test_compile(void) {
  const char *policies[] = {
      "arch x86_64\ndefault allow\n",
      EXAMPLE,
      "arch x86_64\ndefault kill\nallow read if arg0 < 5\n"
      "allow write if (arg1 >= 0x10) && (arg1 <= 0x20)\n",
      "arch x86_64\ndefault errno 9\nallow read if arg0 & 0x100000004 == 0\n"
      "allow write if (arg0 == 0xffffffffffffffff) || (arg1 != 7)\n",
      "arch x86_64\ndefault allow\nkill 0\nerrno 5 1 if arg2 > 0x100000000\n",
  };
  int ok = 1;
  for (size_t i = 0; i < ARRAY_LEN(policies); i++) {
    mord_policy p;
    mord_program prog;
    if (build(policies[i], &p, &prog) != 0) {
      printf("  policy %zu failed to parse/compile/validate\n", i);
      ok = 0;
      continue;
    }
    if (prog.count == 0 || prog.count > (size_t)MORDANT_MAX_INSNS) {
      printf("  policy %zu count %zu out of range\n", i, prog.count);
      ok = 0;
    }
    if (prog.insns[prog.count - 1].code != (BPF_RET | BPF_K)) {
      printf("  policy %zu does not end with a return instruction\n", i);
      ok = 0;
    }
    mord_program_free(&prog);
    mord_policy_free(&p);
  }
  return ok;
}

static int cmp64_expected(uint64_t a, const char *op, uint64_t c) {
  if (strcmp(op, "<") == 0)
    return a < c;
  if (strcmp(op, "<=") == 0)
    return a <= c;
  if (strcmp(op, ">") == 0)
    return a > c;
  if (strcmp(op, ">=") == 0)
    return a >= c;
  if (strcmp(op, "==") == 0)
    return a == c;
  if (strcmp(op, "!=") == 0)
    return a != c;
  return 0;
}

static uint64_t sm_state;

static uint64_t sm_next(void) {
  uint64_t z = (sm_state += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

static int eval_pair(const mord_policy *p, const mord_program *prog,
                     const mord_context *ctx, mord_u32 *out) {
  mord_u32 a1;
  mord_u32 a2;
  mord_diaglist d;
  mord_diags_init(&d);
  int rc = 0;
  if (mord_eval_policy(p, ctx, &a1) != 0)
    rc = -1;
  else if (mord_eval_program(prog, ctx, &a2, &d) != 0)
    rc = -1;
  else if (a1 != a2)
    rc = -1;
  else
    *out = a1;
  mord_diags_free(&d);
  return rc;
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

static int test_compare64(void) {
  static const uint64_t consts[] = {0ULL, 0xffffffffULL, 0x100000000ULL,
                                    0xffffffffffffffffULL, 0x100000002ULL};
  static const char *ops[] = {"<", "<=", ">", ">=", "==", "!="};
  int ok = 1;
  for (size_t ci = 0; ci < ARRAY_LEN(consts); ci++) {
    for (size_t oi = 0; oi < ARRAY_LEN(ops); oi++) {
      char src[256];
      snprintf(src, sizeof(src),
               "arch x86_64\ndefault errno 7\nallow read if arg0 %s 0x%llx\n",
               ops[oi], (unsigned long long)consts[ci]);
      mord_policy p;
      mord_program prog;
      if (build(src, &p, &prog) != 0) {
        printf("  64-bit build failed: const=0x%llx op=%s\n",
               (unsigned long long)consts[ci], ops[oi]);
        ok = 0;
        continue;
      }
      for (size_t vi = 0; vi < ARRAY_LEN(BOUNDARY) + 512; vi++) {
        uint64_t v;
        if (vi < ARRAY_LEN(BOUNDARY))
          v = BOUNDARY[vi];
        else
          v = sm_next();
        mord_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        ctx.arch = p.arch;
        ctx.nr = 0;
        ctx.args[0] = v;
        mord_u32 expected = cmp64_expected(v, ops[oi], consts[ci])
                                ? mord_action_allow()
                                : mord_action_errno(7);
        mord_u32 got;
        if (eval_pair(&p, &prog, &ctx, &got) != 0 || got != expected) {
          printf("  mismatch v=0x%llx const=0x%llx op=%s\n",
                 (unsigned long long)v, (unsigned long long)consts[ci],
                 ops[oi]);
          ok = 0;
          break;
        }
      }
      mord_program_free(&prog);
      mord_policy_free(&p);
    }
  }

  static const mord_u64 mask = 0x100000004ULL;
  static const mord_u64 mask_vals[] = {0ULL, 0x100000000ULL};
  static const char *mask_src[] = {
      "arch x86_64\ndefault errno 7\nallow read if arg0 & 0x100000004 == 0\n",
      "arch x86_64\ndefault errno 7\n"
      "allow read if arg0 & 0x100000004 == 0x100000000\n",
  };
  for (size_t mi = 0; mi < ARRAY_LEN(mask_src); mi++) {
    mord_policy p;
    mord_program prog;
    if (build(mask_src[mi], &p, &prog) != 0) {
      printf("  mask build failed %zu\n", mi);
      ok = 0;
      continue;
    }
    for (size_t vi = 0; vi < ARRAY_LEN(BOUNDARY) + 512; vi++) {
      uint64_t v = vi < ARRAY_LEN(BOUNDARY) ? BOUNDARY[vi] : sm_next();
      mord_context ctx;
      memset(&ctx, 0, sizeof(ctx));
      ctx.arch = p.arch;
      ctx.nr = 0;
      ctx.args[0] = v;
      uint64_t masked = v & mask;
      mord_u32 expected = masked == mask_vals[mi] ? mord_action_allow()
                                                  : mord_action_errno(7);
      mord_u32 got;
      if (eval_pair(&p, &prog, &ctx, &got) != 0 || got != expected) {
        printf("  mask mismatch v=0x%llx mask=0x%llx val=0x%llx\n",
               (unsigned long long)v, (unsigned long long)mask,
               (unsigned long long)mask_vals[mi]);
        ok = 0;
        break;
      }
    }
    mord_program_free(&prog);
    mord_policy_free(&p);
  }
  return ok;
}

static uint64_t rnd_val(void) {
  if (sm_next() & 1)
    return BOUNDARY[sm_next() % ARRAY_LEN(BOUNDARY)];
  return sm_next();
}

static void rnd_pred(char *buf, size_t cap, size_t *off, int depth) {
  static const char *ops[] = {"<", "<=", ">", ">=", "==", "!="};
  if (depth <= 0 || (sm_next() % 3) == 0) {
    unsigned arg = (unsigned)(sm_next() % 6);
    if ((sm_next() % 4) == 0) {
      static const uint64_t masks[] = {0x1ULL,    0x2ULL,       0x4ULL,
                                       0xffULL,   0xff00ULL,    0xffffffffULL,
                                       0x100000004ULL, 0x100000000ULL};
      uint64_t mask = masks[sm_next() % ARRAY_LEN(masks)];
      uint64_t val = sm_next() & mask;
      ap(buf, cap, off, "arg%u & 0x%llx == 0x%llx", arg,
         (unsigned long long)mask, (unsigned long long)val);
      return;
    }
    const char *op = ops[sm_next() % ARRAY_LEN(ops)];
    ap(buf, cap, off, "arg%u %s 0x%llx", arg, op,
       (unsigned long long)rnd_val());
    return;
  }
  const char *join = (sm_next() & 1) ? "&&" : "||";
  ap(buf, cap, off, "(");
  rnd_pred(buf, cap, off, depth - 1);
  ap(buf, cap, off, " %s ", join);
  rnd_pred(buf, cap, off, depth - 1);
  ap(buf, cap, off, ")");
}

static void rnd_action(char *out, size_t cap) {
  uint32_t r = (uint32_t)(sm_next() % 3);
  if (r == 0)
    snprintf(out, cap, "allow");
  else if (r == 1)
    snprintf(out, cap, "kill");
  else
    snprintf(out, cap, "errno %u", (unsigned)(1 + sm_next() % 65535));
}

static int test_random(void) {
  static const mord_u32 real[] = {0, 1, 2, 3, 9, 10, 16, 39, 60, 231};
  int ok = 1;
  int cases = 20000;
  char *src = malloc(8192);
  if (!src)
    return 0;
  for (int it = 0; it < cases; it++) {
    size_t off = 0;
    char act[32];
    rnd_action(act, sizeof(act));
    ap(src, 8192, &off, "arch x86_64\ndefault %s\n", act);
    unsigned nrules = (unsigned)(sm_next() % 5);
    for (unsigned i = 0; i < nrules; i++) {
      mord_u32 nr = (sm_next() % 5 == 0)
                        ? (mord_u32)(sm_next() % 300)
                        : real[sm_next() % ARRAY_LEN(real)];
      rnd_action(act, sizeof(act));
      ap(src, 8192, &off, "%s %u if ", act, (unsigned)nr);
      rnd_pred(src, 8192, &off, 3);
      ap(src, 8192, &off, "\n");
    }
    mord_policy p;
    mord_program prog;
    if (build(src, &p, &prog) != 0) {
      printf("  random case %d failed to build:\n%s\n", it, src);
      ok = 0;
      break;
    }
    mord_context ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.arch = (sm_next() % 8 == 0) ? (mord_u32)sm_next()
                                    : (mord_u32)AUDIT_ARCH_X86_64;
    ctx.nr = (sm_next() % 16 == 0)
                 ? (int64_t)(0x40000000u | (sm_next() & 0xffffu))
                 : (int64_t)(sm_next() % 320);
    for (int j = 0; j < 6; j++)
      ctx.args[j] = rnd_val();
    mord_u32 got;
    if (eval_pair(&p, &prog, &ctx, &got) != 0) {
      printf("  random case %d diverged:\n%s", it, src);
      ok = 0;
      mord_program_free(&prog);
      mord_policy_free(&p);
      break;
    }
    mord_program_free(&prog);
    mord_policy_free(&p);
  }
  free(src);
  return ok;
}

static void emit_or_chain(char *buf, size_t cap, size_t *off, int i, int n) {
  if (i == n - 1) {
    ap(buf, cap, off, "(arg0 == %d)", i);
    return;
  }
  ap(buf, cap, off, "(arg0 == %d) || (", i);
  emit_or_chain(buf, cap, off, i + 1, n);
  ap(buf, cap, off, ")");
}

static int test_branch(void) {
  size_t cap = 262144;
  char *src = malloc(cap);
  if (!src)
    return 0;
  size_t off = 0;
  ap(src, cap, &off, "arch x86_64\ndefault allow\n");
  ap(src, cap, &off, "kill 9000 if ");
  emit_or_chain(src, cap, &off, 0, 120);
  ap(src, cap, &off, "\n");
  for (int i = 0; i < 400; i++)
    ap(src, cap, &off, "allow %d if arg0 == %d\n", 1000 + i, i);

  mord_policy p;
  mord_program prog;
  int ok = 1;
  if (build(src, &p, &prog) != 0) {
    printf("  branch policy failed to build\n");
    free(src);
    return 0;
  }
  size_t trampolines = 0;
  for (size_t i = 0; i < prog.count; i++) {
    const mord_insn *ins = &prog.insns[i];
    if (ins->code == (BPF_JMP | BPF_JA)) {
      size_t target = i + 1 + (size_t)ins->k;
      if (!(target > i && target < prog.count)) {
        printf("  ja at %zu targets %zu out of range\n", i, target);
        ok = 0;
      }
    } else if (ins->code == (BPF_JMP | BPF_JEQ | BPF_K) ||
               ins->code == (BPF_JMP | BPF_JGT | BPF_K) ||
               ins->code == (BPF_JMP | BPF_JGE | BPF_K)) {
      size_t t = i + 1 + ins->jt;
      size_t f = i + 1 + ins->jf;
      if (!(t > i && t < prog.count) || !(f > i && f < prog.count)) {
        printf("  cond at %zu targets %zu,%zu out of range\n", i, t, f);
        ok = 0;
      }
      if (ins->jt == 0 && ins->jf == 1 && i + 2 < prog.count &&
          prog.insns[i + 1].code == (BPF_JMP | BPF_JA) &&
          prog.insns[i + 2].code == (BPF_JMP | BPF_JA))
        trampolines++;
    }
  }
  if (trampolines == 0) {
    printf("  expected trampolines but found none\n");
    ok = 0;
  }
  if (prog.count > (size_t)MORDANT_MAX_INSNS) {
    printf("  branch program exceeds instruction limit\n");
    ok = 0;
  }
  mord_program_free(&prog);
  mord_policy_free(&p);
  free(src);
  return ok;
}

static int test_limit(void) {
  size_t cap = 131072;
  char *src = malloc(cap);
  if (!src)
    return 0;
  size_t off = 0;
  ap(src, cap, &off, "arch x86_64\ndefault allow\n");
  for (int i = 0; i < 700; i++)
    ap(src, cap, &off, "allow read if arg0 < 5\n");
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  int ok = 0;
  if (mord_parse_string(src, "<limit>", &p, &d) != 0) {
    printf("  limit policy failed to parse\n");
  } else {
    mord_program prog;
    int rc = mord_compile(&p, &prog, &d);
    if (rc == 0) {
      printf("  oversized policy compiled unexpectedly\n");
      mord_program_free(&prog);
    } else {
      ok = 0;
      for (size_t i = 0; i < d.count; i++) {
        if (strstr(d.items[i].message, "limit")) {
          ok = 1;
          break;
        }
      }
      if (!ok)
        printf("  failure diagnostic does not mention the limit\n");
    }
    mord_policy_free(&p);
  }
  mord_diags_free(&d);
  free(src);
  return ok;
}

static int test_roundtrip(void) {
  mord_policy p;
  mord_program prog;
  if (build(EXAMPLE, &p, &prog) != 0) {
    printf("  round-trip policy failed to build\n");
    return 0;
  }
  char path[] = "/tmp/mordant_roundtripXXXXXX";
  int fd = mkstemp(path);
  if (fd < 0) {
    printf("  mkstemp failed\n");
    mord_program_free(&prog);
    mord_policy_free(&p);
    return 0;
  }
  close(fd);
  mord_diaglist d;
  mord_diags_init(&d);
  int ok = 1;
  if (mord_program_write(&prog, path, &d) != 0) {
    printf("  program write failed\n");
    ok = 0;
  } else {
    mord_program readback;
    if (mord_program_read(path, &readback, &d) != 0) {
      printf("  program read failed\n");
      ok = 0;
    } else {
      if (readback.count != prog.count || readback.arch != prog.arch ||
          memcmp(readback.insns, prog.insns,
                 prog.count * sizeof(mord_insn)) != 0) {
        printf("  round-trip bytes differ\n");
        ok = 0;
      }
      mord_program_free(&readback);
    }
  }
  remove(path);
  mord_diags_free(&d);
  mord_program_free(&prog);
  mord_policy_free(&p);
  return ok;
}

int main(void) {
  group("parser-accept", test_parser_accept());
  group("parser-reject", test_parser_reject());
  group("compile", test_compile());
  group("compare64", test_compare64());
  group("random-differential", test_random());
  group("branch-layout", test_branch());
  group("instruction-limit", test_limit());
  group("serialization-roundtrip", test_roundtrip());
  return g_failed ? 1 : 0;
}
