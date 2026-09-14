#define _GNU_SOURCE
#include "mordant.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

enum {
  EXIT_OK = 0,
  EXIT_USAGE = 1,
  EXIT_POLICY = 2,
  EXIT_COMPILE = 3,
  EXIT_RUNTIME = 4
};

static void print_diags(const char *path, const mord_diaglist *d) {
  for (size_t i = 0; i < d->count; i++) {
    const mord_diag *g = &d->items[i];
    if (g->line)
      fprintf(stderr, "%s:%u:%u: %s\n", path ? path : "<input>", g->line, g->col,
              g->message);
    else
      fprintf(stderr, "%s: %s\n", path ? path : "<input>", g->message);
  }
}

static void print_action(FILE *f, mord_u32 ret) {
  mord_u32 act = ret & SECCOMP_RET_ACTION_FULL;
  if (act == SECCOMP_RET_ALLOW)
    fprintf(f, "allow");
  else if (act == SECCOMP_RET_KILL_PROCESS)
    fprintf(f, "kill_process");
  else if (act == SECCOMP_RET_ERRNO)
    fprintf(f, "errno(%u)", (unsigned)(ret & SECCOMP_RET_DATA));
  else
    fprintf(f, "0x%08x", ret);
}

static void usage(FILE *f) {
  fprintf(f,
          "usage: mordant <command> [options]\n"
          "  check   POLICY.mdt\n"
          "  compile POLICY.mdt -o FILTER.bin\n"
          "  dump    FILTER.bin\n"
          "  eval    POLICY.mdt --syscall NAME|NR [--argN V]...\n"
          "  verify  FILTER.bin\n");
}

static int cmd_check(const char *path) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  int rc = mord_parse_file(path, &p, &d);
  if (rc != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_POLICY;
  }
  printf("%s: ok, %zu rule(s), arch 0x%08x\n", path, p.nrules, p.arch);
  mord_policy_free(&p);
  mord_diags_free(&d);
  return EXIT_OK;
}

static int cmd_compile(const char *path, const char *out) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  if (mord_parse_file(path, &p, &d) != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_POLICY;
  }
  mord_program prog;
  if (mord_compile(&p, &prog, &d) != 0) {
    print_diags(path, &d);
    mord_policy_free(&p);
    mord_diags_free(&d);
    return EXIT_COMPILE;
  }
  if (mord_validate(&prog, &d) != 0) {
    print_diags(path, &d);
    mord_program_free(&prog);
    mord_policy_free(&p);
    mord_diags_free(&d);
    return EXIT_COMPILE;
  }
  if (mord_program_write(&prog, out, &d) != 0) {
    print_diags(out, &d);
    mord_program_free(&prog);
    mord_policy_free(&p);
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  fprintf(stderr, "%s: %zu instructions -> %s\n", path, prog.count, out);
  mord_program_free(&prog);
  mord_policy_free(&p);
  mord_diags_free(&d);
  return EXIT_OK;
}

static int cmd_dump(const char *path) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_program prog;
  if (mord_program_read(path, &prog, &d) != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  mord_program_dump(stdout, &prog);
  mord_program_free(&prog);
  mord_diags_free(&d);
  return EXIT_OK;
}

static int cmd_verify(const char *path) {
  mord_diaglist d;
  mord_diags_init(&d);
  mord_program prog;
  if (mord_program_read(path, &prog, &d) != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  int rc = mord_validate(&prog, &d);
  if (rc != 0) {
    print_diags(path, &d);
    mord_program_free(&prog);
    mord_diags_free(&d);
    return EXIT_POLICY;
  }
  printf("%s: ok, %zu instruction(s) valid\n", path, prog.count);
  mord_program_free(&prog);
  mord_diags_free(&d);
  return EXIT_OK;
}

static int parse_u64(const char *s, mord_u64 *out) {
  if (!s || !*s)
    return -1;
  errno = 0;
  char *end = NULL;
  unsigned long long v = strtoull(s, &end, 0);
  if (errno != 0 || end == s || *end != '\0')
    return -1;
  *out = (mord_u64)v;
  return 0;
}

static int cmd_eval(int argc, char **argv) {
  const char *path = argv[0];
  mord_diaglist d;
  mord_diags_init(&d);
  mord_policy p;
  if (mord_parse_file(path, &p, &d) != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_POLICY;
  }
  mord_context ctx;
  memset(&ctx, 0, sizeof(ctx));
  ctx.arch = p.arch;
  int have_nr = 0;
  int rc = EXIT_OK;
  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--syscall") == 0 && i + 1 < argc) {
      const char *val = argv[++i];
      mord_u64 num;
      if (parse_u64(val, &num) == 0) {
        ctx.nr = (int64_t)num;
      } else {
        mord_u32 nr;
        if (mord_syscall_lookup(val, &nr) != 0) {
          fprintf(stderr, "mordant: unknown syscall '%s'\n", val);
          rc = EXIT_USAGE;
          goto done;
        }
        ctx.nr = (int64_t)nr;
      }
      have_nr = 1;
    } else if (strcmp(a, "--nr") == 0 && i + 1 < argc) {
      mord_u64 num;
      if (parse_u64(argv[++i], &num) != 0) {
        fprintf(stderr, "mordant: invalid --nr value\n");
        rc = EXIT_USAGE;
        goto done;
      }
      ctx.nr = (int64_t)num;
      have_nr = 1;
    } else if (strcmp(a, "--arch") == 0 && i + 1 < argc) {
      const char *val = argv[++i];
      if (strcmp(val, "x86_64") == 0)
        ctx.arch = AUDIT_ARCH_X86_64;
      else {
        mord_u64 num;
        if (parse_u64(val, &num) != 0) {
          fprintf(stderr, "mordant: invalid --arch value\n");
          rc = EXIT_USAGE;
          goto done;
        }
        ctx.arch = (mord_u32)num;
      }
    } else if (strcmp(a, "--ip") == 0 && i + 1 < argc) {
      mord_u64 num;
      if (parse_u64(argv[++i], &num) != 0) {
        fprintf(stderr, "mordant: invalid --ip value\n");
        rc = EXIT_USAGE;
        goto done;
      }
      ctx.ip = num;
    } else if (strncmp(a, "--arg", 5) == 0 && a[5] >= '0' && a[5] <= '5' &&
               a[6] == '\0' && i + 1 < argc) {
      unsigned idx = (unsigned)(a[5] - '0');
      mord_u64 num;
      if (parse_u64(argv[++i], &num) != 0) {
        fprintf(stderr, "mordant: invalid --arg%u value\n", idx);
        rc = EXIT_USAGE;
        goto done;
      }
      ctx.args[idx] = num;
    } else {
      fprintf(stderr, "mordant: unknown option '%s'\n", a);
      rc = EXIT_USAGE;
      goto done;
    }
  }
  if (!have_nr) {
    fprintf(stderr, "mordant: eval requires --syscall\n");
    rc = EXIT_USAGE;
    goto done;
  }

  mord_u32 action;
  if (mord_eval_policy(&p, &ctx, &action) != 0) {
    rc = EXIT_RUNTIME;
    goto done;
  }
  mord_program prog;
  if (mord_compile(&p, &prog, &d) != 0) {
    print_diags(path, &d);
    rc = EXIT_COMPILE;
    goto done;
  }
  mord_u32 bpf_action;
  if (mord_eval_program(&prog, &ctx, &bpf_action, &d) != 0) {
    print_diags(path, &d);
    mord_program_free(&prog);
    rc = EXIT_COMPILE;
    goto done;
  }
  printf("policy: ");
  print_action(stdout, action);
  printf("\nbpf:    ");
  print_action(stdout, bpf_action);
  printf("\n");
  rc = (action == bpf_action) ? EXIT_OK : EXIT_RUNTIME;
  mord_program_free(&prog);

done:
  mord_policy_free(&p);
  mord_diags_free(&d);
  return rc;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    usage(stderr);
    return EXIT_USAGE;
  }
  const char *cmd = argv[1];
  if (strcmp(cmd, "check") == 0) {
    if (argc != 3) {
      usage(stderr);
      return EXIT_USAGE;
    }
    return cmd_check(argv[2]);
  }
  if (strcmp(cmd, "compile") == 0) {
    if (argc != 5 || strcmp(argv[3], "-o") != 0) {
      usage(stderr);
      return EXIT_USAGE;
    }
    return cmd_compile(argv[2], argv[4]);
  }
  if (strcmp(cmd, "dump") == 0) {
    if (argc != 3) {
      usage(stderr);
      return EXIT_USAGE;
    }
    return cmd_dump(argv[2]);
  }
  if (strcmp(cmd, "eval") == 0) {
    if (argc < 3) {
      usage(stderr);
      return EXIT_USAGE;
    }
    return cmd_eval(argc - 2, argv + 2);
  }
  if (strcmp(cmd, "verify") == 0) {
    if (argc != 3) {
      usage(stderr);
      return EXIT_USAGE;
    }
    return cmd_verify(argv[2]);
  }
  usage(stderr);
  return EXIT_USAGE;
}
