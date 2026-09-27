#define _GNU_SOURCE
#include "install.h"
#include "mordant.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

enum {
  EXIT_OK = 0,
  EXIT_USAGE = 1,
  EXIT_INVALID = 2,
  EXIT_RUNTIME = 4
};

static void usage(FILE *f) {
  fprintf(f, "usage: mordant-load FILTER.bin [--exec -- CMD [ARGS...]]\n");
}

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

int main(int argc, char **argv) {
  if (argc < 2) {
    usage(stderr);
    return EXIT_USAGE;
  }
  const char *path = argv[1];
  char **cmd = NULL;
  int do_exec = 0;
  if (argc == 2) {
    do_exec = 0;
  } else if (strcmp(argv[2], "--exec") == 0) {
    if (argc < 5 || strcmp(argv[3], "--") != 0) {
      usage(stderr);
      return EXIT_USAGE;
    }
    cmd = &argv[4];
    do_exec = 1;
  } else {
    usage(stderr);
    return EXIT_USAGE;
  }

  mord_diaglist d;
  mord_diags_init(&d);
  mord_program prog;
  if (mord_program_read(path, &prog, &d) != 0) {
    print_diags(path, &d);
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  if (mord_validate(&prog, &d) != 0) {
    print_diags(path, &d);
    mord_program_free(&prog);
    mord_diags_free(&d);
    return EXIT_INVALID;
  }
  if (prog.arch != (mord_u32)AUDIT_ARCH_X86_64)
    fprintf(stderr,
            "mordant-load: warning: filter arch 0x%08x is not AUDIT_ARCH_X86_64\n",
            (unsigned)prog.arch);

  if (mordant_install_program(prog.insns, prog.count, &d) != 0) {
    print_diags(path, &d);
    mord_program_free(&prog);
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  fprintf(stderr, "mordant-load: filter installed\n");
  mord_program_free(&prog);

  if (do_exec) {
    execvp(cmd[0], cmd);
    fprintf(stderr, "mordant-load: exec '%s' failed: %s\n", cmd[0],
            strerror(errno));
    mord_diags_free(&d);
    return EXIT_RUNTIME;
  }
  mord_diags_free(&d);
  return EXIT_OK;
}
