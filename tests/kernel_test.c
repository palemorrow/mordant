#define _GNU_SOURCE
#include "mordant.h"

#include "../tools/install.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

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

static int build_policy(const char *src, mord_policy *p, mord_program *prog) {
  mord_diaglist d;
  mord_diags_init(&d);
  if (mord_parse_string(src, "<kernel>", p, &d) != 0) {
    print_diags("<kernel>", &d);
    mord_diags_free(&d);
    return -1;
  }
  if (mord_compile(p, prog, &d) != 0) {
    print_diags("<kernel>", &d);
    mord_policy_free(p);
    mord_diags_free(&d);
    return -1;
  }
  if (mord_validate(prog, &d) != 0) {
    print_diags("<kernel>", &d);
    mord_program_free(prog);
    mord_policy_free(p);
    mord_diags_free(&d);
    return -1;
  }
  mord_diags_free(&d);
  return 0;
}

static void child_errno_getpid(mord_program *prog) {
  int fds[2];
  if (pipe(fds) != 0)
    _exit(10);
  mord_diaglist d;
  mord_diags_init(&d);
  if (mordant_install_program(prog->insns, prog->count, &d) != 0)
    _exit(11);
  errno = 0;
  long r = syscall(SYS_getpid);
  if (r != -1 || errno != EPERM)
    _exit(12);
  errno = 0;
  long w = syscall(SYS_write, fds[1], "x", 1);
  if (w != 1)
    _exit(13);
  errno = 0;
  long pp = syscall(SYS_getppid);
  if (pp < 0 || errno == EPERM)
    _exit(14);
  _exit(0);
}

static void child_kill_default(mord_program *prog) {
  int fds[2];
  if (pipe(fds) != 0)
    syscall(SYS_exit_group, 20);
  mord_diaglist d;
  mord_diags_init(&d);
  if (mordant_install_program(prog->insns, prog->count, &d) != 0)
    syscall(SYS_exit_group, 21);
  errno = 0;
  long w = syscall(SYS_write, fds[1], "k", 1);
  if (w != 1)
    syscall(SYS_exit_group, 22);
  syscall(SYS_exit_group, 0);
}

static int run_child(mord_program *prog, void (*fn)(mord_program *),
                     const char *label) {
  pid_t pid = fork();
  if (pid < 0) {
    fprintf(stderr, "kernel test: fork failed: %s\n", strerror(errno));
    return -1;
  }
  if (pid == 0)
    fn(prog);
  int status = 0;
  if (waitpid(pid, &status, 0) < 0) {
    fprintf(stderr, "kernel test: waitpid failed: %s\n", strerror(errno));
    return -1;
  }
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    fprintf(stderr, "kernel test: %s child failed (status 0x%x)\n", label,
            (unsigned)status);
    return -1;
  }
  return 0;
}

int main(void) {
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
    if (errno == EPERM) {
      printf("kernel test: skip\n");
      return 0;
    }
    fprintf(stderr, "kernel test: prctl failed: %s\n", strerror(errno));
    return 1;
  }

  static const char *ALLOW_DEFAULT =
      "arch x86_64\ndefault allow\nerrno 1 getpid\n";
  static const char *KILL_DEFAULT =
      "arch x86_64\ndefault kill\nallow write\nallow exit_group\n";

  mord_policy p;
  mord_program prog;
  int rc = 0;

  if (build_policy(ALLOW_DEFAULT, &p, &prog) != 0) {
    fprintf(stderr, "kernel test: could not build errno-getpid policy\n");
    return 1;
  }
  if (run_child(&prog, child_errno_getpid, "errno-getpid") != 0)
    rc = 1;
  mord_program_free(&prog);
  mord_policy_free(&p);

  if (build_policy(KILL_DEFAULT, &p, &prog) != 0) {
    fprintf(stderr, "kernel test: could not build kill-default policy\n");
    return 1;
  }
  if (run_child(&prog, child_kill_default, "kill-default") != 0)
    rc = 1;
  mord_program_free(&prog);
  mord_policy_free(&p);

  if (rc != 0)
    return 1;
  printf("kernel test: pass\n");
  return 0;
}
