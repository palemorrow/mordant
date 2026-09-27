#define _GNU_SOURCE
#include "install.h"

#include <errno.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <unistd.h>

#include <linux/filter.h>
#include <linux/seccomp.h>

int mordant_install_program(const struct sock_filter *insns, size_t count,
                            mord_diaglist *diags) {
  if (!insns || count == 0) {
    mord_diag_add(diags, 0, 0, "cannot install an empty filter");
    return -1;
  }
  if (count > BPF_MAXINSNS) {
    mord_diag_add(diags, 0, 0,
                  "filter has %zu instructions, kernel limit is %d", count,
                  BPF_MAXINSNS);
    return -1;
  }
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
    mord_diag_add(diags, 0, 0, "prctl(PR_SET_NO_NEW_PRIVS) failed: %s",
                  strerror(errno));
    return -1;
  }
  struct sock_fprog prog;
  prog.len = (unsigned short)count;
  prog.filter = (struct sock_filter *)insns;
  if (syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &prog) != 0) {
    mord_diag_add(diags, 0, 0, "seccomp(SECCOMP_SET_MODE_FILTER) failed: %s",
                  strerror(errno));
    return -1;
  }
  return 0;
}
