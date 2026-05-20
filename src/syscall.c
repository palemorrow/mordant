#include "mordant.h"
#include "syscalls.gen.h"

#include <string.h>

int mord_syscall_lookup(const char *name, mord_u32 *out) {
  unsigned lo = 0;
  unsigned hi = mord_syscall_table_len;
  while (lo < hi) {
    unsigned mid = lo + (hi - lo) / 2;
    int cmp = strcmp(name, mord_syscall_table[mid].name);
    if (cmp == 0) {
      *out = mord_syscall_table[mid].nr;
      return 0;
    }
    if (cmp < 0)
      hi = mid;
    else
      lo = mid + 1;
  }
  return -1;
}

const char *mord_syscall_name(mord_u32 nr) {
  for (unsigned i = 0; i < mord_syscall_table_len; i++)
    if (mord_syscall_table[i].nr == nr)
      return mord_syscall_table[i].name;
  return NULL;
}
