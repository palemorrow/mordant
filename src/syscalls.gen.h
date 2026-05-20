#ifndef MORDANT_SYSCALLS_GEN_H
#define MORDANT_SYSCALLS_GEN_H

struct mord_syscall_entry {
  const char *name;
  unsigned int nr;
};

extern const struct mord_syscall_entry mord_syscall_table[];
extern const unsigned int mord_syscall_table_len;

#endif
