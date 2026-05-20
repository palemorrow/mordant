#!/bin/sh
set -eu
out="${1:-src/syscalls.gen.c}"
hdr="${2:-src/syscalls.gen.h}"
tmp="$(mktemp)"
tmp2="$(mktemp)"
cc -E -dM -include asm/unistd_64.h - </dev/null \
  | sed -n 's/^#define __NR_\([a-z][a-z0-9_]*\) \([0-9][0-9]*\)$/\1 \2/p' \
  | sort -k1,1 > "$tmp"
n=$(wc -l < "$tmp" | tr -d ' ')
{
  printf 'const unsigned int mord_syscall_table_len = %s;\n' "$n"
} > "$tmp2"
{
  printf '#ifndef MORDANT_SYSCALLS_GEN_H\n'
  printf '#define MORDANT_SYSCALLS_GEN_H\n\n'
  printf 'struct mord_syscall_entry {\n'
  printf '  const char *name;\n'
  printf '  unsigned int nr;\n'
  printf '};\n\n'
  printf 'extern const struct mord_syscall_entry mord_syscall_table[];\n'
  printf 'extern const unsigned int mord_syscall_table_len;\n\n'
  printf '#endif\n'
} > "$hdr"
{
  printf '#include "syscalls.gen.h"\n\n'
  printf 'const struct mord_syscall_entry mord_syscall_table[] = {\n'
  while read -r name nr; do
    printf '  { "%s", %s },\n' "$name" "$nr"
  done < "$tmp"
  printf '};\n\n'
  cat "$tmp2"
} > "$out"
rm -f "$tmp" "$tmp2"
