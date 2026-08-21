#include "mordant.h"
#include "private.h"

#include <stdlib.h>
#include <string.h>

static const int SECCOMP_DATA_SIZE = (int)sizeof(struct seccomp_data);

static int check_abs_offset(unsigned k) {
  return (k % 4u) == 0 && k + 4u <= (unsigned)SECCOMP_DATA_SIZE;
}

static int valid_opcode(unsigned code) {
  switch (code) {
  case BPF_LD | BPF_W | BPF_ABS:
  case BPF_LD | BPF_IMM:
  case BPF_ALU | BPF_AND | BPF_K:
  case BPF_JMP | BPF_JEQ | BPF_K:
  case BPF_JMP | BPF_JGT | BPF_K:
  case BPF_JMP | BPF_JGE | BPF_K:
  case BPF_JMP | BPF_JA:
  case BPF_RET | BPF_K:
    return 1;
  default:
    return 0;
  }
}

int mord_validate(const mord_program *prog, mord_diaglist *diags) {
  size_t n = prog->count;
  int errors = 0;
  if (n == 0) {
    mord_diag_add(diags, 0, 0, "program is empty");
    return -1;
  }
  if (n > MORDANT_MAX_INSNS) {
    mord_diag_add(diags, 0, 0, "program has %zu instructions, limit is %d", n,
                  MORDANT_MAX_INSNS);
    return -1;
  }

  for (size_t i = 0; i < n; i++) {
    const mord_insn *ins = &prog->insns[i];
    if (!valid_opcode(ins->code)) {
      mord_diag_add(diags, 0, 0, "instruction %zu has unsupported opcode 0x%02x",
                    i, ins->code);
      errors++;
      continue;
    }
    switch (ins->code) {
    case BPF_LD | BPF_W | BPF_ABS:
      if (!check_abs_offset(ins->k)) {
        mord_diag_add(diags, 0, 0,
                      "instruction %zu loads from invalid offset %u", i, ins->k);
        errors++;
      }
      break;
    case BPF_JMP | BPF_JEQ | BPF_K:
    case BPF_JMP | BPF_JGT | BPF_K:
    case BPF_JMP | BPF_JGE | BPF_K: {
      size_t t = i + 1 + ins->jt;
      size_t f = i + 1 + ins->jf;
      if (t >= n) {
        mord_diag_add(diags, 0, 0,
                      "instruction %zu true target %zu out of range", i, t);
        errors++;
      }
      if (f >= n) {
        mord_diag_add(diags, 0, 0,
                      "instruction %zu false target %zu out of range", i, f);
        errors++;
      }
      break;
    }
    case BPF_JMP | BPF_JA: {
      size_t t = i + 1 + (size_t)ins->k;
      if (t >= n) {
        mord_diag_add(diags, 0, 0,
                      "instruction %zu jump target %zu out of range", i, t);
        errors++;
      }
      break;
    }
    case BPF_RET | BPF_K:
      if (!mord_is_supported_action(ins->k)) {
        mord_diag_add(diags, 0, 0,
                      "instruction %zu returns unsupported action 0x%08x", i,
                      ins->k);
        errors++;
      }
      break;
    default:
      break;
    }
  }

  if (prog->insns[n - 1].code != (BPF_RET | BPF_K)) {
    mord_diag_add(diags, 0, 0, "program does not end with a return instruction");
    errors++;
  }

  unsigned char *reach = calloc(n, 1);
  if (!reach) {
    mord_diag_add(diags, 0, 0, "out of memory during validation");
    return -1;
  }
  reach[0] = 1;
  for (size_t i = 0; i < n; i++) {
    if (!reach[i])
      continue;
    const mord_insn *ins = &prog->insns[i];
    switch (ins->code) {
    case BPF_RET | BPF_K:
      break;
    case BPF_JMP | BPF_JA: {
      size_t t = i + 1 + (size_t)ins->k;
      if (t < n)
        reach[t] = 1;
      break;
    }
    case BPF_JMP | BPF_JEQ | BPF_K:
    case BPF_JMP | BPF_JGT | BPF_K:
    case BPF_JMP | BPF_JGE | BPF_K: {
      size_t t = i + 1 + ins->jt;
      size_t f = i + 1 + ins->jf;
      if (i + 1 < n)
        reach[i + 1] = 1;
      if (t < n)
        reach[t] = 1;
      if (f < n)
        reach[f] = 1;
      break;
    }
    default:
      if (i + 1 < n)
        reach[i + 1] = 1;
      break;
    }
  }
  if (reach[n - 1] && prog->insns[n - 1].code != (BPF_RET | BPF_K)) {
    mord_diag_add(diags, 0, 0, "reachable path falls past the final instruction");
    errors++;
  }
  free(reach);

  return errors ? -1 : 0;
}
