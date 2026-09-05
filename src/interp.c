#include "mordant.h"

#include <string.h>

static mord_u32 read_le32(const unsigned char *p) {
  return (mord_u32)p[0] | ((mord_u32)p[1] << 8) | ((mord_u32)p[2] << 16) |
         ((mord_u32)p[3] << 24);
}

static void write_le32(unsigned char *p, mord_u32 v) {
  p[0] = (unsigned char)(v & 0xff);
  p[1] = (unsigned char)((v >> 8) & 0xff);
  p[2] = (unsigned char)((v >> 16) & 0xff);
  p[3] = (unsigned char)((v >> 24) & 0xff);
}

static void write_le64(unsigned char *p, mord_u64 v) {
  for (int i = 0; i < 8; i++)
    p[i] = (unsigned char)((v >> (8 * i)) & 0xff);
}

int mord_eval_program(const mord_program *prog, const mord_context *ctx,
                      mord_u32 *action, mord_diaglist *diags) {
  unsigned char data[64];
  memset(data, 0, sizeof(data));
  write_le32(data + 0, (mord_u32)ctx->nr);
  write_le32(data + 4, ctx->arch);
  write_le64(data + 8, ctx->ip);
  for (int i = 0; i < 6; i++)
    write_le64(data + 16 + 8 * i, ctx->args[i]);

  mord_u32 a = 0;
  size_t pc = 0;
  size_t steps = 0;
  while (pc < prog->count) {
    if (++steps > prog->count + 1) {
      mord_diag_add(diags, 0, 0, "program did not terminate");
      return -1;
    }
    const mord_insn *ins = &prog->insns[pc];
    size_t next;
    switch (ins->code) {
    case BPF_LD | BPF_W | BPF_ABS:
      if (ins->k + 4u > sizeof(struct seccomp_data)) {
        mord_diag_add(diags, 0, 0, "absolute load out of range");
        return -1;
      }
      a = read_le32(data + ins->k);
      next = pc + 1;
      break;
    case BPF_LD | BPF_IMM:
      a = ins->k;
      next = pc + 1;
      break;
    case BPF_ALU | BPF_AND | BPF_K:
      a = a & ins->k;
      next = pc + 1;
      break;
    case BPF_JMP | BPF_JEQ | BPF_K:
      next = pc + 1 + (a == ins->k ? ins->jt : ins->jf);
      break;
    case BPF_JMP | BPF_JGT | BPF_K:
      next = pc + 1 + (a > ins->k ? ins->jt : ins->jf);
      break;
    case BPF_JMP | BPF_JGE | BPF_K:
      next = pc + 1 + (a >= ins->k ? ins->jt : ins->jf);
      break;
    case BPF_JMP | BPF_JA:
      next = pc + 1 + (size_t)ins->k;
      break;
    case BPF_RET | BPF_K:
      *action = ins->k;
      return 0;
    default:
      mord_diag_add(diags, 0, 0, "unsupported instruction at pc %zu", pc);
      return -1;
    }
    if (next >= prog->count) {
      mord_diag_add(diags, 0, 0, "control escaped program at pc %zu", pc);
      return -1;
    }
    pc = next;
  }
  mord_diag_add(diags, 0, 0, "program did not return");
  return -1;
}
