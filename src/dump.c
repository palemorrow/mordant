#include "mordant.h"

static const char *field_name(unsigned k) {
  switch (k) {
  case 0:
    return "nr";
  case 4:
    return "arch";
  case 8:
    return "ip.lo";
  case 12:
    return "ip.hi";
  default:
    break;
  }
  return "?";
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

void mord_program_dump(FILE *f, const mord_program *prog) {
  fprintf(f, "arch 0x%08x  instructions %zu\n", prog->arch, prog->count);
  for (size_t i = 0; i < prog->count; i++) {
    const mord_insn *ins = &prog->insns[i];
    fprintf(f, "%4zu: ", i);
    switch (ins->code) {
    case BPF_LD | BPF_W | BPF_ABS:
      if (ins->k >= 16 && ins->k < 64)
        fprintf(f, "ld   [%u] arg%u.%s", ins->k, (ins->k - 16) / 8,
                (ins->k % 8 == 0) ? "lo" : "hi");
      else
        fprintf(f, "ld   [%u] %s", ins->k, field_name(ins->k));
      break;
    case BPF_LD | BPF_IMM:
      fprintf(f, "ld   #0x%08x", ins->k);
      break;
    case BPF_ALU | BPF_AND | BPF_K:
      fprintf(f, "and  #0x%08x", ins->k);
      break;
    case BPF_JMP | BPF_JEQ | BPF_K:
      fprintf(f, "jeq  #0x%08x -> %zu, %zu", ins->k,
              i + 1 + ins->jt, i + 1 + ins->jf);
      break;
    case BPF_JMP | BPF_JGT | BPF_K:
      fprintf(f, "jgt  #0x%08x -> %zu, %zu", ins->k,
              i + 1 + ins->jt, i + 1 + ins->jf);
      break;
    case BPF_JMP | BPF_JGE | BPF_K:
      fprintf(f, "jge  #0x%08x -> %zu, %zu", ins->k,
              i + 1 + ins->jt, i + 1 + ins->jf);
      break;
    case BPF_JMP | BPF_JA:
      fprintf(f, "ja   -> %zu", i + 1 + (size_t)ins->k);
      break;
    case BPF_RET | BPF_K:
      fprintf(f, "ret  ");
      print_action(f, ins->k);
      break;
    default:
      fprintf(f, "?    code=0x%04x jt=%u jf=%u k=0x%08x", ins->code, ins->jt,
              ins->jf, ins->k);
      break;
    }
    fputc('\n', f);
  }
}
