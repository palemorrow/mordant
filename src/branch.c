#include "lower.h"

#include <stdlib.h>
#include <string.h>

static void set_insn(mord_insn *ins, unsigned code, unsigned jt, unsigned jf,
                     mord_u32 k) {
  ins->code = (uint16_t)code;
  ins->jt = (uint8_t)jt;
  ins->jf = (uint8_t)jf;
  ins->k = k;
}

static int is_cond(mop_kind op) {
  return op == MOP_JEQ || op == MOP_JGT || op == MOP_JGE;
}

static unsigned cond_code(mop_kind op) {
  switch (op) {
  case MOP_JEQ:
    return BPF_JMP | BPF_JEQ | BPF_K;
  case MOP_JGT:
    return BPF_JMP | BPF_JGT | BPF_K;
  case MOP_JGE:
    return BPF_JMP | BPF_JGE | BPF_K;
  default:
    return 0;
  }
}

int mord_resolve(const mopbuf *in, mord_program *out, mord_diaglist *diags) {
  out->insns = NULL;
  out->count = 0;
  out->arch = 0;

  size_t n = in->n;
  if (n == 0) {
    mord_diag_add(diags, 0, 0, "empty program");
    return -1;
  }

  unsigned char *tramp = calloc(n ? n : 1, 1);
  size_t *label_pc = malloc((size_t)(in->next_label ? in->next_label : 1) *
                            sizeof(size_t));
  size_t *cond_pc = malloc(n * sizeof(size_t));
  if (!tramp || !label_pc || !cond_pc) {
    free(tramp);
    free(label_pc);
    free(cond_pc);
    mord_diag_add(diags, 0, 0, "out of memory during layout");
    return -1;
  }

  int changed = 1;
  size_t total = 0;
  while (changed) {
    changed = 0;
    for (int i = 0; i < in->next_label; i++)
      label_pc[i] = (size_t)-1;
    size_t pc = 0;
    for (size_t i = 0; i < n; i++) {
      const mop *m = &in->ops[i];
      if (m->op == MOP_LABEL)
        label_pc[m->label] = pc;
      else if (is_cond(m->op)) {
        cond_pc[i] = pc;
        pc += tramp[i] ? 3u : 1u;
      } else
        pc++;
    }
    total = pc;
    for (size_t i = 0; i < n; i++) {
      const mop *m = &in->ops[i];
      if (!is_cond(m->op) || tramp[i])
        continue;
      size_t base = cond_pc[i] + 1;
      size_t dt = label_pc[m->tlabel];
      size_t df = label_pc[m->flabel];
      if (dt == (size_t)-1 || df == (size_t)-1) {
        mord_diag_add(diags, 0, 0, "unresolved branch label");
        free(tramp);
        free(label_pc);
        free(cond_pc);
        return -1;
      }
      if (dt < base || df < base || dt - base > 255 || df - base > 255) {
        tramp[i] = 1;
        changed = 1;
      }
    }
  }

  for (int i = 0; i < in->next_label; i++) {
    if (label_pc[i] == (size_t)-1) {
      mord_diag_add(diags, 0, 0, "label %d defined but never reached", i);
      free(tramp);
      free(label_pc);
      free(cond_pc);
      return -1;
    }
  }

  if (total > MORDANT_MAX_INSNS) {
    mord_diag_add(diags, 0, 0,
                  "program requires %zu instructions, limit is %d", total,
                  MORDANT_MAX_INSNS);
    free(tramp);
    free(label_pc);
    free(cond_pc);
    return -1;
  }

  mord_insn *insns = calloc(total, sizeof(*insns));
  if (!insns) {
    free(tramp);
    free(label_pc);
    free(cond_pc);
    mord_diag_add(diags, 0, 0, "out of memory during layout");
    return -1;
  }

  size_t e = 0;
  for (size_t i = 0; i < n; i++) {
    const mop *m = &in->ops[i];
    switch (m->op) {
    case MOP_LABEL:
      break;
    case MOP_LD_ABS:
      set_insn(&insns[e++], BPF_LD | BPF_W | BPF_ABS, 0, 0, m->k);
      break;
    case MOP_LD_IMM:
      set_insn(&insns[e++], BPF_LD | BPF_IMM, 0, 0, m->k);
      break;
    case MOP_AND_IMM:
      set_insn(&insns[e++], BPF_ALU | BPF_AND | BPF_K, 0, 0, m->k);
      break;
    case MOP_RET:
      set_insn(&insns[e++], BPF_RET | BPF_K, 0, 0, m->k);
      break;
    case MOP_JA: {
      size_t target = label_pc[m->label];
      size_t base = e + 1;
      if (target < base) {
        mord_diag_add(diags, 0, 0, "backward unconditional jump");
        goto fail;
      }
      set_insn(&insns[e++], BPF_JMP | BPF_JA, 0, 0,
               (mord_u32)(target - base));
      break;
    }
    case MOP_JEQ:
    case MOP_JGT:
    case MOP_JGE: {
      unsigned code = cond_code(m->op);
      size_t base = e + 1;
      if (!tramp[i]) {
        size_t dt = label_pc[m->tlabel];
        size_t df = label_pc[m->flabel];
        if (dt < base || df < base || dt - base > 255 || df - base > 255) {
          mord_diag_add(diags, 0, 0, "conditional branch out of range");
          goto fail;
        }
        set_insn(&insns[e++], code, (unsigned)(dt - base), (unsigned)(df - base),
                 m->k);
      } else {
        size_t jt = label_pc[m->tlabel];
        size_t jf = label_pc[m->flabel];
        if (jt < base + 1 || jf < base + 2) {
          mord_diag_add(diags, 0, 0, "backward trampoline jump");
          goto fail;
        }
        set_insn(&insns[e++], code, 0, 1, m->k);
        set_insn(&insns[e++], BPF_JMP | BPF_JA, 0, 0, (mord_u32)(jt - (base + 1)));
        set_insn(&insns[e++], BPF_JMP | BPF_JA, 0, 0, (mord_u32)(jf - (base + 2)));
      }
      break;
    }
    default:
      mord_diag_add(diags, 0, 0, "internal error, unknown lowering op");
      goto fail;
    }
  }

  free(tramp);
  free(label_pc);
  free(cond_pc);
  out->insns = insns;
  out->count = e;
  return 0;

fail:
  free(insns);
  free(tramp);
  free(label_pc);
  free(cond_pc);
  return -1;
}

void mord_program_free(mord_program *prog) {
  free(prog->insns);
  prog->insns = NULL;
  prog->count = 0;
}
