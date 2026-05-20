#ifndef MORDANT_H
#define MORDANT_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>

#define MORDANT_FILTER_MAGIC 0x3146444dU
#define MORDANT_FILTER_VERSION 1U
#define MORDANT_MAX_INSNS BPF_MAXINSNS

#ifndef SECCOMP_RET_KILL_PROCESS
#define SECCOMP_RET_KILL_PROCESS 0x80000000U
#endif

#define MORDANT_X32_SYSCALL_BIT 0x40000000U

typedef unsigned int mord_u32;
typedef uint64_t mord_u64;

typedef struct {
  unsigned line;
  unsigned col;
  char message[256];
} mord_diag;

typedef struct {
  mord_diag *items;
  size_t count;
  size_t cap;
} mord_diaglist;

void mord_diags_init(mord_diaglist *d);
void mord_diags_free(mord_diaglist *d);
void mord_diag_add(mord_diaglist *d, unsigned line, unsigned col,
                   const char *fmt, ...);

typedef enum {
  MORD_P_TRUE,
  MORD_P_EQ,
  MORD_P_NE,
  MORD_P_LT,
  MORD_P_LE,
  MORD_P_GT,
  MORD_P_GE,
  MORD_P_MASK_ZERO,
  MORD_P_MASK_EQ,
  MORD_P_AND,
  MORD_P_OR
} mord_pred_kind;

typedef struct mord_pred {
  mord_pred_kind kind;
  unsigned arg;
  mord_u64 value;
  mord_u64 mask;
  struct mord_pred *left;
  struct mord_pred *right;
} mord_pred;

typedef struct {
  mord_u32 ret;
} mord_action;

typedef struct {
  mord_u32 nr;
  mord_pred *pred;
  mord_action action;
} mord_rule;

typedef struct {
  int has_arch;
  int has_default;
  mord_u32 arch;
  mord_action default_action;
  mord_rule *rules;
  size_t nrules;
  char source[256];
} mord_policy;

typedef struct sock_filter mord_insn;

typedef struct {
  mord_insn *insns;
  size_t count;
  mord_u32 arch;
} mord_program;

typedef struct {
  int64_t nr;
  mord_u32 arch;
  mord_u64 ip;
  mord_u64 args[6];
} mord_context;

int mord_parse_file(const char *path, mord_policy *out, mord_diaglist *diags);
int mord_parse_string(const char *src, const char *name, mord_policy *out,
                      mord_diaglist *diags);
void mord_policy_free(mord_policy *p);

int mord_compile(const mord_policy *p, mord_program *out, mord_diaglist *diags);
void mord_program_free(mord_program *prog);

int mord_validate(const mord_program *prog, mord_diaglist *diags);

int mord_program_write(const mord_program *prog, const char *path,
                       mord_diaglist *diags);
int mord_program_read(const char *path, mord_program *out, mord_diaglist *diags);
int mord_program_write_file(FILE *f, const mord_program *prog,
                            mord_diaglist *diags);
int mord_program_read_file(FILE *f, mord_program *out, mord_diaglist *diags);

void mord_program_dump(FILE *f, const mord_program *prog);

int mord_eval_policy(const mord_policy *p, const mord_context *ctx,
                     mord_u32 *action);
int mord_eval_program(const mord_program *prog, const mord_context *ctx,
                      mord_u32 *action, mord_diaglist *diags);

int mord_syscall_lookup(const char *name, mord_u32 *out);
const char *mord_syscall_name(mord_u32 nr);

mord_u32 mord_action_allow(void);
mord_u32 mord_action_kill_process(void);
mord_u32 mord_action_errno(mord_u32 err);

#endif
