#define _GNU_SOURCE
#include "lexer.h"
#include "private.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  mord_lexer lx;
  mord_token cur;
  mord_diaglist *diags;
  int failed;
} mord_parser;

static void advance(mord_parser *ps) {
  if (ps->failed)
    return;
  if (mord_lex(&ps->lx, &ps->cur) < 0)
    ps->failed = 1;
}

static int at(mord_parser *ps, mord_tok_kind k) {
  return !ps->failed && ps->cur.kind == k;
}

static void error_here(mord_parser *ps, const char *msg) {
  if (ps->failed)
    return;
  mord_diag_add(ps->diags, ps->cur.line, ps->cur.col, "%s", msg);
  ps->failed = 1;
}

static int expect(mord_parser *ps, mord_tok_kind k, const char *what) {
  if (at(ps, k)) {
    advance(ps);
    return 1;
  }
  error_here(ps, what);
  return 0;
}

static int parse_action(mord_parser *ps, mord_action *out) {
  if (at(ps, TOK_ALLOW)) {
    advance(ps);
    out->ret = mord_action_allow();
    return 1;
  }
  if (at(ps, TOK_KILL)) {
    advance(ps);
    out->ret = mord_action_kill_process();
    return 1;
  }
  if (at(ps, TOK_ERRNO)) {
    advance(ps);
    if (!at(ps, TOK_NUMBER)) {
      error_here(ps, "expected errno value after 'errno'");
      return 0;
    }
    mord_u64 v = ps->cur.num;
    unsigned line = ps->cur.line;
    unsigned col = ps->cur.col;
    advance(ps);
    if (v < 1 || v > SECCOMP_RET_DATA) {
      mord_diag_add(ps->diags, line, col,
                    "errno value %llu outside permitted range 1..%u",
                    (unsigned long long)v, (unsigned)SECCOMP_RET_DATA);
      ps->failed = 1;
      return 0;
    }
    out->ret = mord_action_errno((mord_u32)v);
    return 1;
  }
  error_here(ps, "expected action 'allow', 'kill' or 'errno N'");
  return 0;
}

static int parse_syscall(mord_parser *ps, mord_u32 *out) {
  if (at(ps, TOK_IDENT)) {
    char name[128];
    size_t n = ps->cur.len < sizeof(name) - 1 ? ps->cur.len : sizeof(name) - 1;
    memcpy(name, ps->cur.text, n);
    name[n] = '\0';
    unsigned line = ps->cur.line;
    unsigned col = ps->cur.col;
    mord_u32 nr;
    if (mord_syscall_lookup(name, &nr) != 0) {
      mord_diag_add(ps->diags, line, col, "unknown syscall '%s'", name);
      ps->failed = 1;
      return 0;
    }
    advance(ps);
    *out = nr;
    return 1;
  }
  if (at(ps, TOK_NUMBER)) {
    mord_u64 v = ps->cur.num;
    unsigned line = ps->cur.line;
    unsigned col = ps->cur.col;
    advance(ps);
    if (v & MORDANT_X32_SYSCALL_BIT) {
      mord_diag_add(ps->diags, line, col,
                    "syscall number sets the x32 bit and is not accepted");
      ps->failed = 1;
      return 0;
    }
    if (v > 0x3fffffffULL) {
      mord_diag_add(ps->diags, line, col,
                    "syscall number %llu outside permitted range",
                    (unsigned long long)v);
      ps->failed = 1;
      return 0;
    }
    *out = (mord_u32)v;
    return 1;
  }
  error_here(ps, "expected syscall name or number");
  return 0;
}

static mord_pred *parse_or(mord_parser *ps);

static mord_pred *parse_atom(mord_parser *ps) {
  if (at(ps, TOK_LPAREN)) {
    advance(ps);
    mord_pred *node = parse_or(ps);
    if (!node)
      return NULL;
    if (!expect(ps, TOK_RPAREN, "expected ')'"))
      return NULL;
    return node;
  }
  if (at(ps, TOK_ARG)) {
    unsigned arg = ps->cur.arg;
    unsigned line = ps->cur.line;
    unsigned col = ps->cur.col;
    advance(ps);
    if (arg > 5) {
      mord_diag_add(ps->diags, line, col,
                    "argument index %u out of range 0..5", arg);
      ps->failed = 1;
      return NULL;
    }
    if (at(ps, TOK_AMP)) {
      advance(ps);
      if (!at(ps, TOK_NUMBER)) {
        error_here(ps, "expected bitmask constant");
        return NULL;
      }
      mord_u64 mask = ps->cur.num;
      unsigned mline = ps->cur.line;
      unsigned mcol = ps->cur.col;
      advance(ps);
      if (!at(ps, TOK_EQ)) {
        error_here(ps, "bitmask predicate requires '=='");
        return NULL;
      }
      advance(ps);
      if (!at(ps, TOK_NUMBER)) {
        error_here(ps, "expected comparison constant after '=='");
        return NULL;
      }
      mord_u64 val = ps->cur.num;
      advance(ps);
      if (val & ~mask) {
        mord_diag_add(ps->diags, mline, mcol,
                      "masked comparison value has bits outside the mask");
        ps->failed = 1;
        return NULL;
      }
      mord_pred_kind kind = (val == 0) ? MORD_P_MASK_ZERO : MORD_P_MASK_EQ;
      mord_pred *node = mord_pred_new(kind);
      if (!node) {
        ps->failed = 1;
        return NULL;
      }
      node->arg = arg;
      node->mask = mask;
      node->value = val;
      return node;
    }
    mord_pred_kind kind;
    switch (ps->cur.kind) {
    case TOK_EQ:
      kind = MORD_P_EQ;
      break;
    case TOK_NE:
      kind = MORD_P_NE;
      break;
    case TOK_LT:
      kind = MORD_P_LT;
      break;
    case TOK_LE:
      kind = MORD_P_LE;
      break;
    case TOK_GT:
      kind = MORD_P_GT;
      break;
    case TOK_GE:
      kind = MORD_P_GE;
      break;
    default:
      error_here(ps, "expected comparison operator after argument");
      return NULL;
    }
    advance(ps);
    if (!at(ps, TOK_NUMBER)) {
      error_here(ps, "expected comparison constant");
      return NULL;
    }
    mord_u64 val = ps->cur.num;
    advance(ps);
    mord_pred *node = mord_pred_new(kind);
    if (!node) {
      ps->failed = 1;
      return NULL;
    }
    node->arg = arg;
    node->value = val;
    return node;
  }
  error_here(ps, "expected predicate");
  return NULL;
}

static mord_pred *parse_and(mord_parser *ps, int *used_and) {
  mord_pred *node = parse_atom(ps);
  if (!node)
    return NULL;
  while (at(ps, TOK_ANDAND)) {
    advance(ps);
    mord_pred *rhs = parse_atom(ps);
    if (!rhs) {
      mord_pred_free(node);
      return NULL;
    }
    mord_pred *n = mord_pred_new(MORD_P_AND);
    if (!n) {
      mord_pred_free(node);
      mord_pred_free(rhs);
      ps->failed = 1;
      return NULL;
    }
    n->left = node;
    n->right = rhs;
    node = n;
    *used_and = 1;
  }
  return node;
}

static mord_pred *parse_or(mord_parser *ps) {
  int used = 0;
  mord_pred *node = parse_and(ps, &used);
  if (!node)
    return NULL;
  while (at(ps, TOK_OROR)) {
    if (used) {
      error_here(ps, "ambiguous boolean expression, use parentheses when "
                     "mixing '&&' and '||'");
      mord_pred_free(node);
      return NULL;
    }
    advance(ps);
    int used2 = 0;
    mord_pred *rhs = parse_and(ps, &used2);
    if (!rhs) {
      mord_pred_free(node);
      return NULL;
    }
    if (used2) {
      error_here(ps, "ambiguous boolean expression, use parentheses when "
                     "mixing '&&' and '||'");
      mord_pred_free(node);
      mord_pred_free(rhs);
      return NULL;
    }
    mord_pred *n = mord_pred_new(MORD_P_OR);
    if (!n) {
      mord_pred_free(node);
      mord_pred_free(rhs);
      ps->failed = 1;
      return NULL;
    }
    n->left = node;
    n->right = rhs;
    node = n;
  }
  return node;
}

static int policy_add_rule(mord_policy *pol, mord_rule rule) {
  mord_rule *rules = realloc(pol->rules, (pol->nrules + 1) * sizeof(*rules));
  if (!rules)
    return -1;
  pol->rules = rules;
  pol->rules[pol->nrules++] = rule;
  return 0;
}

static int parse_program(mord_parser *ps, mord_policy *pol) {
  while (!ps->failed) {
    while (at(ps, TOK_NEWLINE))
      advance(ps);
    if (at(ps, TOK_EOF))
      break;
    if (at(ps, TOK_ARCH)) {
      advance(ps);
      if (!at(ps, TOK_IDENT)) {
        error_here(ps, "expected architecture name");
        return -1;
      }
      unsigned line = ps->cur.line;
      unsigned col = ps->cur.col;
      int is64 = ps->cur.len == 6 && memcmp(ps->cur.text, "x86_64", 6) == 0;
      advance(ps);
      if (!is64) {
        mord_diag_add(ps->diags, line, col,
                      "unsupported architecture, only 'x86_64' is accepted");
        ps->failed = 1;
        return -1;
      }
      if (pol->has_arch) {
        mord_diag_add(ps->diags, line, col,
                      "duplicate architecture declaration");
        ps->failed = 1;
        return -1;
      }
      pol->has_arch = 1;
      pol->arch = AUDIT_ARCH_X86_64;
    } else if (at(ps, TOK_DEFAULT)) {
      unsigned line = ps->cur.line;
      unsigned col = ps->cur.col;
      advance(ps);
      mord_action act;
      if (!parse_action(ps, &act))
        return -1;
      if (pol->has_default) {
        mord_diag_add(ps->diags, line, col, "duplicate default action");
        ps->failed = 1;
        return -1;
      }
      pol->has_default = 1;
      pol->default_action = act;
    } else if (at(ps, TOK_ALLOW) || at(ps, TOK_KILL) || at(ps, TOK_ERRNO)) {
      mord_action act;
      if (!parse_action(ps, &act))
        return -1;
      mord_u32 nr = 0;
      if (!parse_syscall(ps, &nr))
        return -1;
      mord_pred *pred = NULL;
      if (at(ps, TOK_IF)) {
        advance(ps);
        pred = parse_or(ps);
        if (!pred)
          return -1;
      }
      mord_rule rule;
      rule.nr = nr;
      rule.pred = pred;
      rule.action = act;
      if (policy_add_rule(pol, rule) != 0) {
        mord_pred_free(pred);
        ps->failed = 1;
        return -1;
      }
    } else {
      error_here(ps, "expected 'arch', 'default' or a rule");
      return -1;
    }
    if (!at(ps, TOK_NEWLINE) && !at(ps, TOK_EOF)) {
      error_here(ps, "unexpected token after statement");
      return -1;
    }
  }
  if (ps->failed)
    return -1;
  if (!pol->has_arch) {
    mord_diag_add(ps->diags, 0, 0, "policy has no architecture declaration");
    return -1;
  }
  if (!pol->has_default) {
    mord_diag_add(ps->diags, 0, 0, "policy has no default action");
    return -1;
  }
  return 0;
}

int mord_parse_string(const char *src, const char *name, mord_policy *out,
                      mord_diaglist *diags) {
  mord_parser ps;
  memset(&ps, 0, sizeof(ps));
  ps.diags = diags;
  mord_lexer_init(&ps.lx, src, diags);
  memset(out, 0, sizeof(*out));
  if (name) {
    strncpy(out->source, name, sizeof(out->source) - 1);
    out->source[sizeof(out->source) - 1] = '\0';
  }
  advance(&ps);
  if (parse_program(&ps, out) != 0 || ps.failed) {
    mord_policy_free(out);
    return -1;
  }
  return 0;
}

int mord_parse_file(const char *path, mord_policy *out, mord_diaglist *diags) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    mord_diag_add(diags, 0, 0, "cannot open '%s'", path);
    return -1;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    mord_diag_add(diags, 0, 0, "cannot seek '%s'", path);
    return -1;
  }
  long len = ftell(f);
  if (len < 0) {
    fclose(f);
    mord_diag_add(diags, 0, 0, "cannot size '%s'", path);
    return -1;
  }
  if (fseek(f, 0, SEEK_SET) != 0) {
    fclose(f);
    mord_diag_add(diags, 0, 0, "cannot seek '%s'", path);
    return -1;
  }
  char *buf = malloc((size_t)len + 1);
  if (!buf) {
    fclose(f);
    mord_diag_add(diags, 0, 0, "out of memory reading '%s'", path);
    return -1;
  }
  size_t got = fread(buf, 1, (size_t)len, f);
  fclose(f);
  if (got != (size_t)len) {
    free(buf);
    mord_diag_add(diags, 0, 0, "short read on '%s'", path);
    return -1;
  }
  buf[len] = '\0';
  int rc = mord_parse_string(buf, path, out, diags);
  free(buf);
  return rc;
}
