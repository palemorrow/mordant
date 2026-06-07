#include "lexer.h"

#include <string.h>

static int ident_start(int c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

static int ident_part(int c) {
  return ident_start(c) || (c >= '0' && c <= '9');
}

void mord_lexer_init(mord_lexer *lx, const char *src, mord_diaglist *diags) {
  lx->src = src;
  lx->pos = 0;
  lx->line = 1;
  lx->col = 1;
  lx->diags = diags;
  lx->failed = 0;
}

static int peek(mord_lexer *lx) { return (unsigned char)lx->src[lx->pos]; }

static int next_ch(mord_lexer *lx) {
  int c = (unsigned char)lx->src[lx->pos];
  if (c == '\0')
    return 0;
  lx->pos++;
  if (c == '\n') {
    lx->line++;
    lx->col = 1;
  } else {
    lx->col++;
  }
  return c;
}

static int match_kw(const char *text, size_t len, const char *kw) {
  size_t n = strlen(kw);
  return len == n && memcmp(text, kw, n) == 0;
}

static int lex_number(mord_lexer *lx, mord_token *tok, unsigned line,
                      unsigned col) {
  const char *start = lx->src + lx->pos;
  size_t len;
  mord_u64 value = 0;
  int base = 10;
  int c = peek(lx);
  if (c == '0' && (lx->src[lx->pos + 1] == 'x' || lx->src[lx->pos + 1] == 'X')) {
    base = 16;
    next_ch(lx);
    next_ch(lx);
    if (!((peek(lx) >= '0' && peek(lx) <= '9') ||
          (peek(lx) >= 'a' && peek(lx) <= 'f') ||
          (peek(lx) >= 'A' && peek(lx) <= 'F'))) {
      mord_diag_add(lx->diags, line, col, "malformed hexadecimal constant");
      return -1;
    }
  } else if (c == '0' &&
             (lx->src[lx->pos + 1] == 'b' || lx->src[lx->pos + 1] == 'B')) {
    base = 2;
    next_ch(lx);
    next_ch(lx);
    if (!(peek(lx) == '0' || peek(lx) == '1')) {
      mord_diag_add(lx->diags, line, col, "malformed binary constant");
      return -1;
    }
  }
  for (;;) {
    int d = peek(lx);
    int digit = -1;
    if (d >= '0' && d <= '9')
      digit = d - '0';
    else if (base == 16 && d >= 'a' && d <= 'f')
      digit = d - 'a' + 10;
    else if (base == 16 && d >= 'A' && d <= 'F')
      digit = d - 'A' + 10;
    else if (base == 2 && (d == '0' || d == '1'))
      digit = d - '0';
    if (digit < 0 || digit >= base)
      break;
    if (value > (UINT64_MAX - (mord_u64)digit) / (mord_u64)base) {
      mord_diag_add(lx->diags, line, col, "integer constant exceeds 64 bits");
      return -1;
    }
    value = value * (mord_u64)base + (mord_u64)digit;
    next_ch(lx);
  }
  len = (size_t)((lx->src + lx->pos) - start);
  tok->kind = TOK_NUMBER;
  tok->text = start;
  tok->len = len;
  tok->num = value;
  tok->line = line;
  tok->col = col;
  return 0;
}

int mord_lex(mord_lexer *lx, mord_token *tok) {
  for (;;) {
    int c = peek(lx);
    if (c == ' ' || c == '\t' || c == '\r') {
      next_ch(lx);
      continue;
    }
    if (c == '#') {
      while (peek(lx) != '\n' && peek(lx) != '\0')
        next_ch(lx);
      continue;
    }
    break;
  }

  unsigned line = lx->line;
  unsigned col = lx->col;
  int c = peek(lx);

  if (c == '\0') {
    tok->kind = TOK_EOF;
    tok->line = line;
    tok->col = col;
    return 0;
  }
  if (c == '\n') {
    next_ch(lx);
    tok->kind = TOK_NEWLINE;
    tok->line = line;
    tok->col = col;
    return 0;
  }
  if (c >= '0' && c <= '9')
    return lex_number(lx, tok, line, col);
  if (ident_start(c)) {
    const char *start = lx->src + lx->pos;
    while (ident_part(peek(lx)))
      next_ch(lx);
    size_t len = (size_t)((lx->src + lx->pos) - start);
    tok->text = start;
    tok->len = len;
    tok->line = line;
    tok->col = col;
    if (len > 3 && memcmp(start, "arg", 3) == 0) {
      size_t i = 3;
      mord_u64 idx = 0;
      int ok = 1;
      for (; i < len; i++) {
        if (start[i] < '0' || start[i] > '9') {
          ok = 0;
          break;
        }
        idx = idx * 10 + (mord_u64)(start[i] - '0');
      }
      if (ok) {
        tok->kind = TOK_ARG;
        tok->arg = (unsigned)idx;
        return 0;
      }
    }
    if (match_kw(start, len, "arch"))
      tok->kind = TOK_ARCH;
    else if (match_kw(start, len, "default"))
      tok->kind = TOK_DEFAULT;
    else if (match_kw(start, len, "allow"))
      tok->kind = TOK_ALLOW;
    else if (match_kw(start, len, "kill"))
      tok->kind = TOK_KILL;
    else if (match_kw(start, len, "errno"))
      tok->kind = TOK_ERRNO;
    else if (match_kw(start, len, "if"))
      tok->kind = TOK_IF;
    else
      tok->kind = TOK_IDENT;
    return 0;
  }

  next_ch(lx);
  int d = peek(lx);
  switch (c) {
  case '=':
    if (d == '=') {
      next_ch(lx);
      tok->kind = TOK_EQ;
      break;
    }
    mord_diag_add(lx->diags, line, col, "expected '=='");
    return -1;
  case '!':
    if (d == '=') {
      next_ch(lx);
      tok->kind = TOK_NE;
      break;
    }
    mord_diag_add(lx->diags, line, col, "expected '!='");
    return -1;
  case '<':
    if (d == '=') {
      next_ch(lx);
      tok->kind = TOK_LE;
    } else
      tok->kind = TOK_LT;
    break;
  case '>':
    if (d == '=') {
      next_ch(lx);
      tok->kind = TOK_GE;
    } else
      tok->kind = TOK_GT;
    break;
  case '&':
    if (d == '&') {
      next_ch(lx);
      tok->kind = TOK_ANDAND;
    } else
      tok->kind = TOK_AMP;
    break;
  case '|':
    if (d == '|') {
      next_ch(lx);
      tok->kind = TOK_OROR;
    } else {
      mord_diag_add(lx->diags, line, col, "expected '||'");
      return -1;
    }
    break;
  case '(':
    tok->kind = TOK_LPAREN;
    break;
  case ')':
    tok->kind = TOK_RPAREN;
    break;
  default:
    mord_diag_add(lx->diags, line, col, "unexpected character '%c'", c);
    return -1;
  }
  tok->text = NULL;
  tok->line = line;
  tok->col = col;
  return 0;
}
