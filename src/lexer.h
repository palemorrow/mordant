#ifndef MORDANT_LEXER_H
#define MORDANT_LEXER_H

#include "mordant.h"

typedef enum {
  TOK_EOF,
  TOK_NEWLINE,
  TOK_IDENT,
  TOK_NUMBER,
  TOK_ARG,
  TOK_ARCH,
  TOK_DEFAULT,
  TOK_ALLOW,
  TOK_KILL,
  TOK_ERRNO,
  TOK_IF,
  TOK_EQ,
  TOK_NE,
  TOK_LT,
  TOK_LE,
  TOK_GT,
  TOK_GE,
  TOK_ANDAND,
  TOK_OROR,
  TOK_AMP,
  TOK_LPAREN,
  TOK_RPAREN
} mord_tok_kind;

typedef struct {
  mord_tok_kind kind;
  const char *text;
  size_t len;
  mord_u64 num;
  unsigned arg;
  unsigned line;
  unsigned col;
} mord_token;

typedef struct {
  const char *src;
  size_t pos;
  unsigned line;
  unsigned col;
  mord_diaglist *diags;
  int failed;
} mord_lexer;

void mord_lexer_init(mord_lexer *lx, const char *src, mord_diaglist *diags);
int mord_lex(mord_lexer *lx, mord_token *tok);

#endif
