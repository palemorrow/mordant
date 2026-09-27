#ifndef MORDANT_TOOLS_INSTALL_H
#define MORDANT_TOOLS_INSTALL_H

#include <stddef.h>

#include "mordant.h"

int mordant_install_program(const struct sock_filter *insns, size_t count,
                            mord_diaglist *diags);

#endif
