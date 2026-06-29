#ifndef MORDANT_PRIVATE_H
#define MORDANT_PRIVATE_H

#include "mordant.h"

mord_pred *mord_pred_new(mord_pred_kind kind);
void mord_pred_free(mord_pred *p);

int mord_is_supported_action(mord_u32 ret);

#endif
