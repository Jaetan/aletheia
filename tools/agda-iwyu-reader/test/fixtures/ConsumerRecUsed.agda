-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerRecUsed where
open import RecLib using (TagR; mkR; Pair; fstP)
getF : Pair → TagR
getF p = fstP p
