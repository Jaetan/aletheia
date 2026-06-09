-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerOpUsed where
open import OpMod using (TagO; mkO; _⊕_; _⊗_)
useOp : TagO
useOp = mkO ⊕ mkO
