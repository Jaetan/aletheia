-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerRenameUsed where
open import Origin using () renaming (idO to idR)
useR : {X : Set} → X → X
useR x = idR x
