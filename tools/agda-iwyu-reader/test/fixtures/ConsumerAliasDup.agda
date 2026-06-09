-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerAliasDup where
open import Origin using (idO)
open import Origin using () renaming (idO to idR)
useId : {X : Set} → X → X
useId x = idO x
