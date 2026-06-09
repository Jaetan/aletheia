-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OpMod where
data TagO : Set where mkO : TagO
_⊕_ : TagO → TagO → TagO
_ ⊕ y = y
_⊗_ : TagO → TagO → TagO
_ ⊗ y = y
