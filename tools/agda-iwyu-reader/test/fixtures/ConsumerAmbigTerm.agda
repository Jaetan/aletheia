-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- `nilA` is written here, in TERM position, and so is USED.  This is the case that
-- pins the overloaded-name rule: Agda attributes no highlight to the constructor a
-- term occurrence resolves to, so the syntactic count sees only the import token
-- and the elaborated terms are the sole witness.  Trust the count here and this
-- reads DEAD -- a used import wrongly reported for removal.
module ConsumerAmbigTerm where

open import AmbigMid using (BoxA; nilA)

v : BoxA
v = nilA
