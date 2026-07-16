-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- The same overloaded `nilA` as ConsumerAmbigTerm, but in PATTERN position, which
-- Agda attributes differently: a pattern occurrence DOES get a highlight at the
-- constructor's def-site, so the syntactic count reaches it here and the verdict no
-- longer rests on the overloaded-name rule.  Kept to pin that asymmetry -- the two
-- positions must agree on USED even though only one of them is legible.
module ConsumerAmbigPat where

open import AmbigMid using (BoxA; nilA)

v : BoxA → BoxA
v nilA = nilA
