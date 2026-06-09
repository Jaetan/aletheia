-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerAbsDead where
open import AbsGen using (TagAb; mkAb)
open import AbsMid using (module InstAb)
open InstAb
noAb : TagAb
noAb = mkAb
