-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- Imports the value and the module but uses NEITHER.
-- Expected reader verdicts: Mid=idO DEAD, Mid=InstR (module) DEAD.
module ConsumerDead where

open import Mid using (idO; module InstR)
open InstR

something : {X : Set} → X → X
something x = x       -- uses neither idO nor wrapR
