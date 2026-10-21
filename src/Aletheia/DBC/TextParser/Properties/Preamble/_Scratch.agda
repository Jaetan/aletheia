-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Load-bearing reduction canary for the `NS_` proof.
--
-- The preamble's keyword lines are words, and their `T (isWordᵇ (toList kw))`
-- witnesses are `tt`.  That is well-typed only if `isWordᵇ (toList kw)`
-- reduces to `true` on every literal keyword string, so `T (...) = T true = ⊤`.
--
-- If stdlib `Data.Char.Base` ever changes the primitive-char classification
-- (`isDigit`, `_≟_`, `toℕ`) in a way that blocks reduction on closed chars,
-- this file fails to type-check before `Format/Preamble.agda` does, which
-- makes the regression easier to diagnose.  A keyword is a word and never an
-- identifier: `validIdentifierᵇ` refuses it.
module Aletheia.DBC.TextParser.Properties.Preamble._Scratch where

open import Data.Bool using (T; not)
open import Data.String using (toList)
open import Data.Unit using (tt)

open import Aletheia.DBC.Identifier using (isWordᵇ; validIdentifierᵇ)

_test-NSDescWord : T (isWordᵇ (toList "NS_DESC_"))
_test-NSDescWord = tt

_test-SGMULVALWord : T (isWordᵇ (toList "SG_MUL_VAL_"))
_test-SGMULVALWord = tt

_test-FILTERWord : T (isWordᵇ (toList "FILTER"))
_test-FILTERWord = tt

_test-NSDescNotIdentifier : T (not (validIdentifierᵇ (toList "NS_DESC_")))
_test-NSDescNotIdentifier = tt
