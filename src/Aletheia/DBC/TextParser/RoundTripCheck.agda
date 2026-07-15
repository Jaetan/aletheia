-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Exact round-trip check for the DBC text formatter.
--
-- Answers "does this DBC survive the text round-trip?" with ZERO over-refusal, by
-- EVALUATING `parseText (formatText d)` and deep-comparing the parse-back value
-- with `d` via `_≟-DBC_` (the decidable-equality tower, `Properties.Equality.Full`).
-- Its YES is ground truth by construction, and — unlike the universal WF theorem —
-- its soundness (`RoundTripCheck/Sound.agda`) is AXIOM-FREE, because the
-- check is conditioned on the evaluation: the `Dec`'s yes-branch IS the proof
-- object for THIS `d`.  Runtime-side: no proofs here.  (A `Properties.Equality.*`
-- import is fine — `check-no-properties-in-runtime` guards only Main/Handlers'
-- direct imports, and the tower is all runtime decidable-equality, no lemmas.)
module Aletheia.DBC.TextParser.RoundTripCheck where

open import Data.Bool using (Bool; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Error using (DBCTextParseError)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextParser using (parseText)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.Decidable.Equality.Full using (_≟-DBC_)

-- Exposed on the parse-back result (per feedback_expose_scrutinee_for_external_rewrite):
-- a parse-back FAILURE counts as divergence (honest — e.g. an `AVFloat` under an
-- `ATInt` def emits a line the parser rejects); a parse-back value is compared to `d`.
rtGo : DBCTextParseError ⊎ DBC → DBC → Bool
rtGo (inj₁ _)  _ = false
rtGo (inj₂ d″) d = ⌊ d ≟-DBC d″ ⌋

-- The handler passes the already-computed text (argument-passing, not `let`, so the
-- "one extra parseText, one formatText" cost accounting holds).
roundTripsWithᵇ : DBC → String → Bool
roundTripsWithᵇ d txt = rtGo (parseText txt) d

roundTripsᵇ : DBC → Bool
roundTripsᵇ d = roundTripsWithᵇ d (formatText d)
