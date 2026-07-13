-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Soundness of the V2 exact round-trip check (E.2 route (b), slice 2 — §6.3).
--
-- `roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d`.  This is the precise
-- sense in which V2's YES is ground truth BY CONSTRUCTION, and — crucially — it is
-- AXIOM-FREE: unlike the universal theorem `parseText-on-formatText` (which routes
-- through the two String↔List Char bridging axioms in `Substrate/Unsafe.agda`), this
-- lemma is CONDITIONED ON THE EVALUATION.  `parseText (formatText d)` is literally
-- run, and the `Dec`'s yes-branch IS the proof object for THIS `d`: no well-formedness
-- hypothesis, no String axiom (both sides of the traced equation already live at the
-- value level, decided by `_≟-DBC_`).  `--safe`, no `postulate`, no `Unsafe` import.
module Aletheia.DBC.TextParser.Properties.RoundTripCheck.Sound where

open import Data.Bool using (true)
open import Data.Bool.Properties using (T-≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)

open import Aletheia.Error using (DBCTextParseError)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextParser using (parseText)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextParser.RoundTripCheck using (rtGo; roundTripsᵇ)

-- `rtGo r d ≡ true` forces the parse-back to be `inj₂ d` exactly:
--   • inj₁ e: `rtGo (inj₁ _) d = false`, so `false ≡ true` is absurd.
--   • inj₂ d″: `rtGo (inj₂ d″) d = ⌊ d ≟-DBC d″ ⌋`; `⌊…⌋ ≡ true` ⇒ `T ⌊…⌋`
--     (`Equivalence.from T-≡`) ⇒ the witness `d ≡ d″` (`toWitness`) ⇒ `inj₂ d″ ≡ inj₂ d`.
rtGo-sound : ∀ (r : DBCTextParseError ⊎ DBC) (d : DBC) → rtGo r d ≡ true → r ≡ inj₂ d
rtGo-sound (inj₁ _)  d ()
rtGo-sound (inj₂ d″) d eq = cong inj₂ (sym (toWitness (Equivalence.from T-≡ eq)))

roundTripsᵇ-sound : ∀ (d : DBC) → roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d
roundTripsᵇ-sound d eq = rtGo-sound (parseText (formatText d)) d eq
