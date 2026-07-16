-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Emitted-text round-trip soundness for the FormatDBCText handler.
--
-- The handler produces a `DBCTextResponse txt _` ONLY through
-- `formatDBCTextResult`, and only in the branch where the exact round-trip check
-- `roundTripsWithᵇ d′ (formatText d′)` returned `true`.  This module MACHINE-
-- CHECKS that promise: every `DBCTextResponse txt` the handler can emit
-- satisfies `parseText txt ≡ inj₂ d′` — i.e. the shipped text re-parses to the
-- (node-normalized) input DBC.  Without this lemma the "provably round-trips, or
-- refuse" guarantee would be only definitional (true by how the code happens to
-- be written); here it is a checked theorem, so a future refactor that broke the
-- sharing or the check would fail this proof rather than silently ship lossy text.
--
-- AXIOM-FREE: it composes `roundTripsᵇ-sound` (the conditioned-on-evaluation
-- soundness lemma) with a case-split on the handler's round-trip verdict, kept
-- abstract to keep the check cheap (see `go` below).  No String bridging axiom,
-- no well-formedness hypothesis.
module Aletheia.Protocol.Handlers.Properties.FormatDBCText where

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.TextParser using (parseText)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextParser.RoundTripCheck using (roundTripsWithᵇ)
open import Aletheia.DBC.TextParser.WellFormedCheck using (wfTextIssues)
open import Aletheia.DBC.TextParser.Properties.RoundTripCheck.Sound
  using (roundTripsᵇ-sound)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.Handlers.FormatDBCText using (finish; formatDBCTextResult)

-- Every `DBCTextResponse` the handler emits round-trips: its text re-parses to
-- the (node-normalized) input DBC.  `formatDBCTextResult d′` reduces to
-- `finish (formatText d′) (roundTripsWithᵇ d′ (formatText d′)) (wfTextIssues d′)`.
--
-- The helper `go` takes the round-trip verdict as an ABSTRACT `w` (never the concrete
-- `roundTripsWithᵇ d′ (formatText d′)` term) with a witness `eqw : … ≡ w`.  This
-- is what keeps the proof cheap: were the verdict left concrete, checking it
-- would force Agda to evaluate `parseText (formatText d′)` — the round-trip
-- composition — which explodes, because `formatText d′` emits a concrete
-- parseable prefix even with `d′` symbolic, so `parseText` reduces far before
-- getting stuck.  With `w` abstract, splitting it to `true`/`false` reduces the
-- handler's `if` by a literal, never touching `parseText (formatText d′)`.
--
--   • `w ≡ true`:  `finish … true …` is `DBCTextResponse (formatText d′)
--     (wfTextIssues d′)`, so the emitted text is `formatText d′`; and `eqw` is
--     definitionally `roundTripsᵇ d′ ≡ true`, which `roundTripsᵇ-sound` discharges.
--   • `w ≡ false`: `finish … false …` is an `Error`, refuted against a
--     `DBCTextResponse`.
formatDBCTextResult-sound : ∀ d′ txt′ is′
  → formatDBCTextResult d′ ≡ Response.DBCTextResponse txt′ is′
  → parseText txt′ ≡ inj₂ d′
formatDBCTextResult-sound d′ txt′ is′ h =
  go (roundTripsWithᵇ d′ (formatText d′)) refl txt′ is′ h
  where
  go : ∀ w → roundTripsWithᵇ d′ (formatText d′) ≡ w
     → ∀ t i → finish (formatText d′) w (wfTextIssues d′) ≡ Response.DBCTextResponse t i
     → parseText t ≡ inj₂ d′
  go true  eqw .(formatText d′) .(wfTextIssues d′) refl = roundTripsᵇ-sound d′ eqw
  go false eqw t i ()
