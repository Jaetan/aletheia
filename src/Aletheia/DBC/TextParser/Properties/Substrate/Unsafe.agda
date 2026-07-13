-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --without-K #-}

-- Bridging axioms for `String ↔ List Char`
-- (see `memory/project_b3d_stdlib_audit.md`).
--
-- This is the *one* non-`--safe` module in the project.  See
-- `Shakefile.hs` `check-invariants` for the explicit allowlist entry
-- and the corresponding postulate-allowlist exception.  Adding any
-- other `*Unsafe*.agda` module requires user approval (see
-- `feedback_no_suppression_without_approval.md`).
--
-- Origin and rationale:
--   The Aletheia DBC text parser/formatter pair operates on `List Char`
--   internally; the public boundary is `parseText : String → ⊎ DBC` and
--   `formatText : DBC → String`.  Composing the universal
--
--     parseText-formatText-roundtrip : ∀ d → parseText (formatText d) ≡ inj₂ d
--
--   from the internal `List Char`-level theorem requires reducing
--   through the two String↔List Char primitives:
--
--     parseText (formatText d)
--   = parseTextChars (toList (fromList (formatChars d)))   -- by defn
--   ≡ parseTextChars (formatChars d)                        -- by toList∘fromList
--   ≡ inj₂ d                                                -- by internal theorem
--
--   Per-primitive identifier roundtrip at layer-2 / layer-3 proofs uses
--   `toList∘fromList` to bridge `toList (fromList cs) = cs` whenever a
--   formatter emits `fromList cs` (e.g. namespace identifier emission)
--   and the parser-side proof needs to recover `cs`.  `fromList∘toList`
--   bridges the opposite direction for proofs that go from a String s
--   through `toList s` and back.
--
-- Status (2026-04-26): this module previously also hosted
-- `mkIdentFromCharsUnsafe`, the helper Lexer.parseIdentifier used to
-- bridge a char-level `T (validIdentifierᵇ cs)` witness into the
-- String-internal `T (validIdentifierᵇ (toList name))` witness required
-- by the old `Identifier.name : String` shape.  After `Identifier.name`
-- was lifted to `List Char`, that helper is gone; Lexer builds the
-- Identifier directly via `mkIdentFromChars` (axiom-free) in
-- `Aletheia.DBC.Identifier`.  This module's surface shrinks to the two
-- axioms only.
--
-- Stdlib reference:
--   `agda-stdlib v2.3 Data.String.Unsafe` exports the same two lemmas as
--   `toList∘fromList` and `fromList∘toList`, both proven by `trustMe`
--   under `{-# OPTIONS --with-K #-}`.  Direct `postulate` here is
--   semantically identical to stdlib's `trustMe`-backed proofs and
--   avoids the `--with-K` requirement (this module declares
--   `--without-K`).  Pre-audit confirmed `Data.String.Properties` (the
--   `--safe` counterpart) carries `toList-injective` but no inverse
--   equation, and `Agda.Builtin.String.Properties` exposes only
--   `primStringToListInjective` / `primStringFromListInjective` — no
--   roundtrip lemma at any layer.
--
-- Why these are unprovable under `--safe --without-K`:
--   `primStringToList` / `primStringFromList` / `primStringAppend` are
--   Agda built-ins that reduce only on closed-term arguments.
--   Universally-quantified `s : String` and `cs : List Char` arguments
--   stay abstract through these primitives, so neither structural
--   induction nor primitive reduction is available.  See
--   `memory/project_b3d_stdlib_audit.md` (2026-04-22) for the full
--   substrate-audit trail.
--
-- Soundness:
--   Both equations are operationally true (the Agda runtime's `String`
--   representation guarantees the round-trip behaviour at the
--   primitive level), and `agda-stdlib` itself treats them as
--   foundational by exposing them under `Data.String.Unsafe`.
--   Aletheia inherits the same soundness assumption.
module Aletheia.DBC.TextParser.Properties.Substrate.Unsafe where

open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; [])
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextParser using (parseText; parseTextChars)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextFormatter.TopLevel using (formatChars)

open import Aletheia.DBC.TextParser.WellFormed using (WellFormedTextDBCAgg)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Universal using
  (parseTextChars-on-formatChars)
-- S2.5 (stitching V1↔V2): the equality tower, the V2 check, and slice-1's checker soundness.
open import Aletheia.DBC.Properties.Equality.Full using (_≟-DBC_)
open import Aletheia.DBC.TextParser.RoundTripCheck using (rtGo; roundTripsᵇ)
open import Aletheia.DBC.TextParser.WellFormedCheck using (wfTextIssues)
open import Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound using (wfTextIssues-sound)

-- ============================================================================
-- BRIDGING AXIOMS
-- ============================================================================

postulate
  toList∘fromList : ∀ (cs : List Char) → toList (fromList cs) ≡ cs
  fromList∘toList : ∀ (s  : String)    → fromList (toList s)  ≡ s

-- ============================================================================
-- UNIVERSAL ROUNDTRIP — parseText ∘ formatText ≡ inj₂ at WF DBC
-- ============================================================================
--
-- Lives in this module (and not a separate
-- `Aggregator/UniversalText.agda`) by deliberate policy: the `parseText`/
-- `formatText` String-level wrap is the SOLE consumer of `toList∘fromList`
-- in the project, and adding a second non-`--safe` module would expand
-- the trusted-axiom-consuming surface beyond the one allowlisted here.
-- Keeping the consumer co-located with the axioms preserves the "1
-- allowlisted Unsafe module" policy stated in CLAUDE.md and AGENTS.md
-- G-A8.
--
-- Composition (one step):
--
--     parseText (formatText d)
--   = parseTextChars (toList (fromList (formatChars d)))   -- by defn
--   ≡ parseTextChars (formatChars d)                        -- by toList∘fromList
--   ≡ inj₂ d                                                -- by parseTextChars-on-formatChars

parseText-on-formatText :
    ∀ (d : DBC) → WellFormedTextDBCAgg d
  → parseText (formatText d) ≡ inj₂ d
parseText-on-formatText d wf =
  trans (cong parseTextChars (toList∘fromList (formatChars d)))
        (parseTextChars-on-formatChars d wf)

-- ============================================================================
-- V1 ↔ V2 STITCHING (E.2 route (b), slice 2 — §6.4)
-- ============================================================================
--
-- The coherence theorem: no V1 diagnostics ⟹ V2 round-trips.  These CONSUME the
-- bridging axioms (they route through `parseText-on-formatText`), so they are
-- co-located here per the "1 allowlisted Unsafe module" policy above — unlike the
-- V2 SOUNDNESS (`RoundTripCheck/Sound.agda`), which is genuinely axiom-free.

-- Reflexive decidable equality never answers `no` on `d , d`, so `⌊ d ≟-DBC d ⌋`
-- (= `rtGo (inj₂ d) d`) is `true`.  `⌊_⌋` is written explicitly so the `with`
-- abstracts the scrutinee cleanly.
dec-refl : ∀ (d : DBC) → ⌊ d ≟-DBC d ⌋ ≡ true
dec-refl d with d ≟-DBC d
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

-- WellFormed ⟹ V2 says YES: transport `parseText-on-formatText` through `rtGo`,
-- then close `rtGo (inj₂ d) d ≡ true` by `dec-refl` (definitional: it is `⌊ d ≟-DBC d ⌋`).
wf→roundTripsᵇ : ∀ (d : DBC) → WellFormedTextDBCAgg d → roundTripsᵇ d ≡ true
wf→roundTripsᵇ d wf =
  trans (cong (λ r → rtGo r d) (parseText-on-formatText d wf)) (dec-refl d)

-- The coherence theorem itself: an empty V1 diagnostic set implies V2 round-trips
-- (modulo the Substrate axioms).  Contrapositive: every V2 divergence ships ≥1 V1
-- diagnostic.  Composes slice-1's `wfTextIssues-sound` with the above.
issues-empty→roundTrips : ∀ (d : DBC) → wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true
issues-empty→roundTrips d eq = wf→roundTripsᵇ d (wfTextIssues-sound d eq)
