{-# OPTIONS --without-K #-}

-- B.3.d substrate: bridging axioms for `String ↔ List Char` (Phase B.3.d
-- layer 1 — Option 3a per `memory/project_b3d_stdlib_audit.md`).
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
-- Post-3d.4 status (2026-04-26): pre-3d.4 this module also hosted
-- `mkIdentFromCharsUnsafe`, the helper Lexer.parseIdentifier used to
-- bridge a char-level `T (validIdentifierᵇ cs)` witness into the
-- String-internal `T (validIdentifierᵇ (toList name))` witness required
-- by the old `Identifier.name : String` shape.  After 3d.4 lifted
-- `Identifier.name : List Char`, that helper is gone; Lexer builds the
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

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans; cong)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextParser using (parseText; parseTextChars)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextFormatter.TopLevel using (formatChars)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Universal using
  (WellFormedDBC; parseTextChars-on-formatChars)

-- ============================================================================
-- BRIDGING AXIOMS
-- ============================================================================

postulate
  toList∘fromList : ∀ (cs : List Char) → toList (fromList cs) ≡ cs
  fromList∘toList : ∀ (s  : String)    → fromList (toList s)  ≡ s

-- ============================================================================
-- B.3.d UNIVERSAL ROUNDTRIP — parseText ∘ formatText ≡ inj₂ at WF DBC
-- ============================================================================
--
-- Closes Phase B.3.d.  Lives in this module (and not a separate
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
    ∀ (d : DBC) → WellFormedDBC d
  → parseText (formatText d) ≡ inj₂ d
parseText-on-formatText d wf =
  trans (cong parseTextChars (toList∘fromList (formatChars d)))
        (parseTextChars-on-formatChars d wf)
