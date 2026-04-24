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
--   Per-primitive identifier roundtrip at the layer-2 proofs additionally
--   needs `fromList (toList name) ≡ name` because every `String`-typed
--   `DBC` field (e.g. `Node.name`, `DBCSignal.name`, `DBCComment.text`)
--   round-trips through `parseIdentifier (toList name) ≡ inj₂ (fromList
--   (toList name)) = inj₂ name` — only collapsible by the second axiom.
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

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.String using (String; toList; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)
open import Aletheia.DBC.Identifier using (Identifier; mkIdent; validIdentifierᵇ)

-- ============================================================================
-- BRIDGING AXIOMS
-- ============================================================================

postulate
  toList∘fromList : ∀ (cs : List Char) → toList (fromList cs) ≡ cs
  fromList∘toList : ∀ (s  : String)    → fromList (toList s)  ≡ s

-- ============================================================================
-- CHAR-LIST IDENTIFIER CONSTRUCTION (text parser path)
-- ============================================================================

-- Build an Identifier from a char list, bridging the char-level bool witness
-- to the `toList name`-level witness required by `Identifier.valid` via the
-- `toList∘fromList` axiom.  This is the text parser's construction path; the
-- axiom use is bounded to this single helper.
mkIdentFromCharsUnsafe : (cs : List Char) → Maybe Identifier
mkIdentFromCharsUnsafe cs with validIdentifierᵇ cs in eq
... | true  = just (mkIdent (fromList cs)
                   (subst T
                     (cong validIdentifierᵇ (sym (toList∘fromList cs)))
                     (subst T (sym eq) tt)))
... | false = nothing
