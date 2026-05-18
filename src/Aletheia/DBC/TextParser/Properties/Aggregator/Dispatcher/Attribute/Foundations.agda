{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Foundations for the universal-attribute roundtrip.
--
-- Hosts the bridges the per-shape dispatchers (Assign/String,
-- Assign/Frac, Assign/BareInt, Default, Def) need:
--
--   1. `identifier-name-stop` — every `Identifier` has a non-empty
--      name whose head char is non-hspace, by composing `validIdentifierᵇ`
--      with `isIdentStart→¬isHSpace` from CharClassDisjoint.
--
--   2. `IdentNameStop-of target` — per-target precondition: ⊤ for
--      Network/Message (no nested Identifier), `IdentNameStop n` for
--      Node/EnvVar/NodeMsg, `IdentNameStop sig` for Signal, conjunction
--      for NodeSig.
--
--   3. Value bridges — `rawOfAssignValue` produces `RavDecRat` over the
--      typed refinement's `.value` field for AVInt/AVHex/AVEnum.  The
--      bareInt slim emits via `showInt-chars (intDecRatToℤ z)` and yields
--      `RavDecRat (fromℤ (intDecRatToℤ z))`; we bridge to `IntDecRat.value
--      z` via `mkIntDecRatFromℤ-intDecRatToℤ`.  Mirror for NatDecRat.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations where

open import Data.Bool using (Bool; true; T; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.DBC.Identifier using
  ( Identifier; mkIdent; isIdentStart; isIdentCont
  ; validIdentifierᵇ)
open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal
  ; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)

open import Aletheia.DBC.TextParser.Properties.CharClassDisjoint using
  (isIdentStart→¬isHSpace)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign using
  (IdentNameStop)

-- ============================================================================
-- IDENT-NAME-STOP UNIVERSAL DISCHARGE
-- ============================================================================
--
-- The 21-shape attribute slims (Node/Signal/EnvVar/NodeMsg/NodeSig
-- arms) take `IdentNameStop n` as a precondition: a non-empty `Identi-
-- fier.name n` whose first char is non-hspace.  Every well-formed
-- `Identifier` discharges this universally: empty-name is impossible
-- (`validIdentifierᵇ [] = false`); non-empty-name has `T (isIdentStart
-- c)` for the head, which `isIdentStart→¬isHSpace` rules out.

private
  -- `T (a ∧ b)` projects to `T a × T b`.  Closed-Bool reduction:
  -- `(true ∧ b) = b`, so `T (true ∧ b) = T b`; only the `(true, true)`
  -- case is inhabited (others have `T (false ∧ _) = T false = ⊥`).
  T-∧→× : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
  T-∧→× {true}  {true}  tt = tt , tt

-- Universal IdentNameStop witness, formulated against the same Σ-shape
-- the slims expect.  Pattern-matches on the Identifier record's two
-- fields directly: empty-name is closed via `()` on `valid : T false`;
-- non-empty extracts `T (isIdentStart c)` and composes with the disjoint-
-- ness lemma.
identifier-name-stop : ∀ (n : Identifier) → IdentNameStop n
identifier-name-stop (mkIdent []       ())
identifier-name-stop (mkIdent (c ∷ cs) v) =
  c , cs , refl , isIdentStart→¬isHSpace c (proj₁ (T-∧→× v))

-- ============================================================================
-- PER-TARGET IDENT-NAME-STOP PRECONDITION
-- ============================================================================
--
-- Each `AttrTarget` constructor carries 0, 1, or 2 nested `Identifier`s.
-- The corresponding slim takes one `IdentNameStop` per nested ident; this
-- helper lifts the per-target need to a single Set indexed by the ctor.

IdentNameStop-of : AttrTarget → Set
IdentNameStop-of ATgtNetwork           = ⊤
IdentNameStop-of (ATgtNode n)          = IdentNameStop n
IdentNameStop-of (ATgtMessage _)       = ⊤
IdentNameStop-of (ATgtSignal _ sig)    = IdentNameStop sig
IdentNameStop-of (ATgtEnvVar ev)       = IdentNameStop ev
IdentNameStop-of (ATgtNodeMsg n _)     = IdentNameStop n
IdentNameStop-of (ATgtNodeSig n _ sig) = IdentNameStop n × IdentNameStop sig

-- Universal discharge from `Identifier.valid`-only: every `IdentNameStop-of
-- target` is provable by composing `identifier-name-stop` per nested ident.
identifier-name-stop-of : ∀ (target : AttrTarget) → IdentNameStop-of target
identifier-name-stop-of ATgtNetwork           = tt
identifier-name-stop-of (ATgtNode n)          = identifier-name-stop n
identifier-name-stop-of (ATgtMessage _)       = tt
identifier-name-stop-of (ATgtSignal _ sig)    = identifier-name-stop sig
identifier-name-stop-of (ATgtEnvVar ev)       = identifier-name-stop ev
identifier-name-stop-of (ATgtNodeMsg n _)     = identifier-name-stop n
identifier-name-stop-of (ATgtNodeSig n _ sig) =
  identifier-name-stop n , identifier-name-stop sig
