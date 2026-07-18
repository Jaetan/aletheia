-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Attribute well-formedness predicates, shared between the runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`, which decides them with stock
-- `Dec` deciders) and the attribute round-trip proof tree (which consumes
-- them as `WFAttribute` premises).  Hosted outside the `Properties`
-- namespace so the checker imports them without pulling proof modules into
-- the compiled runtime closure; the proof-side homes
-- (`Properties.Attributes.Common`, `Properties.Attributes.Def`,
-- `Properties.Aggregator.Foundations`) re-export them (`open … public`), so
-- proof-tree import paths are unchanged.
module Aletheia.DBC.TextParser.WellFormedAttr where

open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.DBC.DecRat.Refinement using (natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex )
open import Aletheia.DBC.TextParser.Attributes using (findLabel)
open import Aletheia.DBC.TextFormatter.Attributes using (nthLabel)

-- ============================================================================
-- VALUE CONSTRUCTOR MATCHES ATTRIBUTE TYPE
-- ============================================================================
--
-- `DBCAttribute` carries `AttrValue` independently of the looked-up
-- `AttrType`; a hand-built DBC could (in principle) place an `AVFloat`
-- under an `ATInt`-typed name.  The roundtrip target only quantifies
-- over well-formed `DBCAttribute` lists, where each value's
-- constructor matches the looked-up def's type.  This relation
-- captures the pairing (the 5 diagonal constructor pairs).

data ValueMatchesType : AttrType → AttrValue → Set where
  VMTInt    : ∀ {mn mx} z → ValueMatchesType (ATInt mn mx)   (AVInt z)
  VMTFloat  : ∀ {mn mx} d → ValueMatchesType (ATFloat mn mx) (AVFloat d)
  VMTString : ∀ s         → ValueMatchesType ATString        (AVString s)
  VMTEnum   : ∀ {ls} n    → ValueMatchesType (ATEnum ls)     (AVEnum n)
  VMTHex    : ∀ {mn mx} n → ValueMatchesType (ATHex mn mx)   (AVHex n)

-- ============================================================================
-- ATTRIBUTE TYPE WELL-FORMEDNESS
-- ============================================================================
--
-- WfAttrType: ENUM must be non-empty (DBC grammar requirement; an empty
-- ENUM is rejected at the lexical level by `parseEnumLabels`'s `do
-- h ← parseStringLit; t ← many ...; pure (h ∷ t)` — at least one label).

data WfAttrType : AttrType → Set where
  WfATInt    : ∀ mn mx → WfAttrType (ATInt mn mx)
  WfATFloat  : ∀ mn mx → WfAttrType (ATFloat mn mx)
  WfATString : WfAttrType ATString
  WfATEnum   : ∀ x xs → WfAttrType (ATEnum (x ∷ xs))
  WfATHex    : ∀ mn mx → WfAttrType (ATHex mn mx)

-- ============================================================================
-- ENUM-DEFAULT STABILITY
-- ============================================================================
--
-- An ATEnum default whose value is `AVEnum n` emits the label STRING
-- `nthLabel n labels`, which must resolve back to the SAME index —
-- `findLabel (nthLabel n labels) labels ≡ just n` (label uniqueness +
-- index-in-bounds).  Vacuous (`⊤`) for every other (AttrType, AttrValue)
-- pair.

DefaultEnumOK : AttrType → AttrValue → Set
DefaultEnumOK (ATEnum labels) (AVEnum n) =
  findLabel (nthLabel (natDecRatToℕ n) labels) labels ≡ just (natDecRatToℕ n)
DefaultEnumOK _               _          = ⊤
