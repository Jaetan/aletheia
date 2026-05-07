{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC formatter and parser.
--
-- Purpose: Prove format-parse roundtrip (weak inverse) for DBC serialization
-- and the formatter-as-fixed-point corollary.
-- Properties:
--   format-parse-roundtrip : WellFormedDBCRT d → parseDBCWithErrors (formatDBC d) ≡ inj₂ d
--   format-parse-format    : WellFormedDBCRT d → parseDBCWithErrors (formatDBC d) ≡ inj₂ d'
--                            → formatDBC d' ≡ formatDBC d  (corollary)
-- Role: Phase 5 verification of DBC serialization correctness.
--
-- Structure (each layer type-checks independently for fast incremental builds):
--   WellFormed.agda        — predicates + bridge lemmas
--   SignalRoundtrip.agda   — signal-level roundtrip proofs
--   MessageRoundtrip.agda  — message-level roundtrip proofs
--   Properties.agda        — top-level theorem (this file)
--
-- Note: The roundtrip requires WellFormedDBCRT (not just WellFormedDBC)
-- because BigEndian signals need PhysicallyValid constraints for the
-- unconvertStartBit→convertStartBit roundtrip.
module Aletheia.DBC.Formatter.Properties where

open import Data.List using (List; []; map)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Formatter using (formatDBC; formatDBCMessage; formatSignalGroup;
  formatEnvironmentVar; formatValueTable)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)

-- Re-export predicates so consumers only need to import Properties.
open import Aletheia.DBC.Formatter.WellFormed public
open import Aletheia.DBC.Formatter.MessageRoundtrip using (message-list-roundtrip)
open import Aletheia.DBC.Formatter.MetadataRoundtrip using
  (signalGroup-list-roundtrip; environmentVar-list-roundtrip; valueTable-list-roundtrip;
   node-list-roundtrip; comment-list-roundtrip; attribute-list-roundtrip;
   rawValueDescList-roundtrip)

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP
-- ============================================================================

-- Forward roundtrip: formatting then parsing a well-formed DBC recovers the original.
-- Requires WellFormedDBCRT (WellFormedDBC + PhysicallyValid for each signal)
-- because BigEndian signals need the unconvert→convert startBit roundtrip.
-- Metadata fields (signal groups, environment vars, value tables) round-trip
-- unconditionally — no WF constraints needed.
format-parse-roundtrip : ∀ d → WellFormedDBCRT d
  → parseDBCWithErrors (formatDBC d) ≡ inj₂ d
format-parse-roundtrip d wf
  rewrite message-list-roundtrip (DBC.messages d) 0 (WellFormedDBCRT.messages-wf wf)
        | signalGroup-list-roundtrip (DBC.signalGroups d)
        | environmentVar-list-roundtrip (DBC.environmentVars d)
        | valueTable-list-roundtrip (DBC.valueTables d)
        | node-list-roundtrip (DBC.nodes d)
        | comment-list-roundtrip (DBC.comments d)
        | attribute-list-roundtrip (DBC.attributes d)
        | rawValueDescList-roundtrip (DBC.unresolvedValueDescs d)
  = refl

-- ============================================================================
-- FORMATTER FIXED POINT
-- ============================================================================
--
-- Idempotency / stability of `formatDBC` under one round-trip step: any
-- DBC value `d'` recovered from `parseDBCWithErrors (formatDBC d)` must
-- format to the same string as `d`. This is a corollary of
-- `format-parse-roundtrip` — that theorem already pins the parser output
-- to `inj₂ d`, so any other `inj₂ d'` is forced to satisfy `d' ≡ d` via
-- `inj₂-injective`. Stating it as its own theorem documents that the
-- formatter is a fixed point of the parse-format round trip on its own
-- output.
--
-- Companion to the unconditional `parse-format-parse` in
-- `DBC/JSONParser/Properties.agda`: that theorem proves the parser-side dual
-- (parse ∘ format ∘ parse = parse) by composing `format-parse-roundtrip`
-- with the strengthened `parse-wellformed : WellFormedDBCRT`, which is
-- guaranteed by `parseSignalFields`'s `physicalGate`.
format-parse-format : ∀ d → WellFormedDBCRT d
  → ∀ d' → parseDBCWithErrors (formatDBC d) ≡ inj₂ d'
  → formatDBC d' ≡ formatDBC d
format-parse-format d wf d' eq =
  cong formatDBC (sym (inj₂-injective (trans (sym (format-parse-roundtrip d wf)) eq)))

-- ============================================================================
-- FORMATTER INJECTIVITY ON WELL-FORMED INPUTS
-- ============================================================================
--
-- `formatDBC` is injective on well-formed DBCs: distinct WF DBCs always
-- format to distinct strings. This is a corollary of the round-trip — if
-- two WF DBCs format to the same JSON, they parse back to the same DBC,
-- which by the round-trip equals BOTH originals; transitivity then forces
-- them equal. Proves the formatter does not lose information from the WF
-- subtype, which is the dual of the round-trip's "no information added"
-- statement.
formatDBC-injective : ∀ d₁ d₂ → WellFormedDBCRT d₁ → WellFormedDBCRT d₂
  → formatDBC d₁ ≡ formatDBC d₂ → d₁ ≡ d₂
formatDBC-injective d₁ d₂ wf₁ wf₂ fmt-eq = inj₂-injective
  (trans (sym (format-parse-roundtrip d₁ wf₁))
         (trans (cong parseDBCWithErrors fmt-eq)
                (format-parse-roundtrip d₂ wf₂)))

-- Existential completeness corollary: for any WF DBC, parsing its formatted
-- form succeeds. This is `format-parse-roundtrip` packaged in existential
-- form to make the "completeness on the formatDBC-image" claim explicit
-- without forcing the consumer to mention the recovered DBC value.
parseDBC-complete-on-format : ∀ d → WellFormedDBCRT d
  → ∃[ d' ] parseDBCWithErrors (formatDBC d) ≡ inj₂ d'
parseDBC-complete-on-format d wf = d , format-parse-roundtrip d wf
