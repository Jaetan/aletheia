{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC formatter and parser.
--
-- Purpose: Prove format-parse roundtrip (weak inverse) for DBC serialization.
-- Properties:
--   format-parse-roundtrip: WellFormedDBCRT d → parseDBCWithErrors (formatDBC d) ≡ inj₂ d
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
open import Data.List.Relation.Unary.All using (All)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Formatter using (formatDBC; formatDBCMessage)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)

-- Re-export predicates so consumers only need to import Properties.
open import Aletheia.DBC.Formatter.WellFormed public
open import Aletheia.DBC.Formatter.MessageRoundtrip using (message-list-roundtrip)

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP
-- ============================================================================

-- Forward roundtrip: formatting then parsing a well-formed DBC recovers the original.
-- Requires WellFormedDBCRT (WellFormedDBC + PhysicallyValid for each signal)
-- because BigEndian signals need the unconvert→convert startBit roundtrip.
format-parse-roundtrip : ∀ d → WellFormedDBCRT d
  → parseDBCWithErrors (formatDBC d) ≡ inj₂ d
format-parse-roundtrip
  record { version = v ; messages = ms ; signalGroups = .[] ; environmentVars = .[] ; valueTables = .[] }
  record { messages-wf = mwf ; groups-empty = refl ; envvars-empty = refl ; vtables-empty = refl }
  rewrite message-list-roundtrip ms 0 mwf
  = refl
