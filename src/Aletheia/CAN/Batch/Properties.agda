{-# OPTIONS --safe --without-K #-}

-- Correctness properties for batch signal operations.
--
-- Purpose: Facade re-exporting all proof lemmas about batch extraction/building
--   operations from per-topic submodules.
-- Submodules: Roundtrip, Completeness, Capstone.
--
-- Proof flow:
--   1. validateDBCFull dbc succeeds → DBCValid dbc
--   2. lookupDisjointFromDBC extracts PhysicallyDisjoint for any two coexisting signals
--   3. PhysicallyDisjoint is the precondition for injectSignal-preserves-disjoint-bits-physical
--   4. Therefore: batch operations on validated DBCs preserve signal values
--
-- Mixed byte orders are fully supported: PhysicallyDisjoint checks physical bit
-- positions rather than logical intervals, so LE/BE signal pairs are handled correctly.
module Aletheia.CAN.Batch.Properties where

-- Pairwise disjointness predicates, single-injection preservation, batch roundtrip
open import Aletheia.CAN.Batch.Properties.Roundtrip public using
  ( DisjointFromAll; dfa-nil; dfa-cons
  ; AllPairsDisjoint; apd-nil; apd-cons
  ; AllSignalsFit; asf-nil; asf-cons
  ; signalFits
  ; single-inject-preserves
  ; injectAll-preserves-disjoint
  ; InjectRoundtrips
  ; AllRoundtrip; ar-nil; ar-cons
  ; roundtrip-unsigned→IR
  ; roundtrip-signed→IR
  ; injectAll-roundtrip
  )

-- Extraction completeness
open import Aletheia.CAN.Batch.Properties.Completeness public using
  ( totalEntries
  ; extractAll-complete
  )

-- Capstone theorem: ValidDBC → batch roundtrip, representability
open import Aletheia.CAN.Batch.Properties.Capstone public using
  ( AllAlwaysPresent; aap-nil; aap-cons
  ; AllFromMessage; afm-nil; afm-cons
  ; DistinctFromAll; dist-nil; dist-cons
  ; PairsDistinct; pd-nil; pd-cons
  ; allAlwaysPresent?
  ; allFromMessage?
  ; pairsDistinct?
  ; validDBC→allPairsDisjoint
  ; validDBC→allSignalsFit
  ; validDBC-roundtrip
  ; Representable; repr-unsigned; repr-signed
  ; representable?
  ; representable→roundtrips
  ; AllRepresentable; arep-nil; arep-cons
  ; allRepresentable?
  ; allRepresentable→allRoundtrip
  )
