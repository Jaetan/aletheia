-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for batch signal operations.
--
-- Purpose: Facade re-exporting all proof lemmas about batch extraction/building
--   operations from per-topic submodules.
-- Submodules: Roundtrip, Completeness, ReasonParity, Capstone.
--
-- Proof flow:
--   1. a loaded DBC is a ValidDBC, carrying IsValidDBC
--   2. validDBC→allPairsDisjoint gives PhysicallyDisjoint for any two
--      coexisting signals a request names
--   3. withInjected-preserves-disjoint-bits-physical: writing one signal
--      leaves a disjoint one's bits as they were
--   4. extractSignal-encodedBits: an accepted value's frame extracts back to it
--   5. Therefore: batch building on a valid DBC roundtrips every signal
--
-- Mixed byte orders are fully supported: PhysicallyDisjoint checks physical bit
-- positions rather than logical intervals, so LE/BE signal pairs are handled correctly.
module Aletheia.CAN.Batch.Properties where

-- Pairwise disjointness predicates, single-injection preservation, batch roundtrip
open import Aletheia.CAN.Batch.Properties.Roundtrip public using
  ( DisjointFromAll; dfa-nil; dfa-cons
  ; AllPairsDisjoint; apd-nil; apd-cons
  ; AllSignalsFit; asf-nil; asf-cons
  ; AllFromMessage; afm-nil; afm-cons
  ; signalFits
  ; pairs
  ; nonePastFrameEnd-fits
  ; validateAndBuild-fits
  ; single-write-preserves
  ; injectOne-written
  ; injectOne-roundtrip
  ; injectAll-preserves-disjoint
  ; injectAll-roundtrip
  )
-- Extraction completeness
open import Aletheia.CAN.Batch.Properties.Completeness public using
  ( totalEntries
  ; extractAll-complete
  )

-- Binary/JSON reason parity + wire-code distinctness
open import Aletheia.CAN.Batch.Properties.ReasonParity public using
  ( reason-parity
  ; extractionErrorCodeFromℕ
  ; fromℕ∘toℕ
  ; extractionErrorCodeToℕ-injective
  )

-- Capstone theorem: IsValidDBC → batch roundtrip
open import Aletheia.CAN.Batch.Properties.Capstone public using
  ( AllAlwaysPresent; aap-nil; aap-cons
  ; DistinctFromAll; dist-nil; dist-cons
  ; PairsDistinct; pd-nil; pd-cons
  ; allAlwaysPresent?
  ; allFromMessage?
  ; pairsDistinct?
  ; validDBC→allPairsDisjoint
  ; validDBC→allSignalsFit
  ; validDBC-roundtrip
  )
