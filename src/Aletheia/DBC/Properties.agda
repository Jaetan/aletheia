-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Facade re-exporting the proofs about DBC well-formedness — symmetry of the
-- disjointness and coexistence relations, soundness/completeness of the fast
-- overlap check, and proof extraction from a validated DBC — from the per-topic
-- submodules (Disjointness, WellFormedness).
--
-- The predicates and their decision procedures live under
-- `Aletheia.DBC.Decidable.*`.
module Aletheia.DBC.Properties where

open import Aletheia.DBC.Properties.Disjointness public using
  ( signalsDisjoint-sym
  ; physicallyDisjoint-sym
  ; physicallyOverlapᵇ-sound
  ; physicallyOverlapᵇ-complete
  )

open import Aletheia.DBC.Properties.WellFormedness public using
  ( valuesOverlap-sym
  ; canCoexist-sym
  ; signalPairValid-sym
  ; extractFromValidAgainstAll
  ; lookupSignalPairValid
  ; extractDisjointness
  ; extractMessageValid
  ; extractSignalPairs
  ; lookupDisjointFromDBC
  )
