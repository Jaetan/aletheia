-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Facade re-exporting the runtime-facing DBC decision procedures and the
-- predicates they decide, from the per-topic submodules (Equality,
-- Disjointness, WellFormedness).
--
-- The proofs about these predicates — symmetry, soundness/completeness of the
-- fast overlap check, and proof extraction — live under
-- `Aletheia.DBC.Properties.*`.
module Aletheia.DBC.Decidable where

-- Decidable equality for SignalPresence, SignalDef, DBCSignal
open import Aletheia.DBC.Decidable.Equality public using
  ( _≟-SignalPresence_
  ; _≟-SignalDef_
  ; _≟-DBCSignal_
  )

-- Signal disjointness (logical and physical), decision procedures, and the
-- Bool-valued overlap check
open import Aletheia.DBC.Decidable.Disjointness public using
  ( SignalsDisjoint; disjoint-left; disjoint-right
  ; signalsDisjoint?
  ; PhysicallyDisjoint
  ; physicallyDisjoint?
  ; buildPhysicalBits
  ; signalPhysicalBits
  ; Intersects
  ; bitsMember₀
  ; bitsIntersect₀
  ; bitsMemberᵇ
  ; bitsIntersectᵇ
  ; signalsPhysicallyOverlapᵇ
  )

-- Signal coexistence, pair validity, message/DBC well-formedness, and deciders
open import Aletheia.DBC.Decidable.WellFormedness public using
  ( ValuesOverlap; valuesOverlap?
  ; CanCoexist; both-always; always-left; always-right
  ; different-mux; same-mux-overlap
  ; canCoexist?
  ; SignalPairValid; mutually-exclusive; disjoint-when-coexist
  ; signalPairValid?
  ; SignalValidAgainstAll; valid-nil; valid-cons
  ; signalValidAgainstAll?
  ; AllSignalPairsValid; pairs-nil; pairs-cons
  ; allSignalPairsValid?
  ; messageSignalsValid?
  ; SignalRangeConsistent; signalRangeConsistent?
  ; AllSignalRangesConsistent; ranges-nil; ranges-cons
  ; allSignalRangesConsistent?
  ; MessageValid; message-valid; messageValid?
  ; AllMessagesValid; msgs-nil; msgs-cons; allMessagesValid?
  ; DBCValid; dbcValid?
  )
