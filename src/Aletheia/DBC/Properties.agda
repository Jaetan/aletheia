{-# OPTIONS --safe --without-K #-}

-- Correctness properties for DBC types and validation.
--
-- Purpose: Facade re-exporting all DBC property definitions and proofs
--   from per-topic submodules.
-- Submodules: Equality, Disjointness, WellFormedness.
--
-- Key invariant: For any multiplexor configuration, active signals don't overlap.
module Aletheia.DBC.Properties where

-- Decidable equality for SignalPresence, SignalDef, DBCSignal
open import Aletheia.DBC.Properties.Equality public using
  ( _≟-SignalPresence_
  ; _≟-SignalDef_
  ; _≟-DBCSignal_
  )

-- Signal disjointness (logical and physical), Bool-valued overlap check,
-- equivalence proofs
open import Aletheia.DBC.Properties.Disjointness public using
  ( SignalsDisjoint; disjoint-left; disjoint-right
  ; signalsDisjoint?
  ; signalsDisjoint-sym
  ; PhysicallyDisjoint
  ; physicallyDisjoint-sym
  ; physicallyDisjoint?
  ; buildPhysicalBits
  ; signalPhysicalBits
  ; bitsMemberᵇ
  ; bitsIntersectᵇ
  ; signalsPhysicallyOverlapᵇ
  ; physicallyOverlapᵇ-sound
  ; physicallyOverlapᵇ-complete
  )

-- Signal coexistence, pair validity, message/DBC well-formedness,
-- proof extraction from validated DBCs
open import Aletheia.DBC.Properties.WellFormedness public using
  ( ValuesOverlap; valuesOverlap?; valuesOverlap-sym
  ; CanCoexist; both-always; always-left; always-right
  ; different-mux; same-mux-overlap
  ; canCoexist?; canCoexist-sym
  ; SignalPairValid; mutually-exclusive; disjoint-when-coexist
  ; signalPairValid?; signalPairValid-sym
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
  ; extractFromValidAgainstAll
  ; lookupSignalPairValid
  ; extractDisjointness
  ; extractMessageValid
  ; extractSignalPairs
  ; lookupDisjointFromDBC
  )
