{-# OPTIONS --safe --without-K #-}

-- Formal definition of DBC validity.
--
-- Purpose: Define ValidDBC as a precise predicate capturing when a DBC's
-- signal layout defines a well-defined partial function from frames to values.
-- Supports CAN 2.0B (DLC 0–8) and CAN-FD (DLC 0–15).
--
-- A DBC is valid when all 9 error-severity conditions hold.
-- Warning-severity checks are advisory and NOT part of ValidDBC.
module Aletheia.DBC.Validity where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using (findSignalPresence)
open import Aletheia.DBC.Properties using (SignalPairValid)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.DLC using (bytesToDlc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; _∸_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≤_ to _≤ᵣ_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_)
open import Aletheia.Prelude using (max-physical-bits)

-- ============================================================================
-- PER-SIGNAL PREDICATES
-- ============================================================================

-- Condition 3: Factor numerator is non-zero
NonZeroFactor : DBCSignal → Set
NonZeroFactor sig = ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≢ + 0

-- Bridge: NonZeroFactor → factor ≢ 0ℚ (contrapositive of ↥p≡0⇒p≡0)
-- If numerator ≢ +0, then the rational itself ≢ 0ℚ (since numerator 0ℚ = +0)
nonZeroFactor→factor≢0 : ∀ {sig} → NonZeroFactor sig
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
nonZeroFactor→factor≢0 nzf f≡0 = nzf (cong ℚ.numerator f≡0)

-- Condition 4: Multiplexor reference resolves (if conditional)
MuxResolvable : List DBCSignal → SignalPresence → Set
MuxResolvable _    Always           = ⊤
MuxResolvable sigs (When muxName _) = Any (λ s → DBCSignal.name s ≡ muxName) sigs

-- Condition 5: Multiplexor signal (if found) is always-present
-- Defined in terms of findSignalPresence from Validator (first-match lookup)
MuxAPLookup : Maybe SignalPresence → Set
MuxAPLookup nothing            = ⊤
MuxAPLookup (just Always)      = ⊤
MuxAPLookup (just (When _ _))  = ⊥

MuxIsAlways : List DBCSignal → SignalPresence → Set
MuxIsAlways _    Always           = ⊤
MuxIsAlways sigs (When muxName _) = MuxAPLookup (findSignalPresence muxName sigs)

-- Condition 6 (check 8): Signal bits fit in frame
-- After convertStartBit at parse time, the internal startBit is in a
-- canonical representation where startBit + bitLength ≤ payloadBytes * 8
-- holds for both LE and BE byte orders.
BitsInFrame : ℕ → DBCSignal → Set
BitsInFrame payloadBytes sig =
  SignalDef.startBit (DBCSignal.signalDef sig)
  + SignalDef.bitLength (DBCSignal.signalDef sig) ≤ payloadBytes * 8

-- Condition 8 (check 10): Non-zero bit length
NonZeroBitLength : DBCSignal → Set
NonZeroBitLength sig = SignalDef.bitLength (DBCSignal.signalDef sig) ≢ 0

-- Condition 9 (check 12): Valid DLC
-- DBCMessage.dlc stores the byte count. Valid byte counts are exactly
-- {0,1,2,3,4,5,6,7,8,12,16,20,24,32,48,64} — the values for which
-- bytesToDlc succeeds. This rejects invalid intermediate values like
-- 9, 10, 11, 13, etc.
ValidDLC : DBCMessage → Set
ValidDLC m = Is-just (bytesToDlc (DBCMessage.dlc m))

-- ============================================================================
-- ValidDBC: conjunction of all 9 error-severity conditions
-- ============================================================================

record ValidDBC (dbc : DBC) : Set where
  private
    msgs = DBC.messages dbc
  field
    -- 1. All message IDs pairwise distinct
    uniqueIds         : AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
    -- 2. Signal names pairwise distinct within each message
    uniqueSigNames    : All (λ m → AllPairs (λ s₁ s₂ → DBCSignal.name s₁ ≢ DBCSignal.name s₂)
                                            (DBCMessage.signals m)) msgs
    -- 3. Non-zero factors for all signals
    nonZeroFactors    : All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs
    -- 4. Multiplexor references resolve
    muxExist          : All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                                               (DBCSignal.presence sig))
                                       (DBCMessage.signals m)) msgs
    -- 5. Multiplexor signals are always-present
    muxAlwaysPresent  : All (λ m → All (λ sig → MuxIsAlways (DBCMessage.signals m)
                                                             (DBCSignal.presence sig))
                                       (DBCMessage.signals m)) msgs
    -- 6. Signal bits fit in frame (dlc is byte count)
    bitsInFrame       : All (λ m → All (BitsInFrame (DBCMessage.dlc m))
                                       (DBCMessage.signals m)) msgs
    -- 7. Coexisting signal pairs are valid (using each message's own DLC)
    sigPairsValid     : All (λ m → AllPairs (SignalPairValid (DBCMessage.dlc m))
                                            (DBCMessage.signals m)) msgs
    -- 8. Non-zero bit lengths
    nonZeroBitLengths : All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs
    -- 9. Valid DLCs
    validDLCs         : All ValidDLC msgs

-- ============================================================================
-- WARNING PREDICATES (advisory, not part of ValidDBC)
-- ============================================================================

-- Check 7: Signal minimum ≤ maximum
MinLeqMax : DBCSignal → Set
MinLeqMax sig =
  SignalDef.minimum (DBCSignal.signalDef sig) ≤ᵣ
  SignalDef.maximum (DBCSignal.signalDef sig)

-- Check 11: Message names pairwise distinct
DistinctMessageNames : DBCMessage → DBCMessage → Set
DistinctMessageNames m1 m2 = DBCMessage.name m1 ≢ DBCMessage.name m2

-- Check 14: Message has at least one signal
NonEmptySignals : DBCMessage → Set
NonEmptySignals msg = DBCMessage.signals msg ≢ []

-- Check 15: startBit < max-physical-bits
StartBitInRange : DBCSignal → Set
StartBitInRange sig =
  SignalDef.startBit (DBCSignal.signalDef sig) < max-physical-bits

-- Check 16: bitLength ≤ max-physical-bits
BitLengthInRange : DBCSignal → Set
BitLengthInRange sig =
  SignalDef.bitLength (DBCSignal.signalDef sig) ≤ max-physical-bits

-- Check 6: No shared signal names between messages
DisjointSignalNames : List String → List String → Set
DisjointSignalNames names1 names2 = All (λ n → Any (n ≡_) names2 → ⊥) names1

-- Check 13: Component predicates for offset/scale range checking
RangeLowOK : ℚ → ℚ → Set
RangeLowOK physMin declMin = declMin ≤ᵣ physMin

RangeHighOK : ℚ → ℚ → Set
RangeHighOK physMax declMax = physMax ≤ᵣ declMax

-- Composed range check, parameterized by factor sign
RangeBoundsOK : Bool → ℚ → ℚ → ℚ → ℚ → Set
RangeBoundsOK false physA physB declMin declMax = RangeLowOK physA declMin × RangeHighOK physB declMax
RangeBoundsOK true  physA physB declMin declMax = RangeLowOK physB declMin × RangeHighOK physA declMax
