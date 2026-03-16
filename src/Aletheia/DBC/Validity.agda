{-# OPTIONS --safe --without-K #-}

-- Formal definition of DBC validity.
--
-- Purpose: Define ValidDBC as a precise predicate capturing when a DBC's
-- signal layout defines a well-defined partial function from frames to values.
-- Scope: CAN 2.0B (8-byte frames). CAN FD deferred to Phase 5.
--
-- A DBC is valid when all 9 error-severity conditions hold.
-- Warning-severity checks are advisory and NOT part of ValidDBC.
module Aletheia.DBC.Validity where

open import Aletheia.DBC.Types
open import Aletheia.DBC.Validator using (findSignalPresence)
open import Aletheia.DBC.Properties using (SignalPairValid)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; suc; _≤_)
open import Data.Nat as Nat using (_/_)
open import Data.Integer using (ℤ; +_)
open import Data.Rational using (ℚ)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- ============================================================================
-- PER-SIGNAL PREDICATES
-- ============================================================================

-- Condition 3: Factor numerator is non-zero
NonZeroFactor : DBCSignal → Set
NonZeroFactor sig = ℚ.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≢ + 0

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
BitsInFrameLE : ℕ → SignalDef → Set
BitsInFrameLE dlc sd = SignalDef.startBit sd + SignalDef.bitLength sd ≤ dlc * 8

BitsInFrameBE : ℕ → SignalDef → Set
BitsInFrameBE dlc sd = suc (7 ∸ (SignalDef.startBit sd Nat./ 8)) ≤ dlc

BitsInFrame : ℕ → DBCSignal → Set
BitsInFrame dlc sig with DBCSignal.byteOrder sig
... | LittleEndian = BitsInFrameLE dlc (DBCSignal.signalDef sig)
... | BigEndian    = BitsInFrameBE dlc (DBCSignal.signalDef sig)

-- Condition 8 (check 10): Non-zero bit length
NonZeroBitLength : DBCSignal → Set
NonZeroBitLength sig = SignalDef.bitLength (DBCSignal.signalDef sig) ≢ 0

-- Condition 9 (check 12): Valid DLC (≤ 8)
ValidDLC : DBCMessage → Set
ValidDLC m = DBCMessage.dlc m ≤ 8

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
    -- 6. Signal bits fit in frame
    bitsInFrame       : All (λ m → All (BitsInFrame (DBCMessage.dlc m))
                                       (DBCMessage.signals m)) msgs
    -- 7. Coexisting signal pairs are valid
    sigPairsValid     : All (λ m → AllPairs SignalPairValid (DBCMessage.signals m)) msgs
    -- 8. Non-zero bit lengths
    nonZeroBitLengths : All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs
    -- 9. Valid DLCs
    validDLCs         : All ValidDLC msgs
