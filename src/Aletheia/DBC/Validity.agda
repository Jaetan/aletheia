{-# OPTIONS --safe --without-K #-}

-- Formal definition of DBC validity.
--
-- Purpose: Define ValidDBC as a precise predicate capturing when a DBC's
-- signal layout defines a well-defined partial function from frames to values.
-- Supports CAN 2.0B (DLC 0–8) and CAN-FD (DLC 0–15).
--
-- A DBC is valid when all 8 error-severity conditions hold.
-- Warning-severity checks are advisory and NOT part of ValidDBC.
module Aletheia.DBC.Validity where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (signalNameStr; messageNameStr)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using (findSignalPresence; walkMux)
open import Aletheia.CAN.DBCHelpers using (findSignalInList)
open import Aletheia.DBC.Properties using (SignalPairValid)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; 0ᵈ; 1ᵈ; _≤ᵈ_; toℚ)
open import Aletheia.DBC.DecRat.RationalRoundtrip using (↥-toℚ-canonical)
open import Data.Rational.Base as ℚ using ()
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; _∸_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≤_ to _≤ᵣ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; trans; sym)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_)
open import Aletheia.CAN.Constants using (max-physical-bits)

-- ============================================================================
-- PER-SIGNAL PREDICATES
-- ============================================================================

-- Condition 3: Factor numerator is non-zero (at the DecRat-storage level).
-- A canonical DecRat has numerator ≡ +0 iff it represents 0; so this also
-- rules out `factor ≡ 0ᵈ`.
NonZeroFactor : DBCSignal → Set
NonZeroFactor sig = DecRat.numerator (SignalDef.factor (DBCSignal.signalDef sig)) ≢ + 0

-- Bridge: NonZeroFactor → factor ≢ 0ᵈ (contrapositive of numerator 0ᵈ ≡ + 0)
nonZeroFactor→factor≢0 : ∀ {sig} → NonZeroFactor sig
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ᵈ
nonZeroFactor→factor≢0 nzf f≡0 = nzf (cong DecRat.numerator f≡0)

-- ℚ-level bridge: NonZeroFactor → toℚ factor ≢ 0ℚ.  Encoding-layer
-- proofs (Roundtrip, Capstone) operate in ℚ and consume this form.
-- Proof goes via a helper that pattern-matches on `mkDecRat`, so
-- `↥-toℚ-canonical` gets its concrete `num a b c` arguments (its 4th is
-- irrelevant, so the canonical witness can't be extracted via projection).
private
  ↥-toℚ : ∀ (d : DecRat) → ℚ.↥ (toℚ d) ≡ DecRat.numerator d
  ↥-toℚ (mkDecRat num a b c) = ↥-toℚ-canonical num a b c

nonZeroFactor→factorℚ≢0 : ∀ {sig} → NonZeroFactor sig
  → toℚ (SignalDef.factor (DBCSignal.signalDef sig)) ≢ 0ℚ
nonZeroFactor→factorℚ≢0 {sig} nzf toℚfactor≡0 =
  nzf (trans (sym (↥-toℚ (SignalDef.factor (DBCSignal.signalDef sig))))
             (cong ℚ.↥_ toℚfactor≡0))

-- Condition 4: Multiplexor reference resolves (if conditional)
MuxResolvable : List DBCSignal → SignalPresence → Set
MuxResolvable _    Always           = ⊤
MuxResolvable sigs (When muxName _) = Any (λ s → signalNameStr s ≡ Identifier.name muxName) sigs

-- Condition 5: Multiplexor chain is acyclic.
-- Defined in terms of walkMux from Validator: starting from a signal's
-- presence, walking the chain via findSignalPresence reaches Always (or an
-- unresolved reference, caught by check 4) within length sigs steps.
-- Equivalent to: the mux dependency graph (restricted to in-message signals)
-- has no cycle reachable from this signal.
MuxAcyclic : List DBCSignal → SignalPresence → Set
-- Fuel: length sigs — acyclic chain visits each signal at most once.
MuxAcyclic sigs presence = walkMux (length sigs) sigs presence ≡ true

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

-- ============================================================================
-- ValidDBC: conjunction of all 8 error-severity conditions
-- ============================================================================

record ValidDBC (dbc : DBC) : Set where
  private
    msgs = DBC.messages dbc
  field
    -- 1. All message IDs pairwise distinct
    uniqueIds         : AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
    -- 2. Signal names pairwise distinct within each message
    uniqueSigNames    : All (λ m → AllPairs (λ s₁ s₂ → signalNameStr s₁ ≢ signalNameStr s₂)
                                            (DBCMessage.signals m)) msgs
    -- 3. Non-zero factors for all signals
    nonZeroFactors    : All (λ m → All NonZeroFactor (DBCMessage.signals m)) msgs
    -- 4. Multiplexor references resolve
    muxExist          : All (λ m → All (λ sig → MuxResolvable (DBCMessage.signals m)
                                                               (DBCSignal.presence sig))
                                       (DBCMessage.signals m)) msgs
    -- 5. Multiplexor chains are acyclic
    muxAcyclic        : All (λ m → All (λ sig → MuxAcyclic (DBCMessage.signals m)
                                                             (DBCSignal.presence sig))
                                       (DBCMessage.signals m)) msgs
    -- 6. Signal bits fit in frame (dlcBytes extracts byte count from DLC code)
    bitsInFrame       : All (λ m → All (BitsInFrame (dlcBytes (DBCMessage.dlc m)))
                                       (DBCMessage.signals m)) msgs
    -- 7. Coexisting signal pairs are valid (using each message's own DLC byte count)
    sigPairsValid     : All (λ m → AllPairs (SignalPairValid (dlcBytes (DBCMessage.dlc m)))
                                            (DBCMessage.signals m)) msgs
    -- 8. Non-zero bit lengths
    nonZeroBitLengths : All (λ m → All NonZeroBitLength (DBCMessage.signals m)) msgs

-- ============================================================================
-- WARNING PREDICATES (advisory, not part of ValidDBC)
-- ============================================================================

-- Check 7: Signal minimum ≤ maximum (DecRat-level ordering).
MinLeqMax : DBCSignal → Set
MinLeqMax sig =
  SignalDef.minimum (DBCSignal.signalDef sig) ≤ᵈ
  SignalDef.maximum (DBCSignal.signalDef sig)

-- Check 11: Message names pairwise distinct
DistinctMessageNames : DBCMessage → DBCMessage → Set
DistinctMessageNames m1 m2 = messageNameStr m1 ≢ messageNameStr m2

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

-- Check 17: Multiplexor non-unit scaling
-- A mux signal with factor ≠ 1 or offset ≠ 0 produces non-integer physical
-- values, which may silently fail to match the integer mux values in
-- SignalPresence.When.
MuxScalingOK : Maybe DBCSignal → Set
MuxScalingOK nothing = ⊤
MuxScalingOK (just muxSig) =
  SignalDef.factor (DBCSignal.signalDef muxSig) ≡ 1ᵈ
  × SignalDef.offset (DBCSignal.signalDef muxSig) ≡ 0ᵈ

-- Takes SignalPresence directly (not DBCSignal) to allow pattern matching
-- without where-blocks, which are opaque to external proofs.
MuxUnitScaling : List DBCSignal → SignalPresence → Set
MuxUnitScaling _       Always           = ⊤
MuxUnitScaling allSigs (When muxName _) = MuxScalingOK (findSignalInList (Identifier.name muxName) allSigs)
