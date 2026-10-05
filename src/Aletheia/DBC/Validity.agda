-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Formal definition of DBC validity.
--
-- Purpose: Define IsValidDBC as a precise predicate capturing when a DBC's
-- signal layout defines a well-defined partial function from frames to values,
-- and every value its declared ranges admit has an encoding in its bits.
-- Supports CAN 2.0B (DLC 0–8) and CAN-FD (DLC 0–15).
--
-- A DBC is valid when every error-severity condition holds.
-- Warning-severity checks are advisory and NOT part of IsValidDBC.
-- `ValidDBC` is the DBC with its erased proof, the value a loaded session
-- holds; `signalFacts` reads off it what encoding a signal's value needs.
module Aletheia.DBC.Validity where
open import Aletheia.DBC.Identifier using (Identifier; nameStr)

open import Aletheia.DBC.Types using (signalNameStr; messageNameStr; DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Validator using (walkMux)
open import Aletheia.CAN.Encoding.Value.Facts using (bitsRange; SignalFacts)
open import Aletheia.CAN.DBCHelpers using (findSignalInList)
open import Aletheia.DBC.Decidable using (SignalPairValid)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; 0ᵈ; 1ᵈ; _≤ᵈ_; toℚ)
open import Aletheia.DBC.DecRat.RationalRoundtrip using (↥-toℚ-canonical)
open import Data.Rational.Base as ℚ using ()
open import Data.List using (List; []; length)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Properties using (n≢0⇒n>0)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≤_ to _≤ᵣ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; trans; sym)
open import Data.String using (String)
open import Data.Bool using (Bool; true)
open import Data.Product using (_×_; proj₁; proj₂)

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
MuxResolvable sigs (When muxName _) = Any (λ s → signalNameStr s ≡ nameStr muxName) sigs

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

-- Condition 9 (check 26): the declared range lies within the values the
-- signal's bits carry, so every value the range admits has an encoding.
RangeWithinBits : DBCSignal → Set
RangeWithinBits sig =
  let sd = DBCSignal.signalDef sig
  in (proj₁ (bitsRange sd) ≤ᵣ toℚ (SignalDef.minimum sd))
     × (toℚ (SignalDef.maximum sd) ≤ᵣ proj₂ (bitsRange sd))

-- ============================================================================
-- IsValidDBC: conjunction of the error-severity conditions
-- ============================================================================

record IsValidDBC (dbc : DBC) : Set where
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
    -- 9. Declared ranges within what the bits carry
    rangesWithinBits  : All (λ m → All RangeWithinBits (DBCMessage.signals m)) msgs

-- A DBC with the proof that it is valid.  The validator's verdict is its
-- one producer (`Aletheia.DBC.Validated.validate`); the proof is
-- erased, so it costs nothing at run time, and a consumer reads from it any
-- fact it states of the DBC's messages and signals.
record ValidDBC : Set where
  constructor validated
  field
    dbc        : DBC
    @0 isValid : IsValidDBC dbc

-- The facts encoding needs of a signal of a valid DBC, read off where the
-- signal sits.
signalFacts : ∀ {dbc msg sig} → IsValidDBC dbc
  → msg ∈ DBC.messages dbc → sig ∈ DBCMessage.signals msg
  → SignalFacts (DBCSignal.signalDef sig)
signalFacts {sig = sig} v m∈ s∈ = record
  { factor≢0    = nonZeroFactor→factorℚ≢0 {sig} (at IsValidDBC.nonZeroFactors)
  ; bitLength>0 = n≢0⇒n>0 (at IsValidDBC.nonZeroBitLengths)
  ; lowWithin   = proj₁ (at IsValidDBC.rangesWithinBits)
  ; highWithin  = proj₂ (at IsValidDBC.rangesWithinBits)
  }
  where
    at : ∀ {P : DBCSignal → Set}
       → (IsValidDBC _ → All (λ m → All P (DBCMessage.signals m)) _) → P sig
    at field′ = lookup (lookup (field′ v) m∈) s∈

-- ============================================================================
-- WARNING PREDICATES (advisory, not part of IsValidDBC)
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

-- Check 15: start bit inside the message's frame capacity
-- (dlcBytes * 8 — the spec-correct geometry bound; the global
-- max-physical-bits constant remains only as the type-level ceiling).
StartBitInRange : ℕ → DBCSignal → Set
StartBitInRange payloadBytes sig =
  SignalDef.startBit (DBCSignal.signalDef sig) < payloadBytes * 8

-- Check 16: bit length within the message's frame capacity
BitLengthInRange : ℕ → DBCSignal → Set
BitLengthInRange payloadBytes sig =
  SignalDef.bitLength (DBCSignal.signalDef sig) ≤ payloadBytes * 8

-- Check 6: No shared signal names between messages
DisjointSignalNames : List String → List String → Set
DisjointSignalNames names1 names2 = All (λ n → Any (n ≡_) names2 → ⊥) names1

-- Check 13: Component predicates for offset/scale range checking
RangeLowOK : ℚ → ℚ → Set
RangeLowOK physMin declMin = declMin ≤ᵣ physMin

RangeHighOK : ℚ → ℚ → Set
RangeHighOK physMax declMax = physMax ≤ᵣ declMax

-- The values a signal's bits carry lie within its declared range.
BitsWithinRange : DBCSignal → Set
BitsWithinRange sig =
  RangeLowOK (proj₁ (bitsRange (DBCSignal.signalDef sig))) (toℚ (SignalDef.minimum (DBCSignal.signalDef sig)))
  × RangeHighOK (proj₂ (bitsRange (DBCSignal.signalDef sig))) (toℚ (SignalDef.maximum (DBCSignal.signalDef sig)))

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
