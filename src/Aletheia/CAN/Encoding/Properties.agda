{-# OPTIONS --safe --without-K #-}

-- Phase 3 verification: Some proofs still TODO (marked with {- TODO Phase 3: ... -} comments)

-- Correctness properties for CAN signal encoding/decoding.
--
-- Purpose: Prove round-trip correctness and non-overlap for signal operations.
-- Strategy: BitVec-based architecture - structural proofs, not arithmetic:
--   Layer 0: BitVec operations (structural) - PROVEN in BitVec module
--   Layer 1: BitVec ↔ ℕ conversion - proven ONCE in Conversion module
--   Layer 2: Integer conversion (ℕ ↔ ℤ) - no ℚ
--   Layer 3: Scaling (ℤ ↔ ℚ) - isolated ℚ lemmas
--   Layer 4: Composition - combine all layers
--
-- Philosophy: Bit independence is structural, not arithmetic.
-- The hard proofs (testBit-setBit) are now trivial because we use the right representation.
module Aletheia.CAN.Encoding.Properties where

open import Aletheia.CAN.Encoding
open import Aletheia.CAN.Endianness
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.Data.BitVec
open import Aletheia.Data.BitVec.Conversion
open import Data.Vec using (Vec)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; _>_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; floor)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_; _≤_ to _≤ᵣ_; _/_ to _/ᵣ_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Function using (_∘_; _↔_)

-- ============================================================================
-- LAYER 0: BIT-LEVEL PROPERTIES (STRUCTURAL - from BitVec module)
-- ============================================================================

-- The old arithmetic-based approach required 10-14 hours of proofs about:
-- - Power-of-2 independence
-- - Carry propagation
-- - Modular arithmetic
--
-- The new structural approach: Already proven in BitVec module (30 minutes total)!
--
-- From Aletheia.Data.BitVec:
-- - testBit-setBit-same : testBit (setBit bits k v) k ≡ v (3 lines)
-- - testBit-setBit-diff : testBit (setBit bits k₁ v) k₂ ≡ testBit bits k₂  (6 lines)
-- - setBit-setBit-comm : Disjoint setBit operations commute (6 lines)
--
-- These proofs work because BitVec = Vec Bool, not ℕ + arithmetic.
-- Bit independence is structural, not a theorem.

{- TODO Phase 3: Bit-level roundtrip proof

   Property: extractBits-injectBits-roundtrip (NEW ARCHITECTURE)
   -------------------------------------------------------------
   Extracting after injecting returns the original bitvector

   NEW SIGNATURE (BitVec-based):
   ∀ {length} (bytes : Vec Byte 8) (startBit : ℕ) (bits : BitVec length)
   → (startBit + length ≤ 64)  -- Bits stay within frame
   → extractBits (injectBits bytes startBit bits) startBit ≡ bits

   Proof strategy (MUCH SIMPLER than arithmetic approach):
   - Induction on length
   - Base case ([]): Trivial, both sides return []
   - Inductive case (b ∷ bs):
     * extractBits (injectBits bytes start (b ∷ bs)) start
     * = (testBit (setBit byte idx b) idx) ∷ (extractBits (injectBits bytes' ...) ...)
     * = b ∷ bs  (by testBit-setBit-same + IH)

   Required lemmas (ALL PROVEN in BitVec module):
   - testBit-setBit-same : ✅ PROVEN (3 lines, structural induction)
   - testBit-setBit-diff : ✅ PROVEN (6 lines, structural induction)

   Estimated difficulty: LOW (2-3 hours, just composition)
   Total proof effort with new architecture: ~3 hours vs 10-14 hours!

   The key insight: Once you give structure a name (BitVec = Vec Bool),
   the proofs stop fighting you.
-}

{- TODO Phase 3: Other bit-level proofs

   Property: injectBits-preserves-disjoint
   ----------------------------------------
   Injecting bits doesn't affect other bit ranges (non-overlap)

   Property: injectBits-commute
   ----------------------------
   Injecting multiple values to disjoint ranges commutes
-}

-- ============================================================================
-- LAYER 2: INTEGER CONVERSION PROPERTIES (no ℚ)
-- ============================================================================
-- These proofs work with ℕ ↔ ℤ conversion (two's complement).
-- Still no rational arithmetic.

{- TODO Phase 3: Integer conversion round-trip proofs -}

-- Property: Converting to signed then back to unsigned preserves value
-- (for values that fit in the bit width)
fromSigned-toSigned-roundtrip : ∀ (raw : ℕ) (bitLength : ℕ) (isSigned : Bool)
  → (bitLength > 0)
  → (raw < 2 ^ bitLength)
  → fromSigned (toSigned raw bitLength isSigned) bitLength ≡ raw
fromSigned-toSigned-roundtrip raw bitLength false bitLength>0 raw-bounded =
  -- Unsigned case: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
fromSigned-toSigned-roundtrip raw bitLength true bitLength>0 raw-bounded
  with (2 ^ (bitLength ∸ 1)) Data.Nat.≤ᵇ raw
... | false =
  -- Not negative: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
... | true =
  -- Negative case: prove (2 ^ bitLength) ∸ (suc ((2 ^ bitLength) ∸ raw ∸ 1)) ≡ raw
  -- Key insight: suc (x ∸ 1) ≡ x when x > 0
  -- We have: (2 ^ bitLength) ∸ raw > 0 since raw < 2 ^ bitLength
  trans (cong ((2 ^ bitLength) ∸_) suc-m∸1≡m) (m∸[m∸n]≡n (<⇒≤ raw-bounded))
  where
    open import Data.Nat using (_≤ᵇ_)
    open import Data.Nat.Properties using (m∸[m∸n]≡n; <⇒≤; m>n⇒m∸n≢0)
    open import Relation.Binary.PropositionalEquality using (trans; cong)
    open import Data.Empty using (⊥-elim)

    -- Prove: suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    -- By cases on (2 ^ bitLength) ∸ raw
    suc-m∸1≡m : suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    suc-m∸1≡m with (2 ^ bitLength) ∸ raw | m>n⇒m∸n≢0 raw-bounded
    ... | zero | ≢0 = ⊥-elim (≢0 refl)  -- Contradiction: can't be zero
    ... | suc n | _ = refl  -- suc (suc n ∸ 1) = suc n ∸ 0 = suc n ✓

{- TODO Phase 3: toSigned-fromSigned-roundtrip and fromSigned-bounded

   These require more complex two's complement reasoning.
   Defer for now while we prove bit-level properties first.
-}

-- ============================================================================
-- LAYER 3: SCALING PROPERTIES (isolated ℚ lemmas)
-- ============================================================================
-- These are the ONLY proofs involving rational arithmetic.
-- They are isolated and small.

{- TODO Phase 3: Scaling round-trip proofs

   Property: removeScaling-applyScaling-roundtrip
   -----------------------------------------------
   Removing then applying scaling returns original value (modulo floor)

   ∀ (value : ℚ) (factor offset : ℚ)
   → (factor-nonzero : ¬ (factor ≡ 0ℚ))
   → removeScaling value factor offset >>= (λ raw →
       just (applyScaling raw factor offset)) ≡ just value
     ⊎  -- OR (due to floor precision loss):
     ∃ λ (raw : ℤ) →
       removeScaling value factor offset ≡ just raw
       × (let result = applyScaling raw factor offset
          in (result +ᵣ factor) ≡ value ⊎ (result -ᵣ factor) ≡ value)

   Proof strategy:
   - HARD due to floor operation
   - Exact roundtrip only when (value - offset) / factor has no fractional part
   - Otherwise, floor introduces bounded error (< 1 * factor)
   - Estimated difficulty: HIGH (4-6 hours)
   - Dependencies: Data.Rational.Properties, floor properties

   Property: applyScaling-injective
   ---------------------------------
   applyScaling is injective when factor ≠ 0

   ∀ (raw₁ raw₂ : ℤ) (factor offset : ℚ)
   → (factor-nonzero : ¬ (factor ≡ 0ℚ))
   → applyScaling raw₁ factor offset ≡ applyScaling raw₂ factor offset
   → raw₁ ≡ raw₂

   Proof strategy:
   - Straightforward rational arithmetic
   - Estimated difficulty: LOW-MEDIUM (1-2 hours)

   Property: removeScaling-factor-zero-iff-nothing
   ------------------------------------------------
   removeScaling returns nothing only when factor is zero

   ∀ (value factor offset : ℚ)
   → (removeScaling value factor offset ≡ nothing) ↔ (factor ≡ 0ℚ)

   Proof strategy:
   - Follows from implementation
   - Estimated difficulty: LOW (1 hour)
-}

-- ============================================================================
-- LAYER 4: COMPOSITION - FULL ROUNDTRIP
-- ============================================================================
-- Combine all layers into the full signal extraction/injection proof

-- Helper: Define when a signal definition is well-formed
record WellFormedSignal (sig : SignalDef) : Set where
  field
    startBit-bounded : toℕ (SignalDef.startBit sig) < 64
    bitLength-positive : toℕ (SignalDef.bitLength sig) > 0
    bitLength-fits : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64
    factor-nonzero : ¬ (SignalDef.factor sig ≡ 0ℚ)
    ranges-consistent : SignalDef.minimum sig ≤ᵣ SignalDef.maximum sig

{- TODO Phase 3: Full round-trip theorem

   Theorem: extractSignal-injectSignal-roundtrip
   ----------------------------------------------
   Extracting after injecting returns the original value
   This is the main correctness property, built from all layers

   ∀ (value : SignalValue) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
   → WellFormedSignal sig
   → (value-in-bounds : inBounds value (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
   → injectSignal value sig byteOrder frame >>= (λ frame' →
       extractSignal frame' sig byteOrder) ≡ just value

   Proof strategy:
   - Expand definitions of extractSignal and injectSignal
   - Apply layer 1-3 lemmas in sequence:
     1. Bit-level roundtrip (extractBits ∘ injectBits)
     2. Integer conversion roundtrip (toSigned ∘ fromSigned)
     3. Scaling roundtrip (applyScaling ∘ removeScaling)
   - Estimated difficulty: MEDIUM (2-3 hours)
   - Dependencies: All layer 1-3 lemmas
-}

-- ============================================================================
-- NON-OVERLAP PROPERTIES (bit-level, no ℚ)
-- ============================================================================
-- Prove that signals with disjoint bit ranges don't interfere

-- Definition: Two signals are disjoint if their bit ranges don't overlap
data SignalsDisjoint (sig₁ sig₂ : SignalDef) : Set where
  disjoint-left :
    toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁)
      ≤ toℕ (SignalDef.startBit sig₂)
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂)
      ≤ toℕ (SignalDef.startBit sig₁)
    → SignalsDisjoint sig₁ sig₂

{- TODO Phase 3: Non-overlap proofs

   Theorem: disjoint-signals-commute
   ----------------------------------
   Injecting disjoint signals commutes (order doesn't matter)

   ∀ (value₁ value₂ : SignalValue) (sig₁ sig₂ : SignalDef) (order : ByteOrder) (frame : CANFrame)
   → SignalsDisjoint sig₁ sig₂
   → WellFormedSignal sig₁
   → WellFormedSignal sig₂
   → (injectSignal value₁ sig₁ order frame >>= injectSignal value₂ sig₂ order)
     ≡ (injectSignal value₂ sig₂ order frame >>= injectSignal value₁ sig₁ order)

   Proof strategy:
   - Combine bit-level commutativity (injectBits-commute)
   - Show endianness swaps don't affect disjointness
   - Estimated difficulty: MEDIUM (2-3 hours)

   Theorem: extract-disjoint-inject
   ---------------------------------
   Extracting a signal is unaffected by injecting a disjoint signal

   ∀ (value : SignalValue) (sig₁ sig₂ : SignalDef) (order : ByteOrder) (frame : CANFrame)
   → SignalsDisjoint sig₁ sig₂
   → WellFormedSignal sig₁
   → WellFormedSignal sig₂
   → injectSignal value sig₁ order frame >>= (λ frame' →
       extractSignal frame' sig₂ order)
     ≡ extractSignal frame sig₂ order

   Proof strategy:
   - Use injectBits-preserves-disjoint
   - Show disjointness preserved through scaling/conversion layers
   - Estimated difficulty: MEDIUM (2-3 hours)
-}

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================
{-
Proof Strategy:
===============

This module uses postulates for now (Phase 3 cleanup). Actual proofs will be
added incrementally:

LAYER 1 (Bit operations):
- extractBits-injectBits-roundtrip: Prove by induction on length
  - Base case (length = 0): trivial
  - Inductive case: use properties of div, mod, and bit operations
  - Estimated difficulty: MEDIUM (2-3 hours)
  - Dependencies: Data.Nat.DivMod properties, bit operation lemmas

- injectBits-preserves-disjoint: Prove by showing bit ranges don't overlap
  - Use properties of div/mod to show byte indices differ
  - Estimated difficulty: MEDIUM-HIGH (3-4 hours)
  - Dependencies: Disjointness of div/mod ranges

- injectBits-commute: Follows from injectBits-preserves-disjoint
  - Estimated difficulty: LOW (1 hour)
  - Dependencies: Previous two lemmas

LAYER 2 (Integer conversion):
- fromSigned-toSigned-roundtrip: Prove by cases on isSigned
  - Unsigned case: trivial (identity)
  - Signed case: two's complement arithmetic
  - Estimated difficulty: MEDIUM (2-3 hours)
  - Dependencies: Two's complement properties, Data.Integer lemmas

- toSigned-fromSigned-roundtrip: Similar to above
  - Estimated difficulty: MEDIUM (2-3 hours)

- fromSigned-bounded: Prove by cases on sign of ℤ
  - Estimated difficulty: LOW (1 hour)

LAYER 3 (Scaling - the tricky part):
- removeScaling-applyScaling-roundtrip: HARD DUE TO FLOOR
  - Exact roundtrip only when (value - offset) / factor has no fractional part
  - Otherwise, floor introduces bounded error (< 1 * factor)
  - Estimated difficulty: HIGH (4-6 hours)
  - Dependencies: Data.Rational.Properties, floor properties
  - Strategy: Prove bounded error, not exact equality

- applyScaling-injective: Straightforward rational arithmetic
  - Estimated difficulty: LOW-MEDIUM (1-2 hours)
  - Dependencies: Data.Rational.Properties

- removeScaling-factor-zero-iff-nothing: Follows from implementation
  - Estimated difficulty: LOW (1 hour)

LAYER 4 (Composition):
- extractSignal-injectSignal-roundtrip: Combine all previous lemmas
  - Estimated difficulty: MEDIUM (2-3 hours)
  - Dependencies: All layer 1-3 lemmas
  - Strategy: Expand definitions, apply layer lemmas in sequence

NON-OVERLAP:
- disjoint-signals-commute: Combine bit-level commutativity
  - Estimated difficulty: MEDIUM (2-3 hours)
  - Dependencies: Layer 1 and 4 lemmas

- extract-disjoint-inject: Similar to above
  - Estimated difficulty: MEDIUM (2-3 hours)

TOTAL ESTIMATED TIME: 25-35 hours of proof work

This is why we start with postulates! Each postulate is:
- Clearly stated (no hand-waving)
- Reasonable (follows from known properties)
- Isolated (doesn't pollute other modules)
- Documented with proof strategy

Phase 3 proper will fill these in systematically.
-}
