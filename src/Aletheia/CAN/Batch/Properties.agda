{-# OPTIONS --safe --without-K #-}

-- Correctness properties for batch signal operations.
--
-- Purpose: Prove correctness of batch extraction/building operations.
-- Architecture: Connects DBC validation (DBCValid) to signal operation proofs.
--
-- Key connection: DBC validation ensures signals are disjoint, which is exactly
-- the precondition needed for extract-disjoint-inject proofs in Encoding/Properties.
--
-- Proof flow:
--   1. validateDBC dbc succeeds → DBCValid dbc
--   2. lookupDisjointFromDBC extracts SignalsDisjoint for any two coexisting signals
--   3. SignalsDisjoint is the precondition for extract-disjoint-inject-*
--   4. Therefore: batch operations on validated DBCs preserve signal values
--
module Aletheia.CAN.Batch.Properties where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.DBC.Types
open import Aletheia.DBC.Properties using (
  SignalsDisjoint; disjoint-left; disjoint-right;
  SignalPairValid; CanCoexist;
  DBCValid; MessageValid; AllSignalPairsValid;
  signalsDisjoint-sym; canCoexist-sym;
  lookupSignalPairValid; extractDisjointness; lookupDisjointFromDBC;
  extractMessageValid; extractSignalPairs)

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Rational using (ℚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)

-- ============================================================================
-- PROOF ARCHITECTURE: How DBC validation enables batch operation correctness
-- ============================================================================

-- The key insight is that DBC validation (DBCValid) provides exactly what we need
-- to prove batch operations are correct:
--
-- 1. VALIDATION PHASE (at DBC load time):
--    - parseDBCWithErrors parses JSON to DBC
--    - validateDBC checks all signal pairs for disjointness
--    - Result: DBCValid dbc (proof that all coexisting signals are disjoint)
--
-- 2. PROOF EXTRACTION (when needed for formal proofs):
--    - Given: DBCValid dbc, msg ∈ messages, sig₁ sig₂ ∈ signals msg
--    - lookupDisjointFromDBC extracts: SignalsDisjoint sig₁ sig₂
--
-- 3. SIGNAL OPERATION PROOFS (in Encoding/Properties):
--    - extract-disjoint-inject-unsigned/signed:
--      Given SignalsDisjoint, injection at sig₁ doesn't affect extraction at sig₂
--
-- 4. BATCH OPERATION CORRECTNESS (the conclusion):
--    - buildFrame injects multiple signals
--    - Each signal's value is preserved because all pairs are disjoint
--    - This follows by induction using extract-disjoint-inject

-- ============================================================================
-- EXAMPLE: Using lookupDisjointFromDBC
-- ============================================================================

-- The function lookupDisjointFromDBC (from DBC.Properties) has this signature:
--
--   lookupDisjointFromDBC : ∀ {dbc msg sig₁ sig₂}
--     → DBCValid dbc
--     → msg ∈ DBC.messages dbc
--     → sig₁ ∈ DBCMessage.signals msg
--     → sig₂ ∈ DBCMessage.signals msg
--     → sig₁ ≢ sig₂
--     → CanCoexist (DBCSignal.presence sig₁) (DBCSignal.presence sig₂)
--     → SignalsDisjoint (DBCSignal.signalDef sig₁) (DBCSignal.signalDef sig₂)
--
-- Usage: Given membership proofs (from Any), you can extract disjointness directly.
-- The membership proofs can be computed by searching the list, or provided
-- statically when the DBC structure is known at compile time.

-- ============================================================================
-- CONNECTION TO ENCODING PROOFS
-- ============================================================================

-- The SignalsDisjoint proof from above is exactly what extract-disjoint-inject needs.
-- This is defined in Encoding/Properties.agda:
--
--   extract-disjoint-inject-unsigned :
--     ∀ (n : ℕ) (sig₁ sig₂ : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
--     → SignalsDisjoint sig₁ sig₂  -- ← Provided by lookupDisjointFromDBC!
--     → (bounds-ok₁ : ...)
--     → (factor≢0 : ...)
--     → (n<2^bl : ...)
--     → (fits₁ : ...)
--     → (fits₂ : ...)
--     → extractSignal (resultOf (injectSignal ...)) sig₂ bo
--       ≡ extractSignal frame sig₂ bo
--
-- So the proof chain is:
--   DBCValid → SignalsDisjoint → extract-disjoint-inject succeeds

-- ============================================================================
-- BATCH OPERATION CORRECTNESS: The Full Picture
-- ============================================================================

-- For buildFrame with n signals from a validated DBC:
--
-- Base case (n = 0):
--   Empty frame, nothing to prove.
--
-- Inductive case (n = k + 1):
--   - Inject signal k+1 into frame that already has signals 1..k
--   - Need to show: extracting any signal i ∈ 1..k still returns correct value
--   - By extract-disjoint-inject: since signal i and signal k+1 are disjoint
--     (from DBCValid), injection of k+1 doesn't affect extraction of i
--   - Also need: extracting signal k+1 returns its injected value
--   - By roundtrip property (extractSignal-injectSignal-roundtrip)
--
-- The full formal proof requires:
--   1. Lifting roundtrip to Maybe (handling injection success)
--   2. Inductively composing extract-disjoint-inject through the fold
--   3. Careful handling of byte order consistency
--
-- These are mechanical but lengthy; the key insight is that DBCValid provides
-- exactly the disjointness preconditions needed.

-- ============================================================================
-- PAIRWISE DISJOINTNESS FOR SIGNAL LISTS
-- ============================================================================

open import Aletheia.CAN.BatchFrameBuilding using (injectOne; injectAll)
open import Aletheia.CAN.Endianness using (injectBits; extractBits; injectBits-preserves-disjoint; swapBytes)
open import Data.Maybe using (_>>=_)
open import Data.Vec using (Vec)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (trans; cong; subst; sym)

-- A signal is disjoint from all signals in a list
data DisjointFromAll (sig : DBCSignal) : List (DBCSignal × ℚ) → Set where
  dfa-nil : DisjointFromAll sig []
  dfa-cons : ∀ {s v rest}
    → SignalsDisjoint (DBCSignal.signalDef sig) (DBCSignal.signalDef s)
    → DisjointFromAll sig rest
    → DisjointFromAll sig ((s , v) ∷ rest)

-- All pairs in a signal list are disjoint
data AllPairsDisjoint : List (DBCSignal × ℚ) → Set where
  apd-nil : AllPairsDisjoint []
  apd-cons : ∀ {s v rest}
    → DisjointFromAll s rest
    → AllPairsDisjoint rest
    → AllPairsDisjoint ((s , v) ∷ rest)

-- All signals in a list fit within 64 bits
data AllSignalsFit : List (DBCSignal × ℚ) → Set where
  asf-nil : AllSignalsFit []
  asf-cons : ∀ {s v rest}
    → SignalDef.startBit (DBCSignal.signalDef s) + SignalDef.bitLength (DBCSignal.signalDef s) ≤ 64
    → AllSignalsFit rest
    → AllSignalsFit ((s , v) ∷ rest)

-- ============================================================================
-- SINGLE INJECTION PRESERVES DISJOINT EXTRACTION
-- ============================================================================

-- Helper: Signal fit bounds (used in many places)
signalFits : SignalDef → Set
signalFits sig = SignalDef.startBit sig + SignalDef.bitLength sig ≤ 64

-- Convert SignalsDisjoint to the ⊎ form for injectBits-preserves-disjoint
open import Aletheia.DBC.Properties using (SignalsDisjoint; disjoint-left; disjoint-right)

SignalsDisjoint→⊎ : ∀ {sig₁ sig₂} → SignalsDisjoint sig₁ sig₂
  → SignalDef.startBit sig₁ + SignalDef.bitLength sig₁ ≤ SignalDef.startBit sig₂
  ⊎ SignalDef.startBit sig₂ + SignalDef.bitLength sig₂ ≤ SignalDef.startBit sig₁
SignalsDisjoint→⊎ (disjoint-left p) = inj₁ p
SignalsDisjoint→⊎ (disjoint-right p) = inj₂ p

-- ============================================================================
-- THE KEY SEMANTIC PROPERTY
-- ============================================================================
--
-- What we need to prove:
--
--   SignalsDisjoint sig₁ sig₂
--   → injection at sig₁ with bo₁ doesn't affect extraction at sig₂ with bo₂
--
-- ANALYSIS BY BYTE ORDER COMBINATION:
--
--   Let A = byte range touched by [s₁, s₁+l₁)
--   Let B = byte range touched by [s₂, s₂+l₂)
--   Let π = swapBytes (byte reversal)
--
--   SignalsDisjoint gives: A ∩ B = ∅ (in logical bit space)
--
--   Case LE/LE: inject touches A, extract reads B → need A ∩ B = ∅ ✓
--   Case BE/BE: inject touches π(A), extract reads π(B) → need π(A) ∩ π(B) = ∅
--               Since π is bijection and A ∩ B = ∅, we have π(A) ∩ π(B) = ∅ ✓
--   Case LE/BE: inject touches A, extract reads π(B) → need A ∩ π(B) = ∅
--               This does NOT follow from A ∩ B = ∅ alone! ✗
--   Case BE/LE: inject touches π(A), extract reads B → need π(A) ∩ B = ∅
--               This does NOT follow from A ∩ B = ∅ alone! ✗
--
-- COUNTEREXAMPLE for mixed byte orders:
--   s₁ = 0, l₁ = 8 (byte 0)    with LE → modifies byte 0
--   s₂ = 56, l₂ = 8 (byte 7)   with BE → reads swapBytes, so reads original byte 0!
--   SignalsDisjoint holds ([0,8) ∩ [56,64) = ∅) but they DO interfere.
--
-- CONCLUSION:
--   - Same byte order: SignalsDisjoint is SUFFICIENT
--   - Mixed byte orders: Need stronger condition (physical disjointness)
--
-- For now, we require same byte order for batch operations.
-- CAN messages typically use consistent byte order for all signals anyway.
--
-- ============================================================================

-- ============================================================================
-- SAME BYTE ORDER CONSTRAINT
-- ============================================================================

-- All signals in a list use the same byte order
data AllSameByteOrderAs (bo : ByteOrder) : List (DBCSignal × ℚ) → Set where
  asbo-nil : AllSameByteOrderAs bo []
  asbo-cons : ∀ {s v rest}
    → DBCSignal.byteOrder s ≡ bo
    → AllSameByteOrderAs bo rest
    → AllSameByteOrderAs bo ((s , v) ∷ rest)

-- ============================================================================
-- DISJOINTNESS + SAME BYTE ORDER: Concrete single-inject-preserves
-- ============================================================================

-- Import the key lemma from Endianness
open import Aletheia.CAN.Endianness using (injectPayload-preserves-disjoint-same; payloadIso; extractBits; injectBits)
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ)

-- ============================================================================
-- HELPER: extractSignal depends only on the extracted bits
-- ============================================================================

-- If the extracted bits are the same, extractSignal returns the same result
-- This is because extractSignalCore, scaleExtracted, and inBounds are all deterministic
private
  extractSignal-bits-eq : ∀ frame₁ frame₂ sig bo
    → extractBits {SignalDef.bitLength sig} (extractionBytes frame₁ bo) (SignalDef.startBit sig)
      ≡ extractBits {SignalDef.bitLength sig} (extractionBytes frame₂ bo) (SignalDef.startBit sig)
    → extractSignal frame₁ sig bo ≡ extractSignal frame₂ sig bo
  extractSignal-bits-eq frame₁ frame₂ sig bo bits-eq = result-eq
    where
      open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCore; extractionBytes; scaleExtracted; inBounds; toSigned)
      open SignalDef sig

      bytes₁ = extractionBytes frame₁ bo
      bytes₂ = extractionBytes frame₂ bo

      -- extractSignalCore uses extractBits, so equal bits → equal core
      core-eq : extractSignalCore bytes₁ sig ≡ extractSignalCore bytes₂ sig
      core-eq = cong (λ bits → toSigned (bitVecToℕ bits) bitLength isSigned) bits-eq

      -- scaleExtracted only depends on the core
      value-eq : scaleExtracted (extractSignalCore bytes₁ sig) sig
               ≡ scaleExtracted (extractSignalCore bytes₂ sig) sig
      value-eq = cong (λ core → scaleExtracted core sig) core-eq

      -- inBounds only depends on the value
      bounds-eq : inBounds (scaleExtracted (extractSignalCore bytes₁ sig) sig) minimum maximum
                ≡ inBounds (scaleExtracted (extractSignalCore bytes₂ sig) sig) minimum maximum
      bounds-eq = cong (λ v → inBounds v minimum maximum) value-eq

      -- The final result: if then else with same condition and same branches
      result-eq : extractSignal frame₁ sig bo ≡ extractSignal frame₂ sig bo
      result-eq with inBounds (scaleExtracted (extractSignalCore bytes₁ sig) sig) minimum maximum
                   | inBounds (scaleExtracted (extractSignalCore bytes₂ sig) sig) minimum maximum
                   | bounds-eq
      ... | true  | true  | _  = cong just value-eq
      ... | false | false | _  = refl
      ... | true  | false | ()
      ... | false | true  | ()

-- When injection and extraction use the same byte order, SignalsDisjoint suffices
-- This connects injectSignal-preserves-disjoint-bits to the signal level
single-inject-preserves-same-bo :
  ∀ (frame frame' : CANFrame) (s : DBCSignal) (v : ℚ) (sig : DBCSignal)
  → DBCSignal.byteOrder s ≡ DBCSignal.byteOrder sig  -- SAME byte order
  → SignalsDisjoint (DBCSignal.signalDef sig) (DBCSignal.signalDef s)
  → signalFits (DBCSignal.signalDef s)
  → signalFits (DBCSignal.signalDef sig)
  → injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame ≡ just frame'
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
single-inject-preserves-same-bo frame frame' s v sig bo-eq disj fits-s fits-sig inj-eq
  rewrite sym bo-eq = extractSignal-bits-eq frame' frame sig-sig bo bits-preserved
  where
    open import Aletheia.CAN.Encoding using (extractSignal; extractionBytes; injectSignal; injectSignal-preserves-disjoint-bits)

    bo = DBCSignal.byteOrder s
    sig-s = DBCSignal.signalDef s
    sig-sig = DBCSignal.signalDef sig

    start-sig = SignalDef.startBit sig-sig
    len-sig = SignalDef.bitLength sig-sig

    -- Disjointness in ⊎ form (swapped for the lemma signature)
    disj⊎ : SignalDef.startBit sig-s + SignalDef.bitLength sig-s ≤ start-sig
          ⊎ start-sig + len-sig ≤ SignalDef.startBit sig-s
    disj⊎ with SignalsDisjoint→⊎ disj
    ... | inj₁ p = inj₂ p  -- sig ends before s starts
    ... | inj₂ p = inj₁ p  -- s ends before sig starts

    -- Use the lemma from Encoding.agda
    bits-preserved : extractBits {len-sig} (extractionBytes frame' bo) start-sig
                   ≡ extractBits {len-sig} (extractionBytes frame bo) start-sig
    bits-preserved = injectSignal-preserves-disjoint-bits v sig-s bo frame frame' start-sig
                       inj-eq disj⊎ fits-s fits-sig

-- ============================================================================
-- KEY LEMMA: injectAll preserves extraction at disjoint positions
-- ============================================================================
-- Requires: same byte order for all signals, pairwise disjointness, signals fit in 64 bits

injectAll-preserves-disjoint :
  ∀ (bo : ByteOrder) (sigs : List (DBCSignal × ℚ)) (frame frame' : CANFrame)
    (sig : DBCSignal)
  → DBCSignal.byteOrder sig ≡ bo
  → AllSameByteOrderAs bo sigs
  → AllSignalsFit sigs
  → signalFits (DBCSignal.signalDef sig)
  → injectAll frame sigs ≡ just frame'
  → DisjointFromAll sig sigs
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)

-- Base case: empty list, frame unchanged
injectAll-preserves-disjoint bo [] frame .frame sig _ _ _ _ refl dfa-nil = refl

-- Inductive case: inject first, then rest
injectAll-preserves-disjoint bo ((s , v) ∷ rest) frame frame' sig
    sig-bo-eq (asbo-cons s-bo-eq rest-bo) (asf-cons s-fits rest-fits) sig-fits eq (dfa-cons disj restDisj)
  with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame in injEq
... | nothing = case eq of λ ()  -- injectOne failed, contradicts eq
... | just frame₁ = proof
  where
    -- injectAll frame₁ rest ≡ just frame'
    restEq : injectAll frame₁ rest ≡ just frame'
    restEq with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame
    ... | just _ = eq
    ... | nothing = case injEq of λ ()

    -- By IH: extracting sig from frame' equals extracting from frame₁
    step1 : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step1 = injectAll-preserves-disjoint bo rest frame₁ frame' sig sig-bo-eq rest-bo rest-fits sig-fits restEq restDisj

    -- Byte orders match: s and sig both use bo
    bo-match : DBCSignal.byteOrder s ≡ DBCSignal.byteOrder sig
    bo-match = trans s-bo-eq (sym sig-bo-eq)

    -- Single injection preserves disjoint extraction (same byte order)
    step2 : extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step2 = single-inject-preserves-same-bo frame frame₁ s v sig bo-match disj s-fits sig-fits injEq

    proof : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    proof = trans step1 step2

-- ============================================================================
-- EXTRACTALLSIGNALS COMPLETENESS
-- ============================================================================

-- extractAllSignals partitions signals into (values, errors, absent).
-- Completeness: every signal appears in exactly one partition.
--
-- This is true by construction:
--   extractAllSignalsFromMessage dbc frame msg =
--     foldr combineResults emptyResults (map extractOne (DBCMessage.signals msg))
--
-- Each signal in DBCMessage.signals msg is processed by extractOne,
-- which categorizes it into exactly one partition based on ExtractionResult.
-- combineResults concatenates partitions, preserving this property.
--
-- The proof would be by induction on the signal list, showing that
-- foldr preserves the "each signal in exactly one partition" invariant.
