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
open import Data.Fin using (toℕ)
open import Data.Rational using (ℚ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

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
