{-# OPTIONS --safe --without-K #-}

-- Correctness properties for batch signal operations.
--
-- Purpose: Prove correctness of batch extraction/building operations.
-- Architecture: Connects DBC validation (DBCValid) to signal operation proofs.
--
-- Key connection: DBC validation ensures signals are physically disjoint, which is
-- exactly the precondition needed for extract-disjoint-inject proofs in Encoding.
--
-- Proof flow:
--   1. validateDBCFull dbc succeeds → DBCValid dbc
--   2. lookupDisjointFromDBC extracts PhysicallyDisjoint for any two coexisting signals
--   3. PhysicallyDisjoint is the precondition for injectSignal-preserves-disjoint-bits-physical
--   4. Therefore: batch operations on validated DBCs preserve signal values
--
-- Mixed byte orders are fully supported: PhysicallyDisjoint checks physical bit
-- positions rather than logical intervals, so LE/BE signal pairs are handled correctly.
--
module Aletheia.CAN.Batch.Properties where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Encoding using (extractSignal; extractSignalCore; extractionBytes; scaleExtracted; injectSignal; injectSignal-preserves-disjoint-bits-physical)
open import Aletheia.CAN.Encoding.Arithmetic using (inBounds; toSigned; removeScaling)
open import Aletheia.CAN.Endianness using (extractBits)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.BatchExtraction using (ExtractionResults; mkExtractionResults; categorizeResult; combineResults; emptyResults; extractAllSignalsFromMessage)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Properties using (
  PhysicallyDisjoint; physicallyDisjoint-sym; _≟-DBCSignal_;
  SignalPairValid; signalPairValid-sym;
  extractDisjointness; CanCoexist; both-always)

open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _^_; _>_; _∸_; suc; _<?_; _≤?_)
open import Data.Rational using (ℚ; 0ℚ) renaming (_≟_ to _≟ᵣ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat.Properties using (+-suc)
open import Function using (case_of_)

-- ============================================================================
-- PROOF ARCHITECTURE: How DBC validation enables batch operation correctness
-- ============================================================================

-- The key insight is that DBC validation (DBCValid) provides exactly what we need
-- to prove batch operations are correct:
--
-- 1. VALIDATION PHASE (at DBC load time):
--    - parseDBCWithErrors parses JSON to DBC
--    - validateDBCFull checks all signal pairs for physical disjointness
--    - Result: DBCValid dbc (proof that all coexisting signals are physically disjoint)
--
-- 2. PROOF EXTRACTION (when needed for formal proofs):
--    - Given: DBCValid dbc, msg ∈ messages, sig₁ sig₂ ∈ signals msg
--    - lookupDisjointFromDBC extracts: PhysicallyDisjoint sig₁ sig₂
--
-- 3. SIGNAL OPERATION PROOFS (in Encoding):
--    - injectSignal-preserves-disjoint-bits-physical:
--      Given PhysicallyDisjoint, injection at sig₁ doesn't affect extraction at sig₂
--      Works for any byte order combination (LE/LE, BE/BE, LE/BE, BE/LE)
--
-- 4. BATCH OPERATION CORRECTNESS (the conclusion):
--    - buildFrame injects multiple signals
--    - Each signal's value is preserved because all pairs are physically disjoint
--    - This follows by induction using injectSignal-preserves-disjoint-bits-physical

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
--     → PhysicallyDisjoint sig₁ sig₂
--
-- Usage: Given membership proofs (from Any), you can extract disjointness directly.
-- The membership proofs can be computed by searching the list, or provided
-- statically when the DBC structure is known at compile time.

-- ============================================================================
-- CONNECTION TO ENCODING PROOFS
-- ============================================================================

-- The PhysicallyDisjoint proof from above is exactly what the encoding lemma needs.
-- This is defined in Encoding.agda:
--
--   injectSignal-preserves-disjoint-bits-physical :
--     ∀ {n} {len₂} (v : ℚ) (sig : SignalDef) (bo₁ bo₂ : ByteOrder)
--       (frame frame' : CANFrame n) (start₂ : ℕ)
--     → injectSignal v sig bo₁ frame ≡ just frame'
--     → (∀ k₁ → k₁ < bitLength sig → ∀ k₂ → k₂ < len₂
--        → physicalBitPos n bo₁ (startBit sig + k₁) ≢ physicalBitPos n bo₂ (start₂ + k₂))
--     → startBit sig + bitLength sig ≤ n * 8
--     → start₂ + len₂ ≤ n * 8
--     → extractBits {len₂} (extractionBytes frame' bo₂) start₂
--       ≡ extractBits {len₂} (extractionBytes frame bo₂) start₂
--
-- So the proof chain is:
--   DBCValid → PhysicallyDisjoint → injectSignal-preserves-disjoint-bits-physical

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
--   - By injectSignal-preserves-disjoint-bits-physical: since signal i and
--     signal k+1 are physically disjoint (from DBCValid), injection of k+1
--     doesn't affect extraction of i (regardless of byte order combination)
--   - Also need: extracting signal k+1 returns its injected value
--   - By roundtrip property (extractSignal-injectSignal-roundtrip)
--
-- The full formal proof requires:
--   1. Lifting roundtrip to Maybe (handling injection success)
--   2. Inductively composing preservation through the fold
--
-- These are mechanical but lengthy; the key insight is that DBCValid provides
-- exactly the physical disjointness preconditions needed.

-- ============================================================================
-- PAIRWISE DISJOINTNESS FOR SIGNAL LISTS
-- ============================================================================

open import Aletheia.CAN.BatchFrameBuilding using (injectAll)
open import Data.Bool using (true; false)
open import Aletheia.CAN.Encoding.Properties using (
  signalValue;
  injectSignal-reduces-unsigned; injectSignal-reduces-signed;
  extractSignal-reduces-unsigned; extractSignal-reduces-signed;
  SignedFits;
  removeScaling-applyScaling-exact; removeScaling-nothing⇒zero)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Properties using (just-injective)
open import Data.Integer using (ℤ; +_; -[1+_])

-- A signal is physically disjoint from all signals in a list
-- n is the frame byte count (for physicalBitPos)
data DisjointFromAll (n : ℕ) (sig : DBCSignal) : List (DBCSignal × ℚ) → Set where
  dfa-nil : DisjointFromAll n sig []
  dfa-cons : ∀ {s v rest}
    → PhysicallyDisjoint n sig s
    → DisjointFromAll n sig rest
    → DisjointFromAll n sig ((s , v) ∷ rest)

-- All pairs in a signal list are disjoint
data AllPairsDisjoint (n : ℕ) : List (DBCSignal × ℚ) → Set where
  apd-nil : AllPairsDisjoint n []
  apd-cons : ∀ {s v rest}
    → DisjointFromAll n s rest
    → AllPairsDisjoint n rest
    → AllPairsDisjoint n ((s , v) ∷ rest)

-- All signals in a list fit within payloadBytes * 8 bits
data AllSignalsFit (payloadBytes : ℕ) : List (DBCSignal × ℚ) → Set where
  asf-nil : AllSignalsFit payloadBytes []
  asf-cons : ∀ {s v rest}
    → SignalDef.startBit (DBCSignal.signalDef s) + SignalDef.bitLength (DBCSignal.signalDef s) ≤ payloadBytes * 8
    → AllSignalsFit payloadBytes rest
    → AllSignalsFit payloadBytes ((s , v) ∷ rest)

-- ============================================================================
-- SINGLE INJECTION PRESERVES DISJOINT EXTRACTION
-- ============================================================================

-- Helper: Signal fit bounds (parameterized by payload byte count)
signalFits : ℕ → SignalDef → Set
signalFits payloadBytes sig = SignalDef.startBit sig + SignalDef.bitLength sig ≤ payloadBytes * 8

-- ============================================================================
-- HELPER IMPORTS
-- ============================================================================
open import Aletheia.Data.BitVec using (BitVec)
open import Aletheia.Data.BitVec.Conversion using (bitVecToℕ)

-- ============================================================================
-- HELPER: extractSignal depends only on the extracted bits
-- ============================================================================

-- If the extracted bits are the same, extractSignal returns the same result
-- This is because extractSignalCore, scaleExtracted, and inBounds are all deterministic
private
  extractSignal-bits-eq : ∀ {n} (frame₁ frame₂ : CANFrame n) sig bo
    → extractBits {SignalDef.bitLength sig} (extractionBytes frame₁ bo) (SignalDef.startBit sig)
      ≡ extractBits {SignalDef.bitLength sig} (extractionBytes frame₂ bo) (SignalDef.startBit sig)
    → extractSignal frame₁ sig bo ≡ extractSignal frame₂ sig bo
  extractSignal-bits-eq frame₁ frame₂ sig bo bits-eq = result-eq
    where
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

-- PhysicallyDisjoint is sufficient for any byte order combination.
-- This connects injectSignal-preserves-disjoint-bits-physical to the signal level.
single-inject-preserves :
  ∀ {n} (frame frame' : CANFrame n) (s : DBCSignal) (v : ℚ) (sig : DBCSignal)
  → PhysicallyDisjoint n sig s
  → signalFits n (DBCSignal.signalDef s)
  → signalFits n (DBCSignal.signalDef sig)
  → injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame ≡ just frame'
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
single-inject-preserves frame frame' s v sig pd fits-s fits-sig inj-eq =
  extractSignal-bits-eq frame' frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) bits-preserved
  where
    bits-preserved = injectSignal-preserves-disjoint-bits-physical v
      (DBCSignal.signalDef s) (DBCSignal.byteOrder s) (DBCSignal.byteOrder sig)
      frame frame' (SignalDef.startBit (DBCSignal.signalDef sig))
      inj-eq (physicallyDisjoint-sym {_} {sig} {s} pd) fits-s fits-sig

-- ============================================================================
-- KEY LEMMA: injectAll preserves extraction at disjoint positions
-- ============================================================================
-- Requires: pairwise physical disjointness, signals fit in frame.
-- No byte order constraint: works for any mix of LE and BE signals.

injectAll-preserves-disjoint :
  ∀ {n} (sigs : List (DBCSignal × ℚ)) (frame frame' : CANFrame n)
    (sig : DBCSignal)
  → AllSignalsFit n sigs
  → signalFits n (DBCSignal.signalDef sig)
  → injectAll frame sigs ≡ just frame'
  → DisjointFromAll n sig sigs
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)

-- Base case: empty list, frame unchanged
injectAll-preserves-disjoint [] frame .frame sig _ _ refl dfa-nil = refl

-- Inductive case: inject first, then rest
injectAll-preserves-disjoint ((s , v) ∷ rest) frame frame' sig
    (asf-cons s-fits rest-fits) sig-fits eq (dfa-cons disj restDisj)
  with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame in injEq
... | nothing = case eq of λ ()
... | just frame₁ = proof
  where
    restEq : injectAll frame₁ rest ≡ just frame'
    restEq with injectSignal v (DBCSignal.signalDef s) (DBCSignal.byteOrder s) frame
    ... | just _ = eq
    ... | nothing = case injEq of λ ()

    -- By IH: extracting sig from frame' equals extracting from frame₁
    step1 : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step1 = injectAll-preserves-disjoint rest frame₁ frame' sig rest-fits sig-fits restEq restDisj

    -- Single injection preserves disjoint extraction (any byte order combo)
    step2 : extractSignal frame₁ (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    step2 = single-inject-preserves frame frame₁ s v sig disj s-fits sig-fits injEq

    proof : extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
          ≡ extractSignal frame (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
    proof = trans step1 step2

-- ============================================================================
-- SINGLE SIGNAL ROUNDTRIP PREDICATE
-- ============================================================================

-- A (signal, value) pair roundtrips: inject then extract returns v
InjectRoundtrips : ℕ → DBCSignal → ℚ → Set
InjectRoundtrips n sig v =
  ∀ (frame frame' : CANFrame n)
  → injectSignal v (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) frame ≡ just frame'
  → extractSignal frame' (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) ≡ just v

-- All signals in a list roundtrip
data AllRoundtrip (n : ℕ) : List (DBCSignal × ℚ) → Set where
  ar-nil  : AllRoundtrip n []
  ar-cons : ∀ {s v rest}
    → InjectRoundtrips n s v → AllRoundtrip n rest → AllRoundtrip n ((s , v) ∷ rest)

-- ============================================================================
-- BRIDGE LEMMAS: from existing roundtrips to InjectRoundtrips
-- ============================================================================

-- Unsigned signals: bridge from Encoding.Properties roundtrip
roundtrip-unsigned→IR :
  ∀ {m} (n : ℕ) (sig : DBCSignal)
  → inBounds (signalValue (+ n) (DBCSignal.signalDef sig))
             (SignalDef.minimum (DBCSignal.signalDef sig))
             (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ false
  → signalFits m (DBCSignal.signalDef sig)
  → n < 2 ^ SignalDef.bitLength (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig (signalValue (+ n) (DBCSignal.signalDef sig))
roundtrip-unsigned→IR n sig bounds-ok factor≢0 unsigned fits n<2^bl frame frame' inj-eq =
  subst (λ f → extractSignal f sd bo ≡ just v) frame'-eq extract-reduces
  where
    sd = DBCSignal.signalDef sig
    bo = DBCSignal.byteOrder sig
    v  = signalValue (+ n) sd
    inject-reduces = injectSignal-reduces-unsigned n sd bo frame bounds-ok factor≢0 n<2^bl
    frame'-eq      = just-injective (trans (sym inject-reduces) inj-eq)
    extract-reduces = extractSignal-reduces-unsigned n sd bo frame bounds-ok unsigned fits n<2^bl

-- Signed signals: bridge from Encoding.Properties roundtrip
roundtrip-signed→IR :
  ∀ {m} (z : ℤ) (sig : DBCSignal)
  → inBounds (signalValue z (DBCSignal.signalDef sig))
             (SignalDef.minimum (DBCSignal.signalDef sig))
             (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ true
  → SignalDef.bitLength (DBCSignal.signalDef sig) > 0
  → SignedFits z (SignalDef.bitLength (DBCSignal.signalDef sig))
  → signalFits m (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig (signalValue z (DBCSignal.signalDef sig))
roundtrip-signed→IR z sig bounds-ok factor≢0 signed bl>0 sf fits frame frame' inj-eq =
  subst (λ f → extractSignal f sd bo ≡ just v) frame'-eq extract-reduces
  where
    sd = DBCSignal.signalDef sig
    bo = DBCSignal.byteOrder sig
    v  = signalValue z sd
    inject-reduces  = injectSignal-reduces-signed z sd bo frame bounds-ok factor≢0 bl>0 sf
    frame'-eq       = just-injective (trans (sym inject-reduces) inj-eq)
    extract-reduces = extractSignal-reduces-signed z sd bo frame bounds-ok signed bl>0 sf fits

-- ============================================================================
-- BATCH ROUNDTRIP: extracting any injected signal returns its value
-- ============================================================================

injectAll-roundtrip :
  ∀ {n} (sigs : List (DBCSignal × ℚ)) (frame frame' : CANFrame n)
  → AllPairsDisjoint n sigs
  → AllSignalsFit n sigs
  → AllRoundtrip n sigs
  → injectAll frame sigs ≡ just frame'
  → ∀ {s v} → (s , v) ∈ sigs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v

-- Empty list: membership impossible
injectAll-roundtrip [] _ _ _ _ _ _ ()

-- Cons case: decompose injection, split on membership
injectAll-roundtrip ((s₀ , v₀) ∷ rest) frame frame'
    (apd-cons dfa apd-rest) (asf-cons s₀-fits asf-rest) (ar-cons ir₀ ar-rest) eq mem
  with injectSignal v₀ (DBCSignal.signalDef s₀) (DBCSignal.byteOrder s₀) frame in injEq
... | nothing = case eq of λ ()
... | just frame₁ = go mem
  where
    restEq : injectAll frame₁ rest ≡ just frame'
    restEq with injectSignal v₀ (DBCSignal.signalDef s₀) (DBCSignal.byteOrder s₀) frame
    ... | just _  = eq
    ... | nothing = case injEq of λ ()

    go : ∀ {s v} → (s , v) ∈ ((s₀ , v₀) ∷ rest)
       → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
    -- Head signal: roundtrip + preservation through remaining injections
    go (here refl) = trans preserve (ir₀ frame frame₁ injEq)
      where
        preserve = injectAll-preserves-disjoint rest frame₁ frame' s₀
                     asf-rest s₀-fits restEq dfa
    -- Tail signal: inductive hypothesis with intermediate frame
    go (there mem') = injectAll-roundtrip rest frame₁ frame' apd-rest asf-rest ar-rest restEq mem'

-- ============================================================================
-- EXTRACTALLSIGNALS COMPLETENESS
-- ============================================================================

-- Total entries across all three partitions
totalEntries : ExtractionResults → ℕ
totalEntries r = length (ExtractionResults.values r)
               + length (ExtractionResults.errors r)
               + length (ExtractionResults.absent r)

private
  -- Arithmetic: adding 1 to middle partition gives suc of total
  shift-mid : ∀ a b c → a + suc b + c ≡ suc (a + b + c)
  shift-mid a b c = cong (_+ c) (+-suc a b)

  -- Arithmetic: adding 1 to last partition gives suc of total
  shift-last : ∀ a b c → a + b + suc c ≡ suc (a + b + c)
  shift-last a b c = +-suc (a + b) c

-- Completeness: extractAllSignalsFromMessage produces exactly one entry per signal.
-- Each signal is categorized into exactly one partition (values, errors, or absent).
extractAll-complete : ∀ {n} (frame : CANFrame n) msg
  → totalEntries (extractAllSignalsFromMessage frame msg)
    ≡ length (DBCMessage.signals msg)
extractAll-complete frame msg = go (DBCMessage.signals msg)
  where
    f : DBCSignal → ExtractionResults
    f sig = categorizeResult (DBCSignal.name sig)
              (extractSignalDirect msg frame sig)

    go : ∀ sigs → totalEntries (foldr combineResults emptyResults (map f sigs))
                  ≡ length sigs
    go [] = refl
    go (sig ∷ sigs)
      with extractSignalDirect msg frame sig
         | foldr combineResults emptyResults (map f sigs) | go sigs
    ... | Success _              | mkExtractionResults vs es as | ih =
      cong suc ih
    ... | SignalNotInDBC         | mkExtractionResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent _     | mkExtractionResults vs es as | ih =
      trans (shift-last (length vs) (length es) (length as)) (cong suc ih)
    ... | ValueOutOfBounds _ _ _ | mkExtractionResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | ExtractionFailed _     | mkExtractionResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)

-- ============================================================================
-- CAPSTONE THEOREM: ValidDBC → batch roundtrip correctness
-- ============================================================================

-- Additional imports for capstone
import Data.List.Relation.Unary.All as StdAll
import Data.List.Relation.Unary.AllPairs as StdAP
open import Aletheia.DBC.Validity using (ValidDBC; nonZeroFactor→factor≢0; BitsInFrame)
open import Data.Empty using (⊥-elim)

-- --------------------------------------------------------------------------
-- Predicates for capstone preconditions
-- --------------------------------------------------------------------------

-- All signals in the list are always-present (not multiplexed)
data AllAlwaysPresent : List (DBCSignal × ℚ) → Set where
  aap-nil  : AllAlwaysPresent []
  aap-cons : ∀ {s v rest}
    → DBCSignal.presence s ≡ Always
    → AllAlwaysPresent rest
    → AllAlwaysPresent ((s , v) ∷ rest)

-- All signals come from a specific message
data AllFromMessage : List (DBCSignal × ℚ) → DBCMessage → Set where
  afm-nil  : ∀ {msg} → AllFromMessage [] msg
  afm-cons : ∀ {s v rest msg}
    → s ∈ DBCMessage.signals msg
    → AllFromMessage rest msg
    → AllFromMessage ((s , v) ∷ rest) msg

-- Signals in the list are pairwise distinct (as DBCSignal values)
data DistinctFromAll (s : DBCSignal) : List (DBCSignal × ℚ) → Set where
  dist-nil  : DistinctFromAll s []
  dist-cons : ∀ {s' v rest}
    → s ≢ s'
    → DistinctFromAll s rest
    → DistinctFromAll s ((s' , v) ∷ rest)

data PairsDistinct : List (DBCSignal × ℚ) → Set where
  pd-nil  : PairsDistinct []
  pd-cons : ∀ {s v rest}
    → DistinctFromAll s rest
    → PairsDistinct rest
    → PairsDistinct ((s , v) ∷ rest)

-- --------------------------------------------------------------------------
-- Decidable checkers for capstone preconditions
-- --------------------------------------------------------------------------

-- Helper: is a SignalPresence equal to Always?
private
  isAlways? : (p : SignalPresence) → Dec (p ≡ Always)
  isAlways? Always     = yes refl
  isAlways? (When _ _) = no (λ ())

-- Decidable AllAlwaysPresent: check each signal's presence
allAlwaysPresent? : (pairs : List (DBCSignal × ℚ)) → Dec (AllAlwaysPresent pairs)
allAlwaysPresent? [] = yes aap-nil
allAlwaysPresent? ((s , v) ∷ rest) with isAlways? (DBCSignal.presence s)
... | no ¬a = no λ { (aap-cons eq _) → ¬a eq }
... | yes a with allAlwaysPresent? rest
...   | no ¬ar = no λ { (aap-cons _ ar) → ¬ar ar }
...   | yes ar = yes (aap-cons a ar)

-- Decidable AllFromMessage: check each signal's membership
open import Data.List.Membership.DecPropositional {A = DBCSignal} _≟-DBCSignal_ using (_∈?_)

allFromMessage? : (pairs : List (DBCSignal × ℚ)) → (msg : DBCMessage)
                → Dec (AllFromMessage pairs msg)
allFromMessage? [] msg = yes afm-nil
allFromMessage? ((s , v) ∷ rest) msg with s ∈? DBCMessage.signals msg
... | no ¬s∈ = no λ { (afm-cons s∈ _) → ¬s∈ s∈ }
... | yes s∈ with allFromMessage? rest msg
...   | no ¬ar = no λ { (afm-cons _ ar) → ¬ar ar }
...   | yes ar = yes (afm-cons s∈ ar)

-- Decidable DistinctFromAll: check one signal against rest
private
  distinctFromAll? : (s : DBCSignal) → (rest : List (DBCSignal × ℚ))
                   → Dec (DistinctFromAll s rest)
  distinctFromAll? s [] = yes dist-nil
  distinctFromAll? s ((s' , v) ∷ rest) with s ≟-DBCSignal s'
  ... | yes eq = no λ { (dist-cons s≢ _) → s≢ eq }
  ... | no s≢ with distinctFromAll? s rest
  ...   | no ¬dr = no λ { (dist-cons _ dr) → ¬dr dr }
  ...   | yes dr = yes (dist-cons s≢ dr)

-- Decidable PairsDistinct: triangular check
pairsDistinct? : (pairs : List (DBCSignal × ℚ)) → Dec (PairsDistinct pairs)
pairsDistinct? [] = yes pd-nil
pairsDistinct? ((s , v) ∷ rest) with distinctFromAll? s rest
... | no ¬da = no λ { (pd-cons da _) → ¬da da }
... | yes da with pairsDistinct? rest
...   | no ¬pr = no λ { (pd-cons _ pr) → ¬pr pr }
...   | yes pr = yes (pd-cons da pr)

-- --------------------------------------------------------------------------
-- Gap 1: ValidDBC → AllPairsDisjoint
-- --------------------------------------------------------------------------

private
  -- Lookup in stdlib AllPairs (analogous to lookupSignalPairValid for AllSignalPairsValid)
  allPairs-lookup : ∀ {n sig₁ sig₂ sigs}
    → StdAP.AllPairs (SignalPairValid n) sigs
    → sig₁ ∈ sigs → sig₂ ∈ sigs → sig₁ ≢ sig₂
    → SignalPairValid n sig₁ sig₂
  allPairs-lookup (hd StdAP.∷ _) (here refl) (there sig₂∈) _ =
    StdAll.lookup hd sig₂∈
  allPairs-lookup (hd StdAP.∷ _) (there sig₁∈) (here refl) _ =
    signalPairValid-sym (StdAll.lookup hd sig₁∈)
  allPairs-lookup (_ StdAP.∷ rest) (there sig₁∈) (there sig₂∈) sig≢ =
    allPairs-lookup rest sig₁∈ sig₂∈ sig≢
  allPairs-lookup _ (here refl) (here refl) sig≢ = ⊥-elim (sig≢ refl)

  -- Build DisjointFromAll from ValidDBC evidence
  -- n is the frame byte count for PhysicallyDisjoint
  buildDFA : ∀ {n msg} (s : DBCSignal) (rest : List (DBCSignal × ℚ))
    → StdAP.AllPairs (SignalPairValid n) (DBCMessage.signals msg)
    → s ∈ DBCMessage.signals msg
    → DBCSignal.presence s ≡ Always
    → AllFromMessage rest msg
    → AllAlwaysPresent rest
    → DistinctFromAll s rest
    → DisjointFromAll n s rest
  buildDFA _ [] _ _ _ _ _ _ = dfa-nil
  buildDFA s ((s' , _) ∷ rest) ap s∈ refl
      (afm-cons s'∈ afm-rest) (aap-cons refl aap-rest) (dist-cons s≢s' dist-rest) =
    dfa-cons
      (extractDisjointness (allPairs-lookup ap s∈ s'∈ s≢s') both-always)
      (buildDFA s rest ap s∈ refl afm-rest aap-rest dist-rest)

-- Bridge: ValidDBC → AllPairsDisjoint for always-present, distinct signals from one message
-- Uses the message's DLC as the frame byte count for disjointness checking
validDBC→allPairsDisjoint : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllAlwaysPresent pairs
  → AllFromMessage pairs msg
  → PairsDistinct pairs
  → AllPairsDisjoint (DBCMessage.dlc msg) pairs
validDBC→allPairsDisjoint [] _ _ _ _ _ = apd-nil
validDBC→allPairsDisjoint ((s , v) ∷ rest) vdbc msg∈
    (aap-cons ps aap-rest) (afm-cons s∈ afm-rest) (pd-cons dist pd-rest) =
  apd-cons
    (buildDFA s rest ap s∈ ps afm-rest aap-rest dist)
    (validDBC→allPairsDisjoint rest vdbc msg∈ aap-rest afm-rest pd-rest)
  where
    ap = StdAll.lookup (ValidDBC.sigPairsValid vdbc) msg∈

-- --------------------------------------------------------------------------
-- Gap 2: ValidDBC → AllSignalsFit
-- --------------------------------------------------------------------------

private
  buildASF : ∀ {msg} (pairs : List (DBCSignal × ℚ))
    → StdAll.All (BitsInFrame (DBCMessage.dlc msg)) (DBCMessage.signals msg)
    → AllFromMessage pairs msg
    → AllSignalsFit (DBCMessage.dlc msg) pairs
  buildASF [] _ _ = asf-nil
  buildASF ((s , _) ∷ rest) bifs (afm-cons s∈ afm-rest) =
    asf-cons
      (StdAll.lookup bifs s∈)
      (buildASF rest bifs afm-rest)

-- Bridge: ValidDBC → AllSignalsFit for signals from one message.
-- Uses the message's own DLC as the payload byte count.
validDBC→allSignalsFit : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllFromMessage pairs msg
  → AllSignalsFit (DBCMessage.dlc msg) pairs
validDBC→allSignalsFit pairs vdbc msg∈ afm =
  buildASF pairs
    (StdAll.lookup (ValidDBC.bitsInFrame vdbc) msg∈)
    afm

-- --------------------------------------------------------------------------
-- Gap 5: Capstone theorem
-- --------------------------------------------------------------------------

-- Top-level: ValidDBC guarantees batch roundtrip for always-present signals.
--
-- For any byte order combination, if signals are pairwise distinct and
-- always-present (derived from ValidDBC → physically disjoint), fit in the
-- frame (derived from BitsInFrame), and you inject representable values,
-- then extracting any injected signal returns exactly its injected value.
--
-- Both AllPairsDisjoint and AllSignalsFit are derived internally from ValidDBC.
-- The frame size is the message's DLC (works for both CAN 2.0B and CAN-FD).
validDBC-roundtrip :
  ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
    (frame frame' : CANFrame (DBCMessage.dlc msg))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllAlwaysPresent pairs
  → AllFromMessage pairs msg
  → PairsDistinct pairs
  → AllRoundtrip (DBCMessage.dlc msg) pairs
  → injectAll frame pairs ≡ just frame'
  → ∀ {s v} → (s , v) ∈ pairs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
validDBC-roundtrip pairs frame frame' vdbc msg∈ aap afm pd ar eq mem =
  injectAll-roundtrip pairs frame frame'
    (validDBC→allPairsDisjoint pairs vdbc msg∈ aap afm pd)
    (validDBC→allSignalsFit pairs vdbc msg∈ afm)
    ar eq mem

-- ============================================================================
-- REPRESENTABLE: decidable value representability for capstone theorem
-- ============================================================================

-- A value v is representable for signal sig when v = signalValue raw sig
-- for some raw integer that fits in the signal's bit representation.
data Representable (sig : DBCSignal) (v : ℚ) : Set where
  repr-unsigned : (n : ℕ)
    → v ≡ signalValue (+ n) (DBCSignal.signalDef sig)
    → inBounds v (SignalDef.minimum (DBCSignal.signalDef sig))
                  (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
    → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ false
    → n < 2 ^ SignalDef.bitLength (DBCSignal.signalDef sig)
    → Representable sig v
  repr-signed : (z : ℤ)
    → v ≡ signalValue z (DBCSignal.signalDef sig)
    → inBounds v (SignalDef.minimum (DBCSignal.signalDef sig))
                  (SignalDef.maximum (DBCSignal.signalDef sig)) ≡ true
    → SignalDef.isSigned (DBCSignal.signalDef sig) ≡ true
    → SignalDef.bitLength (DBCSignal.signalDef sig) > 0
    → SignedFits z (SignalDef.bitLength (DBCSignal.signalDef sig))
    → Representable sig v

-- Decidable representability checker (requires non-zero factor from ValidDBC)
representable? : (sig : DBCSignal) (v : ℚ)
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → Dec (Representable sig v)
representable? sig v factor≢0 = go (removeScaling v factor offset) refl
  where
    sd = DBCSignal.signalDef sig
    open SignalDef sd

    +-inj : ∀ {m n : ℕ} → (+ m) ≡ (+ n) → m ≡ n
    +-inj refl = refl

    -- Uniqueness: any raw value witnessing Representable must equal the candidate
    raw≡z : ∀ {raw z} → removeScaling v factor offset ≡ just z
          → v ≡ signalValue raw sd → raw ≡ z
    raw≡z {raw} remEq v≡ = just-injective
      (trans (sym (removeScaling-applyScaling-exact raw factor offset factor≢0))
             (trans (cong (λ x → removeScaling x factor offset) (sym v≡)) remEq))

    -- Signed fits decision for each ℤ constructor
    goSF : ∀ z → removeScaling v factor offset ≡ just z → signalValue z sd ≡ v
         → inBounds v minimum maximum ≡ true → isSigned ≡ true
         → bitLength > 0 → Dec (Representable sig v)
    goSF (+ n) remEq sv≡v bEq isEq bl>0 with n <? 2 ^ (bitLength ∸ 1)
    ... | yes n< = yes (repr-signed (+ n) (sym sv≡v) bEq isEq bl>0 n<)
    ... | no ¬n< = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed z' v≡ _ _ _ sf) →
            ¬n< (subst (λ r → SignedFits r bitLength) (raw≡z {z'} remEq v≡) sf)
    goSF -[1+ n ] remEq sv≡v bEq isEq bl>0 with suc n ≤? 2 ^ (bitLength ∸ 1)
    ... | yes sn≤ = yes (repr-signed -[1+ n ] (sym sv≡v) bEq isEq bl>0 sn≤)
    ... | no ¬sn≤ = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed z' v≡ _ _ _ sf) →
            ¬sn≤ (subst (λ r → SignedFits r bitLength) (raw≡z {z'} remEq v≡) sf)

    -- isSigned dispatch
    goIS : ∀ b → isSigned ≡ b → ∀ z → removeScaling v factor offset ≡ just z
         → signalValue z sd ≡ v → inBounds v minimum maximum ≡ true
         → Dec (Representable sig v)
    goIS false isEq (+ n) remEq sv≡v bEq with n <? 2 ^ bitLength
    ... | yes n< = yes (repr-unsigned n (sym sv≡v) bEq isEq n<)
    ... | no ¬n< = no λ where
          (repr-unsigned n' v≡ _ _ n'<) →
            ¬n< (subst (_< 2 ^ bitLength) (+-inj (raw≡z {+ n'} remEq v≡)) n'<)
          (repr-signed _ _ _ s _ _) → case trans (sym isEq) s of λ ()
    goIS false isEq -[1+ _ ] remEq _ _ = no λ where
        (repr-unsigned n v≡ _ _ _) → case raw≡z {+ n} remEq v≡ of λ ()
        (repr-signed _ _ _ s _ _) → case trans (sym isEq) s of λ ()
    goIS true isEq z remEq sv≡v bEq with 0 <? bitLength
    ... | no ¬bl>0 = no λ where
          (repr-unsigned _ _ _ u _) → case trans (sym isEq) u of λ ()
          (repr-signed _ _ _ _ bl>0 _) → ¬bl>0 bl>0
    ... | yes bl>0 = goSF z remEq sv≡v bEq isEq bl>0

    -- Main decision: removeScaling → value check → bounds → signedness
    go : (r : Maybe ℤ) → removeScaling v factor offset ≡ r → Dec (Representable sig v)
    go nothing remEq = ⊥-elim (factor≢0 (removeScaling-nothing⇒zero v factor offset remEq))
    go (just z) remEq with signalValue z sd ≟ᵣ v
    ... | no sv≢v = no λ where
          (repr-unsigned n v≡ _ _ _) →
            sv≢v (subst (λ r → signalValue r sd ≡ v) (raw≡z {+ n} remEq v≡) (sym v≡))
          (repr-signed z' v≡ _ _ _ _) →
            sv≢v (subst (λ r → signalValue r sd ≡ v) (raw≡z {z'} remEq v≡) (sym v≡))
    ... | yes sv≡v with inBounds v minimum maximum in bEq
    ...   | false = no λ where
            (repr-unsigned _ _ b _ _) → case trans (sym bEq) b of λ ()
            (repr-signed _ _ b _ _ _) → case trans (sym bEq) b of λ ()
    ...   | true = goIS isSigned refl z remEq sv≡v bEq

-- Bridge: Representable → InjectRoundtrips (given factor ≢ 0 and signalFits)
representable→roundtrips : ∀ {m sig v}
  → Representable sig v
  → SignalDef.factor (DBCSignal.signalDef sig) ≢ 0ℚ
  → signalFits m (DBCSignal.signalDef sig)
  → InjectRoundtrips m sig v
representable→roundtrips {_} {sig} (repr-unsigned n v≡ bounds-ok unsigned n<) factor≢0 fits =
  subst (InjectRoundtrips _ sig) (sym v≡)
    (roundtrip-unsigned→IR n sig
      (subst (λ x → inBounds x (SignalDef.minimum sd) (SignalDef.maximum sd) ≡ true) v≡ bounds-ok)
      factor≢0 unsigned fits n<)
  where sd = DBCSignal.signalDef sig
representable→roundtrips {_} {sig} (repr-signed z v≡ bounds-ok signed bl>0 sf) factor≢0 fits =
  subst (InjectRoundtrips _ sig) (sym v≡)
    (roundtrip-signed→IR z sig
      (subst (λ x → inBounds x (SignalDef.minimum sd) (SignalDef.maximum sd) ≡ true) v≡ bounds-ok)
      factor≢0 signed bl>0 sf fits)
  where sd = DBCSignal.signalDef sig

-- All signals in a list are representable
data AllRepresentable : List (DBCSignal × ℚ) → Set where
  arep-nil  : AllRepresentable []
  arep-cons : ∀ {s v rest}
    → Representable s v → AllRepresentable rest
    → AllRepresentable ((s , v) ∷ rest)

-- Decidable checker for AllRepresentable (requires non-zero factors)
allRepresentable? : (pairs : List (DBCSignal × ℚ))
  → StdAll.All (λ { (s , _) → SignalDef.factor (DBCSignal.signalDef s) ≢ 0ℚ }) pairs
  → Dec (AllRepresentable pairs)
allRepresentable? [] _ = yes arep-nil
allRepresentable? ((s , v) ∷ rest) (f≢0 StdAll.∷ fs) with representable? s v f≢0
... | no ¬r = no λ { (arep-cons r _) → ¬r r }
... | yes r with allRepresentable? rest fs
...   | no ¬ar = no λ { (arep-cons _ ar) → ¬ar ar }
...   | yes ar = yes (arep-cons r ar)

-- Bridge: AllRepresentable → AllRoundtrip (given ValidDBC context)
-- Uses the message's DLC as the frame byte count.
allRepresentable→allRoundtrip : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → ValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllFromMessage pairs msg
  → AllRepresentable pairs
  → AllRoundtrip (DBCMessage.dlc msg) pairs
allRepresentable→allRoundtrip [] _ _ _ _ = ar-nil
allRepresentable→allRoundtrip ((s , v) ∷ rest) vdbc msg∈
    (afm-cons s∈ afm-rest) (arep-cons rep arep-rest) =
  ar-cons
    (representable→roundtrips rep
      (nonZeroFactor→factor≢0 {s} (StdAll.lookup nzfs s∈))
      (StdAll.lookup bifs s∈))
    (allRepresentable→allRoundtrip rest vdbc msg∈ afm-rest arep-rest)
  where
    nzfs = StdAll.lookup (ValidDBC.nonZeroFactors vdbc) msg∈
    bifs = StdAll.lookup (ValidDBC.bitsInFrame vdbc) msg∈
