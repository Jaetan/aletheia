{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the frame processing path.
--
-- Purpose: Prove properties of handleDataFrame — the core function called by
--          both the JSON path (processJSONLine) and the binary FFI entry point
--          (processFrameDirect in Main.agda).
-- These proofs are about the code that actually runs in production.
--
-- Properties:
--   (1) handleDataFrame-guards: non-Streaming state → state unchanged
--   (2) mod-identity-byte: justifies the Haskell shim's bytesToAgdaVec
--       skipping % 256 for Word8 inputs
--   (3) classifyStepResult/stepProperty: classify result faithfully reflects stepL
--   (4) dispatchIterResult: nothing → Ack, just → PropertyResponse
--   (5) handleDataFrame-streaming: decomposition into dispatchIterResult ∘ iterate ∘ stepProperty
--   (6) handleDataFrame-ack-sound: Ack response ⇒ no property violated
--   (7) handleDataFrame-violation-sound: PropertyResponse ⇒ some property violated
--  (14) handleDataFrame-ack-complete: no property violated ⇒ Ack response
--  (15) handleDataFrame-violation-complete: some property violated ⇒ PropertyResponse
--   (8) collectAtoms-faithful: atom indices in indexFormula look up correctly
--   (9) mkPredTable-lookup: mkPredTable evaluates the looked-up predicate
--  (10) lookupCache-updateCache-hit: looking up after updateCache returns new value
--  (11) lookupCache-updateCache-miss: updating one name doesn't affect other lookups
--  (12) updateSignals-step-hit/miss: updateSignals decomposes into updateCache steps
--  (13) updateCacheFromFrame-no-match/match: decomposition into updateSignals
--  (16) processFrameDirect-state: state = handleDataFrame state (FFI link)
--  (17) processFrameDirect-response: response = formatJSON ∘ formatResponse (FFI link)
--  (18) processFrameDirect-ack-sound-json: Ack JSON ��� no violation (end-to-end)
--  (19) handleExtractAllSignals-preserves-state: extract doesn't change state
--  (20) handleBuildFrameByIndex-preserves-state: build doesn't change state
--  (21) handleUpdateFrameByIndex-preserves-state: update doesn't change state
--  (22) handleFormatDBC-preserves-state: formatDBC doesn't change state
module Aletheia.Protocol.FrameProcessor.Properties where

open import Aletheia.Protocol.StreamState
    using (StreamState; StreamPhase; WaitingForDBC; ReadyToStream; Streaming;
           handleDataFrame; PropertyState; mkPropertyState;
           collectAtoms; indexFormula)
open import Aletheia.Protocol.StreamState.Internals
    using (classifyStepResult; stepProperty; dispatchIterResult;
           mkPredTable; updateCacheFromFrame; updateSignals;
           collectAtomsAcc; indexHelper; lookupAtom)
open import Aletheia.Protocol.Message using (Response; Ack; Error; PropertyResponse)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.ResponseFormat.Properties using (formatResponse-ack-unique)
open import Aletheia.Protocol.JSON using (JSON; formatJSON)
open import Aletheia.Main using (processFrameDirect)
open import Aletheia.Protocol.Handlers
    using (handleExtractAllSignals; handleBuildFrameByIndex;
           handleUpdateFrameByIndex; handleFormatDBC)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate; iterate-correct; specHalt)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually;
    Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate
    using (SignalCache; mkSignalCache; CacheEntries; SignalPredicate; evalPredicateTV;
           CachedSignal; mkCachedSignal; lookupCache; updateCache;
           lookupEntries; updateEntries; extractTruthValue)
open import Aletheia.DBC.Types using (DBC; DBCSignal; DBCMessage)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcToBytes)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex; updateFrameByIndex)
open import Data.Vec using (Vec)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

-- ============================================================================
-- PROPERTY 1: State machine guards
-- ============================================================================

-- When not in Streaming phase, handleDataFrame returns the state unchanged.
-- This is a direct case split — handleDataFrame pattern-matches on phase first.

handleDataFrame-guard-waitingForDBC : ∀ (state : StreamState) (tf : TimedFrame)
    → StreamState.phase state ≡ WaitingForDBC
    → proj₁ (handleDataFrame state tf) ≡ state
handleDataFrame-guard-waitingForDBC state tf refl = refl

handleDataFrame-guard-readyToStream : ∀ (state : StreamState) (tf : TimedFrame)
    → StreamState.phase state ≡ ReadyToStream
    → proj₁ (handleDataFrame state tf) ≡ state
handleDataFrame-guard-readyToStream state tf refl = refl

-- ============================================================================
-- PROPERTY 2: Byte modulus identity (boundary justification)
-- ============================================================================

-- When n < 256, n % 256 ≡ n.
-- This justifies the Haskell shim's bytesToAgdaVec skipping % 256:
-- Agda's listToVec applies (x % 256), but the Haskell shim constructs
-- Vec entries directly from Word8 values (which are already in [0,255]).
-- Since Word8 ∈ [0,255] implies n < 256, the modulo is a no-op.
mod-identity-byte : ∀ (n : ℕ) → n < 256 → n % 256 ≡ n
mod-identity-byte n n<256 = m<n⇒m%n≡m n<256

-- ============================================================================
-- PROPERTY 3: classifyStepResult faithfully reflects StepResult constructors
-- ============================================================================

-- Violated → halt (property index + counterexample)
classifyStepResult-violated : ∀ ce prop
  → classifyStepResult (Violated ce) prop ≡ halt (PropertyState.index prop , ce)
classifyStepResult-violated ce prop = refl

-- Continue → advance (simplified successor state)
classifyStepResult-continue : ∀ n newProc prop
  → classifyStepResult (Continue n newProc) prop
    ≡ advance (mkPropertyState (PropertyState.index prop)
                                (PropertyState.formula prop)
                                (PropertyState.atoms prop)
                                (simplify newProc))
classifyStepResult-continue n newProc prop = refl

-- Satisfied → advance (property state unchanged)
classifyStepResult-satisfied : ∀ prop
  → classifyStepResult Satisfied prop ≡ advance prop
classifyStepResult-satisfied prop = refl

-- ============================================================================
-- PROPERTY 4: stepProperty — halt iff stepL returns Violated
-- ============================================================================

-- Forward: If stepL returns Violated, stepProperty halts with matching evidence.
stepProperty-violated : ∀ dbc cache tf prop ce
  → stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf ≡ Violated ce
  → stepProperty dbc cache tf prop ≡ halt (PropertyState.index prop , ce)
stepProperty-violated dbc cache tf prop ce steq rewrite steq = refl

-- Backward: If stepProperty halts, stepL returned Violated.
-- Returns: proof that idx matches the property index, and the stepL equality.
stepProperty-halt-implies-violated : ∀ dbc cache tf prop idx ce
  → stepProperty dbc cache tf prop ≡ halt (idx , ce)
  → idx ≡ PropertyState.index prop
    × stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf ≡ Violated ce
stepProperty-halt-implies-violated dbc cache tf prop idx ce eq
  with stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf | eq
... | Continue _ _  | ()
... | Violated .ce  | refl = refl , refl
... | Satisfied     | ()

-- ============================================================================
-- PROPERTY 5: dispatchIterResult response characterization
-- ============================================================================

-- When iterate finds no violation (nothing), response is Ack.
dispatchIterResult-ack : ∀ dbc ps tf cache
  → proj₂ (dispatchIterResult dbc (ps , nothing) tf cache) ≡ Response.Ack
dispatchIterResult-ack dbc ps tf cache = refl

-- When iterate finds a violation (just), response is PropertyResponse.
dispatchIterResult-violation : ∀ dbc ps idx ce tf cache
  → proj₂ (dispatchIterResult dbc (ps , just (idx , ce)) tf cache)
    ≡ Response.PropertyResponse
        (PR.PropertyResult.Violation idx
          (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                (Counterexample.reason ce)))
dispatchIterResult-violation dbc ps idx ce tf cache = refl

-- ============================================================================
-- PROPERTY 6: handleDataFrame Streaming decomposition
-- ============================================================================

-- In Streaming phase with loaded DBC, handleDataFrame decomposes into:
--   dispatchIterResult ∘ iterate ∘ stepProperty
-- This is the bridge between handleDataFrame and the factored helpers.
handleDataFrame-streaming : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → handleDataFrame state tf
    ≡ let cache = StreamState.signalCache state
          updatedCache = updateCacheFromFrame dbc cache
                           (TimedFrame.timestamp tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) (StreamState.properties state))
           tf updatedCache
handleDataFrame-streaming state tf dbc phase-eq dbc-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl = refl

-- ============================================================================
-- PROPERTY 7: Ack soundness — Ack means no property violated
-- ============================================================================

-- If handleDataFrame returns Ack, then iterate found no halt evidence.
-- Combined with iterate-correct and specHalt, this means:
-- no property's stepL returned Violated.
handleDataFrame-ack-sound : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → proj₂ (handleDataFrame state tf) ≡ Response.Ack
  → proj₂ (iterate (stepProperty dbc (StreamState.signalCache state) tf)
                    (StreamState.properties state)) ≡ nothing
handleDataFrame-ack-sound state tf dbc phase-eq dbc-eq resp-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  with iterate (stepProperty dbc (StreamState.signalCache state) tf)
               (StreamState.properties state) | resp-eq
... | (ps , nothing)         | _ = refl
... | (ps , just (idx , ce)) | ()

-- ============================================================================
-- PROPERTY 8: Violation soundness — PropertyResponse means some property violated
-- ============================================================================

-- If handleDataFrame returns PropertyResponse, then iterate found halt evidence:
-- some property's stepProperty halted (which, by stepProperty-halt-implies-violated,
-- means some stepL returned Violated).
handleDataFrame-violation-sound : ∀ state tf dbc pr
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → proj₂ (handleDataFrame state tf) ≡ Response.PropertyResponse pr
  → ∃[ e ] proj₂ (iterate (stepProperty dbc (StreamState.signalCache state) tf)
                           (StreamState.properties state)) ≡ just e
handleDataFrame-violation-sound state tf dbc pr phase-eq dbc-eq resp-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  with iterate (stepProperty dbc (StreamState.signalCache state) tf)
               (StreamState.properties state) | resp-eq
... | (ps , nothing)    | ()
... | (ps , just e)     | _ = e , refl

-- ============================================================================
-- PROPERTY 9: mkPredTable faithfulness (atom indexing consistency)
-- ============================================================================
--
-- Proves that indexHelper and collectAtomsAcc assign indices and collect
-- atoms in the same left-to-right order, so mkPredTable evaluates
-- the correct signal predicate for each atom index.

-- Forward specification: atoms in left-to-right order (no accumulator).
flattenAtoms : LTL SignalPredicate → List SignalPredicate
flattenAtoms (Atomic a)               = a ∷ []
flattenAtoms (Not φ)                  = flattenAtoms φ
flattenAtoms (And φ ψ)               = flattenAtoms φ ++ flattenAtoms ψ
flattenAtoms (Or φ ψ)                = flattenAtoms φ ++ flattenAtoms ψ
flattenAtoms (Next φ)                 = flattenAtoms φ
flattenAtoms (Always φ)               = flattenAtoms φ
flattenAtoms (Eventually φ)           = flattenAtoms φ
flattenAtoms (Until φ ψ)             = flattenAtoms φ ++ flattenAtoms ψ
flattenAtoms (Release φ ψ)           = flattenAtoms φ ++ flattenAtoms ψ
flattenAtoms (MetricEventually _ _ φ) = flattenAtoms φ
flattenAtoms (MetricAlways _ _ φ)     = flattenAtoms φ
flattenAtoms (MetricUntil _ _ φ ψ)   = flattenAtoms φ ++ flattenAtoms ψ
flattenAtoms (MetricRelease _ _ φ ψ) = flattenAtoms φ ++ flattenAtoms ψ

-- List lookup over concatenation: left part.
lookupAtom-++-left : ∀ (xs ys : List SignalPredicate) k
  → k < length xs → lookupAtom (xs ++ ys) k ≡ lookupAtom xs k
lookupAtom-++-left []       ys k       ()
lookupAtom-++-left (x ∷ xs) ys zero    _         = refl
lookupAtom-++-left (x ∷ xs) ys (suc k) (s≤s k<n) = lookupAtom-++-left xs ys k k<n

-- List lookup over concatenation: right part.
lookupAtom-++-right : ∀ (xs ys : List SignalPredicate) k
  → lookupAtom (xs ++ ys) (length xs + k) ≡ lookupAtom ys k
lookupAtom-++-right []       ys k = refl
lookupAtom-++-right (x ∷ xs) ys k = lookupAtom-++-right xs ys k

private
  -- Arithmetic: b + (a + n) ≡ (a + b) + n
  +-swap-sum : ∀ a b n → b + (a + n) ≡ (a + b) + n
  +-swap-sum a b n = trans (sym (+-assoc b a n)) (cong (_+ n) (+-comm b a))

  -- Arithmetic: (a + k) + n ≡ k + (a + n)
  ψ-index-eq : ∀ a k n → (a + k) + n ≡ k + (a + n)
  ψ-index-eq a k n = trans (cong (_+ n) (+-comm a k)) (+-assoc k a n)

  -- Extend k < |xs| to k < |xs ++ ys|
  extend-< : ∀ {k} (xs ys : List SignalPredicate)
    → k < length xs → k < length (xs ++ ys)
  extend-<         []       ys ()
  extend-< {zero}  (x ∷ xs) ys _         = s≤s z≤n
  extend-< {suc k} (x ∷ xs) ys (s≤s k<) = s≤s (extend-< xs ys k<)

  -- Shift k < |ys| to |xs| + k < |xs ++ ys|
  shift-< : ∀ (xs ys : List SignalPredicate) {k}
    → k < length ys → length xs + k < length (xs ++ ys)
  shift-< []       ys k< = k<
  shift-< (x ∷ xs) ys k< = s≤s (shift-< xs ys k<)

-- Counter increment equals atom count.
indexHelper-counter : ∀ (φ : LTL SignalPredicate) n
  → proj₂ (indexHelper φ n) ≡ length (flattenAtoms φ) + n
indexHelper-counter (Atomic _) n            = refl
indexHelper-counter (Not φ) n               = indexHelper-counter φ n
indexHelper-counter (And φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Or φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Next φ) n              = indexHelper-counter φ n
indexHelper-counter (Always φ) n            = indexHelper-counter φ n
indexHelper-counter (Eventually φ) n        = indexHelper-counter φ n
indexHelper-counter (Until φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (Release φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (MetricEventually _ _ φ) n = indexHelper-counter φ n
indexHelper-counter (MetricAlways _ _ φ) n     = indexHelper-counter φ n
indexHelper-counter (MetricUntil _ _ φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n
indexHelper-counter (MetricRelease _ _ φ ψ) n
  rewrite indexHelper-counter φ n
  | indexHelper-counter ψ (length (flattenAtoms φ) + n)
  | length-++ (flattenAtoms φ) {flattenAtoms ψ}
  = +-swap-sum (length (flattenAtoms φ)) (length (flattenAtoms ψ)) n

-- Per-index correctness: each atom index maps to the right predicate.
-- Faithful atoms φ n holds when every Atomic k assigned by indexHelper φ n
-- satisfies lookupAtom atoms k ≡ just pred.
Faithful : List SignalPredicate → LTL SignalPredicate → ℕ → Set
Faithful atoms (Atomic a) n               = lookupAtom atoms n ≡ just a
Faithful atoms (Not φ) n                  = Faithful atoms φ n
Faithful atoms (And φ ψ) n               = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Or φ ψ) n                = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Next φ) n                 = Faithful atoms φ n
Faithful atoms (Always φ) n               = Faithful atoms φ n
Faithful atoms (Eventually φ) n           = Faithful atoms φ n
Faithful atoms (Until φ ψ) n             = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (Release φ ψ) n           = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (MetricEventually _ _ φ) n = Faithful atoms φ n
Faithful atoms (MetricAlways _ _ φ) n     = Faithful atoms φ n
Faithful atoms (MetricUntil _ _ φ ψ) n   = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))
Faithful atoms (MetricRelease _ _ φ ψ) n = Faithful atoms φ n × Faithful atoms ψ (proj₂ (indexHelper φ n))

-- Hypothesis constructors for binary formula cases.
private
  mk-φ-hyp : ∀ {n} ga (φ ψ : LTL SignalPredicate) →
    (∀ k → k < length (flattenAtoms φ ++ flattenAtoms ψ) →
       lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ ++ flattenAtoms ψ) k) →
    ∀ k → k < length (flattenAtoms φ) → lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ) k
  mk-φ-hyp ga φ ψ hyp k k< =
    trans (hyp k (extend-< (flattenAtoms φ) (flattenAtoms ψ) k<))
          (lookupAtom-++-left (flattenAtoms φ) (flattenAtoms ψ) k k<)

  mk-ψ-hyp : ∀ ga (φ ψ : LTL SignalPredicate) n →
    (∀ k → k < length (flattenAtoms φ ++ flattenAtoms ψ) →
       lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ ++ flattenAtoms ψ) k) →
    ∀ k → k < length (flattenAtoms ψ) →
    lookupAtom ga (k + proj₂ (indexHelper φ n)) ≡ lookupAtom (flattenAtoms ψ) k
  mk-ψ-hyp ga φ ψ n hyp k k<
    rewrite indexHelper-counter φ n
    | sym (ψ-index-eq (length (flattenAtoms φ)) k n)
    = trans (hyp (length (flattenAtoms φ) + k) (shift-< (flattenAtoms φ) (flattenAtoms ψ) k<))
            (lookupAtom-++-right (flattenAtoms φ) (flattenAtoms ψ) k)

-- Generalized faithfulness: if the atom list matches flattenAtoms at offset n,
-- then every atom index in the indexed formula looks up correctly.
faithful-gen : ∀ ga (φ : LTL SignalPredicate) n →
  (∀ k → k < length (flattenAtoms φ) → lookupAtom ga (k + n) ≡ lookupAtom (flattenAtoms φ) k) →
  Faithful ga φ n
faithful-gen ga (Atomic _) n hyp             = hyp 0 (s≤s z≤n)
faithful-gen ga (Not φ) n hyp                = faithful-gen ga φ n hyp
faithful-gen ga (And φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Or φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Next φ) n hyp               = faithful-gen ga φ n hyp
faithful-gen ga (Always φ) n hyp             = faithful-gen ga φ n hyp
faithful-gen ga (Eventually φ) n hyp         = faithful-gen ga φ n hyp
faithful-gen ga (Until φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (Release φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (MetricEventually _ _ φ) n hyp = faithful-gen ga φ n hyp
faithful-gen ga (MetricAlways _ _ φ) n hyp     = faithful-gen ga φ n hyp
faithful-gen ga (MetricUntil _ _ φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)
faithful-gen ga (MetricRelease _ _ φ ψ) n hyp =
  faithful-gen ga φ n (mk-φ-hyp ga φ ψ hyp) ,
  faithful-gen ga ψ _ (mk-ψ-hyp ga φ ψ n hyp)

-- collectAtomsAcc matches the flattenAtoms specification.
collectAtomsAcc-spec : ∀ φ acc → collectAtomsAcc φ acc ≡ flattenAtoms φ ++ acc
collectAtomsAcc-spec (Atomic _) acc           = refl
collectAtomsAcc-spec (Not φ) acc              = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (And φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Or φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Next φ) acc             = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Always φ) acc           = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Eventually φ) acc       = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (Until φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (Release φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (MetricEventually _ _ φ) acc = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (MetricAlways _ _ φ) acc     = collectAtomsAcc-spec φ acc
collectAtomsAcc-spec (MetricUntil _ _ φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)
collectAtomsAcc-spec (MetricRelease _ _ φ ψ) acc
  rewrite collectAtomsAcc-spec ψ acc
  | collectAtomsAcc-spec φ (flattenAtoms ψ ++ acc)
  = sym (++-assoc (flattenAtoms φ) (flattenAtoms ψ) acc)

-- collectAtoms is exactly flattenAtoms.
collectAtoms-is-flattenAtoms : ∀ φ → collectAtoms φ ≡ flattenAtoms φ
collectAtoms-is-flattenAtoms φ =
  trans (collectAtomsAcc-spec φ []) (++-identityʳ (flattenAtoms φ))

-- Main theorem: atom indices in indexFormula look up correctly in collectAtoms.
collectAtoms-faithful : ∀ φ → Faithful (collectAtoms φ) φ 0
collectAtoms-faithful φ rewrite collectAtoms-is-flattenAtoms φ =
  faithful-gen (flattenAtoms φ) φ 0
    (λ k _ → cong (lookupAtom (flattenAtoms φ)) (+-identityʳ k))

-- mkPredTable evaluates the predicate found by lookupAtom.
mkPredTable-lookup : ∀ dbc cache atoms k pred frame →
  lookupAtom atoms k ≡ just pred →
  mkPredTable dbc cache atoms k frame ≡ evalPredicateTV dbc cache pred (TimedFrame.frame frame)
mkPredTable-lookup dbc cache atoms k pred frame eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 10: Signal cache update — same name lookup
-- ============================================================================

private
  -- Helper: looking up name in (name , v) ∷ rest returns just v.
  -- Uses Dec-based `with` so ⌊ name ≟ₛ name ⌋ reduces inside lookupEntries.
  lookupEntries-head : ∀ name v rest →
    lookupEntries name ((name , v) ∷ rest) ≡ just v
  lookupEntries-head name v rest with name ≟ₛ name
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  -- Helper: looking up name' ≢ name skips the head entry.
  lookupEntries-skip : ∀ name' name v rest →
    name' ≢ name →
    lookupEntries name' ((name , v) ∷ rest) ≡ lookupEntries name' rest
  lookupEntries-skip name' name v rest neq with name' ≟ₛ name
  ... | yes p = ⊥-elim (neq p)
  ... | no  _ = refl

  -- List-level: after updateEntries, looking up the updated name returns the new value.
  lookupEntries-updateEntries-hit : ∀ name val ts (es : CacheEntries) →
    lookupEntries name (updateEntries name val ts es) ≡ just (mkCachedSignal val ts)
  lookupEntries-updateEntries-hit name val ts [] =
    lookupEntries-head name (mkCachedSignal val ts) []
  lookupEntries-updateEntries-hit name val ts ((n , cached) ∷ rest)
    with name ≟ₛ n
  ... | yes _ = lookupEntries-head name (mkCachedSignal val ts) rest
  ... | no ¬a = trans (lookupEntries-skip name n cached (updateEntries name val ts rest) ¬a)
                      (lookupEntries-updateEntries-hit name val ts rest)

  -- List-level: after updateEntries, looking up a different name is unchanged.
  lookupEntries-updateEntries-miss : ∀ name name' val ts (es : CacheEntries) →
    name ≢ name' →
    lookupEntries name' (updateEntries name val ts es) ≡ lookupEntries name' es
  lookupEntries-updateEntries-miss name name' val ts [] name≢name' =
    lookupEntries-skip name' name (mkCachedSignal val ts) [] (λ p → name≢name' (sym p))
  lookupEntries-updateEntries-miss name name' val ts ((n , cached) ∷ rest) name≢name'
    with name ≟ₛ n | name' ≟ₛ n
  ... | yes p | yes q = ⊥-elim (name≢name' (trans p (sym q)))
  ... | yes _ | no  _ =
    lookupEntries-skip name' name (mkCachedSignal val ts) rest (λ p → name≢name' (sym p))
  ... | no  _ | yes refl =
    lookupEntries-head name' cached (updateEntries name val ts rest)
  ... | no  _ | no ¬b =
    trans (lookupEntries-skip name' n cached (updateEntries name val ts rest) ¬b)
          (lookupEntries-updateEntries-miss name name' val ts rest name≢name')

-- After updateCache, looking up the updated name returns the new value.
-- Delegates to list-level proof via record decomposition.
lookupCache-updateCache-hit : ∀ name val ts cache →
  lookupCache name (updateCache name val ts cache) ≡ just (mkCachedSignal val ts)
lookupCache-updateCache-hit name val ts (mkSignalCache es _) =
  lookupEntries-updateEntries-hit name val ts es

-- ============================================================================
-- PROPERTY 11: Signal cache update — different name lookup unchanged
-- ============================================================================

-- After updateCache, looking up a different name returns the original value.
-- Combined with Property 10, this proves updateCache is a correct map-update.
lookupCache-updateCache-miss : ∀ name name' val ts cache →
  name ≢ name' →
  lookupCache name' (updateCache name val ts cache) ≡ lookupCache name' cache
lookupCache-updateCache-miss name name' val ts (mkSignalCache es _) name≢name' =
  lookupEntries-updateEntries-miss name name' val ts es name≢name'

-- ============================================================================
-- PROPERTY 12: updateSignals step decomposition
-- ============================================================================

-- When extraction succeeds, updateSignals steps to updateCache + recurse.
updateSignals-step-hit : ∀ {n} dbc (frame : CANFrame n) ts sig sigs cache v →
  extractTruthValue (DBCSignal.name sig) dbc frame ≡ just v →
  updateSignals dbc frame ts (sig ∷ sigs) cache
    ≡ updateSignals dbc frame ts sigs (updateCache (DBCSignal.name sig) v ts cache)
updateSignals-step-hit dbc frame ts sig sigs cache v eq rewrite eq = refl

-- When extraction fails, updateSignals skips the signal.
updateSignals-step-miss : ∀ {n} dbc (frame : CANFrame n) ts sig sigs cache →
  extractTruthValue (DBCSignal.name sig) dbc frame ≡ nothing →
  updateSignals dbc frame ts (sig ∷ sigs) cache
    ≡ updateSignals dbc frame ts sigs cache
updateSignals-step-miss dbc frame ts sig sigs cache eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 13: updateCacheFromFrame decomposition
-- ============================================================================

-- When no message matches the frame, cache is unchanged.
updateCacheFromFrame-no-match : ∀ {n} dbc cache ts (frame : CANFrame n) →
  findMessageById (CANFrame.id frame) dbc ≡ nothing →
  updateCacheFromFrame dbc cache ts frame ≡ cache
updateCacheFromFrame-no-match dbc cache ts frame eq rewrite eq = refl

-- When a message matches, updateCacheFromFrame delegates to updateSignals.
updateCacheFromFrame-match : ∀ {n} dbc cache ts (frame : CANFrame n) msg →
  findMessageById (CANFrame.id frame) dbc ≡ just msg →
  updateCacheFromFrame dbc cache ts frame
    ≡ updateSignals dbc frame ts (DBCMessage.signals msg) cache
updateCacheFromFrame-match dbc cache ts frame msg eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 14: Ack completeness — no violation ⇒ Ack
-- ============================================================================

-- If no property's stepProperty halts, handleDataFrame returns Ack.
-- Combined with Property 7 (ack soundness), this gives: Ack iff no violation.
handleDataFrame-ack-complete : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → specHalt (stepProperty dbc (StreamState.signalCache state) tf)
             (StreamState.properties state) ≡ nothing
  → proj₂ (handleDataFrame state tf) ≡ Response.Ack
handleDataFrame-ack-complete state tf dbc phase-eq dbc-eq spec-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  rewrite iterate-correct (stepProperty dbc (StreamState.signalCache state) tf)
                          (StreamState.properties state)
  rewrite spec-eq
  = refl

-- ============================================================================
-- PROPERTY 15: Violation completeness — some violation ⇒ PropertyResponse
-- ============================================================================

-- If some property's stepProperty halts, handleDataFrame returns PropertyResponse.
-- Combined with Property 8 (violation soundness), this gives: PropertyResponse iff some violation.
handleDataFrame-violation-complete : ∀ state tf dbc idx ce
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → specHalt (stepProperty dbc (StreamState.signalCache state) tf)
             (StreamState.properties state) ≡ just (idx , ce)
  → proj₂ (handleDataFrame state tf)
    ≡ Response.PropertyResponse
        (PR.PropertyResult.Violation idx
          (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                (Counterexample.reason ce)))
handleDataFrame-violation-complete state tf dbc idx ce phase-eq dbc-eq spec-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  rewrite iterate-correct (stepProperty dbc (StreamState.signalCache state) tf)
                          (StreamState.properties state)
  rewrite spec-eq
  = refl

-- ============================================================================
-- PROPERTY 16-17: processFrameDirect decomposition
-- ============================================================================

-- processFrameDirect = handleDataFrame + formatJSON ∘ formatResponse.
-- State component passes through unchanged.
processFrameDirect-state : ∀ state tf
  → proj₁ (processFrameDirect state tf) ≡ proj₁ (handleDataFrame state tf)
processFrameDirect-state state tf with handleDataFrame state tf
... | (_ , _) = refl

-- Response component is formatJSON ∘ formatResponse of handleDataFrame's response.
processFrameDirect-response : ∀ state tf
  → proj₂ (processFrameDirect state tf)
    ≡ formatJSON (formatResponse (proj₂ (handleDataFrame state tf)))
processFrameDirect-response state tf with handleDataFrame state tf
... | (_ , _) = refl

-- ============================================================================
-- PROPERTY 18: End-to-end Ack soundness at JSON level
-- ============================================================================

-- If formatResponse maps the handler response to the Ack JSON tree,
-- no property was violated. Composes formatResponse-ack-unique (injectivity)
-- with handleDataFrame-ack-sound.
processFrameDirect-ack-sound-json : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → formatResponse (proj₂ (handleDataFrame state tf)) ≡ formatResponse Ack
  → proj₂ (iterate (stepProperty dbc (StreamState.signalCache state) tf)
                    (StreamState.properties state)) ≡ nothing
processFrameDirect-ack-sound-json state tf dbc phase-eq dbc-eq fmt-eq =
  handleDataFrame-ack-sound state tf dbc phase-eq dbc-eq
    (formatResponse-ack-unique (proj₂ (handleDataFrame state tf)) fmt-eq)

-- ============================================================================
-- PROPERTIES 19-22: Read-only handler state preservation
-- ============================================================================

-- Extract, build, update, formatDBC handlers never modify StreamState.
-- Each proof case-splits on StreamState.dbc (withDBC pattern) and, for
-- build/update, on the Either result.

handleExtractAllSignals-preserves-state : ∀ canId dlc bytes state
  → proj₁ (handleExtractAllSignals canId dlc bytes state) ≡ state
handleExtractAllSignals-preserves-state canId dlc bytes state
  with StreamState.dbc state
... | nothing = refl
... | just _  = refl

handleBuildFrameByIndex-preserves-state : ∀ canId dlc signalPairs state
  → proj₁ (handleBuildFrameByIndex canId dlc signalPairs state) ≡ state
handleBuildFrameByIndex-preserves-state canId dlc signalPairs state
  with StreamState.dbc state
... | nothing = refl
... | just dbc with buildFrameByIndex dbc canId (DLC.code dlc) signalPairs
...   | inj₁ _ = refl
...   | inj₂ _ = refl

handleUpdateFrameByIndex-preserves-state : ∀ canId dlc bytes signalPairs state
  → proj₁ (handleUpdateFrameByIndex canId dlc bytes signalPairs state) ≡ state
handleUpdateFrameByIndex-preserves-state canId dlc bytes signalPairs state
  with StreamState.dbc state
... | nothing = refl
... | just _  = refl

handleFormatDBC-preserves-state : ∀ state
  → proj₁ (handleFormatDBC state) ≡ state
handleFormatDBC-preserves-state state
  with StreamState.dbc state
... | nothing = refl
... | just _  = refl
