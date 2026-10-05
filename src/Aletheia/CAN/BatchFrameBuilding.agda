-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Batch frame building from signal index-value pairs.
--
-- Purpose: Build CAN frames from multiple signal values at once with validation.
-- Operations: buildFrameByIndex (ValidDBC + CAN ID + DLC + index-keyed signals → FrameError ⊎ payload),
--             updateFrameByIndex (ValidDBC + CAN ID + frame + index-keyed signals → FrameError ⊎ frame).
-- Role: Batch encoding for the binary FFI path; all language bindings resolve
-- signal names to indices client-side before calling the `*ByIndex` entry points.
--
-- Refusals: a CAN ID the DBC lacks or the updated frame does not carry, a
-- signal index out of range, a signal past the frame's end, two requested
-- signals sharing a bit, and each value its signal cannot carry (outside the
-- declared range, or scaled to by no integer raw value).  An accepted value is
-- written from the proof that it fits its signal's bits.
module Aletheia.CAN.BatchFrameBuilding where

open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.Encoding using (withInjected)
open import Aletheia.CAN.Encoding.Value using (checkValue; encodedBits; Encodable; EncodeRefusal; OutOfRange; NotRepresentable)
open import Aletheia.CAN.Encoding.Value.Facts using (SignalFacts)
open import Aletheia.DBC.Validity using (ValidDBC; signalFacts)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.CAN.Endianness using (replicate-below256)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Aletheia.DBC.Decidable using (signalPhysicalBits; Intersects; bitsIntersect₀)
open import Aletheia.DBC.Decidable.SignalGeometry using (signalFitsFrame₀)
open import Aletheia.CAN.Signal using (SignalDef)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary.Reflects using (ofⁿ)

open import Aletheia.Data.Dec0 using (Dec₀; dec₀; or₀; map₀; does₀)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec as Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.Prelude using (Found; indexIn; _>>=ₑ_)
open import Aletheia.Error using
  ( FrameError; SignalIndexOOB; ValueOutOfRange; ValueNotRepresentable
  ; SignalsOverlap; CANIdNotFound; CANIdMismatch; SignalPastFrameEnd
  )

-- ============================================================================
-- OVERLAP DETECTION (endianness-aware, precomputation-hoisted)
-- ============================================================================
--
-- Uses the certified `bitsIntersect₀` fast path from
-- `DBC.Decidable.Disjointness`; each fold below carries its own erased
-- Any-membership certificate, and the equivalence with `PhysicallyDisjoint`
-- is proved by `physicallyOverlapᵇ-sound` / `physicallyOverlapᵇ-complete`
-- in `DBC.Properties`, so this check is as trustworthy as the `Dec`-valued
-- `physicallyDisjoint?`.
--
-- Performance note: per-signal physical bit positions are precomputed ONCE
-- in `hasOverlaps`, outside the O(m²) pair loop. This turns the per-frame
-- cost from O(m² × l²) (with Dec-boxed per-bit comparisons, as in the
-- `physicallyDisjoint?` path) into O(m × l) precomputation plus
-- O(m² × l²) cheap Bool operations on precomputed lists.

-- The proposition the pair loop decides: some list in the collection
-- intersects a LATER list (mirrors the suffix recursion below).
data HasPairOverlap : List (List ℕ) → Set where
  po-here  : ∀ {bs rest} → Any (Intersects bs) rest → HasPairOverlap (bs ∷ rest)
  po-there : ∀ {bs rest} → HasPairOverlap rest      → HasPairOverlap (bs ∷ rest)

-- Self-certifying twins: `does₀` is the same `_∨_` fold over
-- `bitsIntersectᵇ` as the Bool checks below; the erased certificates pin the
-- folds to Any-membership / HasPairOverlap.  MAlonzo erases the certificates
-- (Dec₀ is a newtype over Bool), so the runtime cost is the bare fold.
anyOverlap₀ : (target : List ℕ) (rest : List (List ℕ)) → Dec₀ (Any (Intersects target) rest)
anyOverlap₀ target [] = dec₀ false (ofⁿ λ ())
anyOverlap₀ target (bs ∷ rest) =
  map₀ join split (or₀ (bitsIntersect₀ target bs) (anyOverlap₀ target rest))
  where
    @0 join : Intersects target bs ⊎ Any (Intersects target) rest
            → Any (Intersects target) (bs ∷ rest)
    join (inj₁ i) = here i
    join (inj₂ a) = there a

    @0 split : Any (Intersects target) (bs ∷ rest)
             → Intersects target bs ⊎ Any (Intersects target) rest
    split (here i)  = inj₁ i
    split (there a) = inj₂ a

anyPairOverlap₀ : (bss : List (List ℕ)) → Dec₀ (HasPairOverlap bss)
anyPairOverlap₀ [] = dec₀ false (ofⁿ λ ())
anyPairOverlap₀ (bs ∷ rest) =
  map₀ join split (or₀ (anyOverlap₀ bs rest) (anyPairOverlap₀ rest))
  where
    @0 join : Any (Intersects bs) rest ⊎ HasPairOverlap rest → HasPairOverlap (bs ∷ rest)
    join (inj₁ a) = po-here a
    join (inj₂ h) = po-there h

    @0 split : HasPairOverlap (bs ∷ rest) → Any (Intersects bs) rest ⊎ HasPairOverlap rest
    split (po-here a)  = inj₁ a
    split (po-there h) = inj₂ h

hasOverlaps₀ : (n : ℕ) (sigs : List DBCSignal) → Dec₀ (HasPairOverlap (map (signalPhysicalBits n) sigs))
hasOverlaps₀ n sigs = anyPairOverlap₀ (map (signalPhysicalBits n) sigs)

-- Bool checks: definitional projections of the twins above, running the
-- same `_∨_` folds.

-- Check if any precomputed signal bit list overlaps a given target bit list.
anyOverlap : List ℕ → List (List ℕ) → Bool
anyOverlap target rest = does₀ (anyOverlap₀ target rest)

-- Check all pairs of precomputed bit lists for physical overlaps.
anyPairOverlap : List (List ℕ) → Bool
anyPairOverlap bss = does₀ (anyPairOverlap₀ bss)

-- Check all signal pairs for physical overlaps. Precomputes each signal's
-- physical bit list ONCE, then runs the O(m²) pair loop over the cached lists.
-- Returns true if at least one pair of signals occupies the same physical bit.
-- `n` is the frame byte count (8 for CAN 2.0B, up to 64 for CAN-FD).
hasOverlaps : ℕ → List DBCSignal → Bool
hasOverlaps n sigs = does₀ (hasOverlaps₀ n sigs)

-- ============================================================================
-- GENERIC SIGNAL LOOKUP (parameterized by resolution strategy)
-- ============================================================================

-- Import shared DBC lookup utilities
open import Aletheia.CAN.DBCHelpers using (findMessage; canIdEquals)

-- Lookup strategy: how to resolve a key to one of a message's signals (with
-- where it sits), and how to produce errors.  Single instance:
-- `indexStrategy : LookupStrategy ℕ`, every binding resolving signal names
-- to indices client-side.  The abstraction keeps the per-key shape (resolve
-- + error) at a single source of truth for the build and update pipelines.
record LookupStrategy (K : Set) : Set where
  field
    resolve : K → (msg : DBCMessage) → Maybe (Found (DBCMessage.signals msg))
    notFoundError : K → FrameError

-- Index-based strategy (binary FFI path — no string allocation)
indexStrategy : LookupStrategy ℕ
indexStrategy = record
  { resolve       = λ idx msg → indexIn idx (DBCMessage.signals msg)
  ; notFoundError = SignalIndexOOB
  }

-- A message's signal, as found, paired with the value requested for it.
Request : DBCMessage → Set
Request msg = Found (DBCMessage.signals msg) × ℚ

requestedSignal : ∀ {msg} → Request msg → DBCSignal
requestedSignal (sig , _) = Found.item sig

-- Generic signal lookup: resolve each key to one of the message's signals.
lookupSignalsG : ∀ {K} → LookupStrategy K → List (K × ℚ) → (msg : DBCMessage) → FrameError ⊎ List (Request msg)
lookupSignalsG _     []                   _   = inj₂ []
lookupSignalsG strat ((key , value) ∷ rest) msg with LookupStrategy.resolve strat key msg
... | nothing = inj₁ (LookupStrategy.notFoundError strat key)
... | just sig = lookupSignalsG strat rest msg >>=ₑ λ restSigs → inj₂ ((sig , value) ∷ restSigs)

-- ============================================================================
-- FRAME BUILDING
-- ============================================================================

-- Inject one signal: check the value (encoding layer), build its bits from
-- the facts the DBC's validity states of the signal (encoding layer), write
-- them into the frame (frame layer).  The value checks are the only refusals.
injectOne : ∀ {n} (vdbc : ValidDBC) → (msg : Found (DBC.messages (ValidDBC.dbc vdbc)))
          → CANFrame n → Request (Found.item msg) → FrameError ⊎ CANFrame n
injectOne {n} vdbc msg frame (sig , value) = settle (checkValue sd (SignalFacts.factor≢0 facts) value)
  where
    signal = Found.item sig
    sd     = DBCSignal.signalDef signal

    @0 facts : SignalFacts sd
    facts = signalFacts (ValidDBC.isValid vdbc) (Found.position msg) (Found.position sig)

    settle : EncodeRefusal ⊎ Encodable sd value → FrameError ⊎ CANFrame n
    settle (inj₁ OutOfRange) =
      inj₁ (ValueOutOfRange (signalNameStr signal) value
             (toℚ (SignalDef.minimum sd)) (toℚ (SignalDef.maximum sd)))
    settle (inj₁ NotRepresentable) =
      inj₁ (ValueNotRepresentable (signalNameStr signal) value
             (toℚ (SignalDef.factor sd)) (toℚ (SignalDef.offset sd)))
    settle (inj₂ checked) =
      inj₂ (withInjected (SignalDef.startBit sd) (encodedBits checked facts) (DBCSignal.byteOrder signal) frame)

-- The frame's size is the caller's and each signal's placement is the DBC's:
-- the two are compatible only where a signal's last bit lies inside the
-- frame.  The bit writer is total, so a signal running past the end would
-- have its overhanging bits written nowhere and the frame returned as if it
-- carried them; this names the first such signal, on the same geometry
-- proposition the ingest gates decide, here decided without allocating.
firstPastFrameEnd : ℕ → List DBCSignal → Maybe DBCSignal
firstPastFrameEnd _ [] = nothing
firstPastFrameEnd n (sig ∷ rest)
  with does₀ (signalFitsFrame₀ n (SignalDef.startBit (DBCSignal.signalDef sig))
                                 (SignalDef.bitLength (DBCSignal.signalDef sig)))
... | true  = firstPastFrameEnd n rest
... | false = just sig

-- Inject all signals into a frame (left-to-right fold)
injectAll : ∀ {n} (vdbc : ValidDBC) → (msg : Found (DBC.messages (ValidDBC.dbc vdbc)))
          → CANFrame n → List (Request (Found.item msg)) → FrameError ⊎ CANFrame n
injectAll _    _   frame [] = inj₂ frame
injectAll vdbc msg frame (req ∷ rest) =
  injectOne vdbc msg frame req >>=ₑ λ frame' → injectAll vdbc msg frame' rest

-- Shared build pipeline: check every signal fits the frame and none overlap,
-- inject into an empty frame, return the payload.
validateAndBuild : (vdbc : ValidDBC) → (msg : Found (DBC.messages (ValidDBC.dbc vdbc)))
                 → CANId → (dlc : DLC) → List (Request (Found.item msg))
                 → FrameError ⊎ Vec Byte (dlcBytes dlc)
validateAndBuild vdbc msg canId dlc reqs
  with firstPastFrameEnd (dlcBytes dlc) (map (requestedSignal {Found.item msg}) reqs)
... | just sig = inj₁ (SignalPastFrameEnd (signalNameStr sig) (dlcBytes dlc))
... | nothing with hasOverlaps (dlcBytes dlc) (map (requestedSignal {Found.item msg}) reqs)
...   | true = inj₁ SignalsOverlap
...   | false = injectAll vdbc msg emptyFrame reqs >>=ₑ λ finalFrame → inj₂ (CANFrame.payload finalFrame)
  where
    emptyFrame : CANFrame (dlcBytes dlc)
    emptyFrame = record
      { id = canId ; dlc = dlc ; payload = Vec.replicate (dlcBytes dlc) 0
      ; below256 = replicate-below256 (dlcBytes dlc) }

-- ============================================================================
-- GENERIC FRAME BUILDING AND UPDATING
-- ============================================================================

-- Generic build: lookup signals via strategy, validate geometry, inject into an empty frame.
buildFrameG : ∀ {K} → LookupStrategy K → ValidDBC → CANId → (dlc : DLC)
            → List (K × ℚ) → FrameError ⊎ Vec Byte (dlcBytes dlc)
buildFrameG strat vdbc canId dlc signals with findMessage canId (ValidDBC.dbc vdbc)
... | nothing = inj₁ CANIdNotFound
... | just msg = lookupSignalsG strat signals (Found.item msg) >>=ₑ validateAndBuild vdbc msg canId dlc

-- Generic update: verify CAN ID match, lookup signals, check their geometry, inject into the existing frame.
updateFrameG : ∀ {K} → LookupStrategy K → ∀ {n} → ValidDBC → CANId
             → CANFrame n → List (K × ℚ) → FrameError ⊎ CANFrame n
updateFrameG strat {n = n} vdbc canId frame signals =
  if canIdEquals canId (CANFrame.id frame)
  then findAndInject
  else inj₁ CANIdMismatch
  where
    -- The frame being updated carries its own size, and a build's two
    -- geometry rules hold of it: a signal past its end has nowhere to write,
    -- and of two requested signals sharing a bit only the later write would
    -- remain.
    fitOrInject : (msg : Found (DBC.messages (ValidDBC.dbc vdbc))) → List (Request (Found.item msg)) → FrameError ⊎ CANFrame n
    fitOrInject msg reqs with firstPastFrameEnd n (map (requestedSignal {Found.item msg}) reqs)
    ... | just sig = inj₁ (SignalPastFrameEnd (signalNameStr sig) n)
    ... | nothing with hasOverlaps n (map (requestedSignal {Found.item msg}) reqs)
    ...   | true  = inj₁ SignalsOverlap
    ...   | false = injectAll vdbc msg frame reqs

    findAndInject : FrameError ⊎ CANFrame _
    findAndInject with findMessage canId (ValidDBC.dbc vdbc)
    ... | nothing = inj₁ CANIdNotFound
    ... | just msg = lookupSignalsG strat signals (Found.item msg) >>=ₑ fitOrInject msg

-- Index-based API (binary FFI path — no string allocation)
buildFrameByIndex : ValidDBC → CANId → (dlc : DLC) → List (ℕ × ℚ)
                  → FrameError ⊎ Vec Byte (dlcBytes dlc)
buildFrameByIndex = buildFrameG indexStrategy

updateFrameByIndex : ∀ {n} → ValidDBC → CANId → CANFrame n → List (ℕ × ℚ)
                   → FrameError ⊎ CANFrame n
updateFrameByIndex = updateFrameG indexStrategy
