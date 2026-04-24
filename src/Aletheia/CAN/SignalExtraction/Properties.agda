{-# OPTIONS --safe --without-K #-}

-- Multiplexing correctness properties for signal extraction.
--
-- Purpose: Prove correctness of the multiplexor presence check used in
-- extractSignalDirect and extractSignalWithContext, including support
-- for nested multiplexing chains.
-- Properties:
--   checkPresenceP-finds-mux        : When-presence check passes → mux signal exists
--   checkPresenceP-rejects-missing  : mux signal absent → When-presence check fails
--   checkSignalPresence-sound       : presence check passes → Always or some When held
--   extractSignalDirect-mux         : presence check fails → extraction returns SignalNotPresent
--   walkMux-blocks-cycle-branch     : static walkMux ≡ true → runtime checkPresenceP
--                                     never reaches its fuel-exhausted cycle reason
--   walkMux-fuel-sufficient         : same at the standard fuel = length signals
--
-- Note: extractSignal normalizes to a complex if-then-else on bounds checking,
-- preventing with-abstraction from matching it in the goal type. Properties
-- involving extractSignal's return value are therefore stated at the
-- checkPresenceP/checkSignalPresence abstraction boundary, which is where
-- multiplexing correctness is decided.
--
-- Runtime cost: zero (proofs erased by MAlonzo compilation).
module Aletheia.CAN.SignalExtraction.Properties where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (signalNameStr)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; SignalNotPresent)
open import Aletheia.CAN.SignalExtraction
    using (checkPresenceP; checkSignalPresence; extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findSignalByName; findSignalInList)
open import Aletheia.DBC.Validator.Checks using (walkMux; findSignalPresence)
open import Aletheia.DBC.Types using (DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.Error using (ExtractionError)
open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.NonEmpty using (List⁺)
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapₘ)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to is-just)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)

-- ============================================================================
-- PROPERTY 1: checkPresenceP — When-case finds the multiplexor signal
-- ============================================================================

-- If checkPresenceP succeeds on a When-presence (with positive fuel), the
-- multiplexor signal exists in the message. This guarantees the DBC reference
-- is valid (the mux signal was defined in the message).
checkPresenceP-finds-mux : ∀ {n} (f : ℕ) (frame : CANFrame n) (msg : DBCMessage)
  (muxName : Identifier) (muxValues : List⁺ ℕ)
  → checkPresenceP (suc f) frame msg (When muxName muxValues) ≡ nothing
  → Is-just (findSignalByName (Identifier.name muxName) msg)
checkPresenceP-finds-mux f frame msg muxName muxValues eq
  with findSignalByName (Identifier.name muxName) msg
... | nothing = case eq of λ ()
... | just _  = is-just tt

-- ============================================================================
-- PROPERTY 2: checkPresenceP — rejects missing multiplexor signal
-- ============================================================================

-- If the multiplexor signal doesn't exist in the message, checkPresenceP
-- on a When-presence fails. Guarantees that typos or renamed signals are
-- caught at runtime as a defensive backstop to the static validator.
checkPresenceP-rejects-missing : ∀ {n} (f : ℕ) (frame : CANFrame n) (msg : DBCMessage)
  (muxName : Identifier) (muxValues : List⁺ ℕ)
  → findSignalByName (Identifier.name muxName) msg ≡ nothing
  → Is-just (checkPresenceP (suc f) frame msg (When muxName muxValues))
checkPresenceP-rejects-missing f frame msg muxName muxValues eq
  with findSignalByName (Identifier.name muxName) msg
... | nothing = is-just tt
... | just _  = case eq of λ ()

-- ============================================================================
-- PROPERTY 3: Signal presence check soundness
-- ============================================================================

-- If the presence check passes, the signal is either Always present or
-- guarded by a When clause whose top-level recursive walker also passed.
-- This is the key dispatch property: Always signals bypass the recursive
-- walk entirely, and When signals are validated by checkPresenceP at the
-- top-level depth bound (length signals).
checkSignalPresence-sound : ∀ {n} (frame : CANFrame n) (msg : DBCMessage) (sig : DBCSignal)
  → checkSignalPresence frame msg sig ≡ nothing
  → (DBCSignal.presence sig ≡ Always)
    ⊎ (∃[ muxName ] ∃[ muxVals ]
        (DBCSignal.presence sig ≡ When muxName muxVals
         × checkPresenceP (length (DBCMessage.signals msg)) frame msg
             (When muxName muxVals) ≡ nothing))
checkSignalPresence-sound frame msg sig eq with DBCSignal.presence sig
... | Always               = inj₁ refl
... | When muxName muxVals = inj₂ (muxName , muxVals , refl , eq)

-- ============================================================================
-- PROPERTY 4: Extraction respects multiplexor
-- ============================================================================

-- When the presence check fails, extractSignalDirect returns SignalNotPresent
-- with the failure reason. This guarantees no data is returned for a
-- multiplexed signal whose multiplexor value doesn't match (or whose mux
-- ancestor chain isn't satisfied).
extractSignalDirect-mux : ∀ {n} (msg : DBCMessage) (frame : CANFrame n) (sig : DBCSignal)
  (reason : ExtractionError)
  → checkSignalPresence frame msg sig ≡ just reason
  → extractSignalDirect msg frame sig ≡ SignalNotPresent reason
extractSignalDirect-mux msg frame sig reason eq
  with checkSignalPresence frame msg sig
... | just r = cong SignalNotPresent (just-injective eq)

-- ============================================================================
-- PROPERTY 5: walkMux blocks the cycle branch in checkPresenceP (Gap 12.2)
-- ============================================================================
--
-- Closes deferred non-blocker 12.2 from project_system_review_deferred.md:
-- formal agreement between the static validator's `walkMux` and the runtime
-- presence walker `checkPresenceP`. The two walkers operate in different
-- namespaces:
--
--   * walkMux  : ℕ → List DBCSignal → SignalPresence → Bool
--                (true = "no cycle within fuel"); discriminator
--                `signalNameStr s ≟ name`
--   * checkPresenceP : ℕ → CANFrame n → DBCMessage → SignalPresence → Maybe ExtractionError
--                (nothing = "presence held"); discriminator
--                `name ≟ signalNameStr s`
--
-- We avoid ExtractionError disequality by introducing an inductive
-- predicate `HitsCycleBranch` that captures structurally the shape of
-- "checkPresenceP exhausts fuel and would emit the cycle reason". The main
-- theorem then states: walkMux ≡ true → ¬ HitsCycleBranch.
--
-- This lifts the operational claim "fuel = length sigs is sufficient for all
-- acyclic chains" to a propositional one: any presence chain that the
-- validator accepts cannot make the runtime walker run out of fuel.

-- The cycle branch is reached either directly (fuel = 0 with When) or
-- recursively through a mux ancestor whose presence chain hits the branch.
data HitsCycleBranch : ∀ {n} → ℕ → CANFrame n → DBCMessage → SignalPresence → Set where
  hit-zero : ∀ {n} (frame : CANFrame n) (msg : DBCMessage)
             (name : Identifier) (vals : List⁺ ℕ)
           → HitsCycleBranch zero frame msg (When name vals)
  hit-suc  : ∀ {n} (f : ℕ) (frame : CANFrame n) (msg : DBCMessage)
             (name : Identifier) (vals : List⁺ ℕ) (sig : DBCSignal)
           → findSignalByName (Identifier.name name) msg ≡ just sig
           → HitsCycleBranch f frame msg (DBCSignal.presence sig)
           → HitsCycleBranch (suc f) frame msg (When name vals)

-- Bridge lemmas: relate `findSignalInList` (used by checkPresenceP via
-- findSignalByName) and `findSignalPresence` (used by walkMux). They use
-- symmetric discriminator orders but agree on every input by symmetry of _≡_.
private
  -- Bridge lemmas: since findSignalPresence is now defined as
  -- mapₘ DBCSignal.presence ∘ findSignalInList, both directions
  -- reduce to congruence on the hypothesis.

  findSignal-bridge-nothing :
    ∀ name (sigs : List DBCSignal)
    → findSignalInList name sigs ≡ nothing
    → findSignalPresence name sigs ≡ nothing
  findSignal-bridge-nothing _ _ eq = cong (mapₘ DBCSignal.presence) eq

  findSignal-bridge-just :
    ∀ name (sigs : List DBCSignal) (sig : DBCSignal)
    → findSignalInList name sigs ≡ just sig
    → findSignalPresence name sigs ≡ just (DBCSignal.presence sig)
  findSignal-bridge-just _ _ _ eq = cong (mapₘ DBCSignal.presence) eq

-- Main theorem: if walkMux validates this presence chain at fuel f, then
-- checkPresenceP at the same fuel cannot reach its fuel-exhausted cycle branch.
walkMux-blocks-cycle-branch :
  ∀ {n} (f : ℕ) (frame : CANFrame n) (msg : DBCMessage) (p : SignalPresence)
  → walkMux f (DBCMessage.signals msg) p ≡ true
  → ¬ HitsCycleBranch f frame msg p
walkMux-blocks-cycle-branch _       _     _   Always         _     ()
walkMux-blocks-cycle-branch zero    _     _   (When _ _)     wm-eq _ =
  case wm-eq of λ ()
walkMux-blocks-cycle-branch (suc f) frame msg (When muxName _) wm-eq
                            (hit-suc _ _ _ _ _ sig fbn-eq inner-hit)
  with findSignalPresence (Identifier.name muxName) (DBCMessage.signals msg)
     | findSignal-bridge-just (Identifier.name muxName) (DBCMessage.signals msg) sig fbn-eq
... | nothing | bridge-eq = case bridge-eq of λ ()
... | just p  | refl      =
        walkMux-blocks-cycle-branch f frame msg p wm-eq inner-hit

-- Corollary at the standard fuel level (fuel = length signals).
walkMux-fuel-sufficient :
  ∀ {n} (frame : CANFrame n) (msg : DBCMessage) (p : SignalPresence)
  → walkMux (length (DBCMessage.signals msg)) (DBCMessage.signals msg) p ≡ true
  → ¬ HitsCycleBranch (length (DBCMessage.signals msg)) frame msg p
walkMux-fuel-sufficient frame msg p =
  walkMux-blocks-cycle-branch (length (DBCMessage.signals msg)) frame msg p
