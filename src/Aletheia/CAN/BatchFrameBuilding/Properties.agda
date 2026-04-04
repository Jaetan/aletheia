{-# OPTIONS --safe --without-K #-}

-- Equivalence between index-based and name-based signal lookup.
--
-- Purpose: Prove that the binary FFI path (lookupSignalsByIndex, buildFrameByIndex,
-- updateFrameByIndex) produces the same result as the JSON path (lookupSignals,
-- buildFrame, updateFrame) when each index resolves to the same signal as the
-- corresponding name.
--
-- Risk mitigated: If the two paths diverged, the binary FFI could silently produce
-- different frames than the JSON API for the same logical operation.
--
-- Properties:
--   (1) lookupSignalsByIndex-lookupSignals-equiv: core lookup equivalence
--   (2) buildFrameByIndex-buildFrame-equiv: build frame equivalence
--   (3) updateFrameByIndex-updateFrame-equiv: update frame equivalence
module Aletheia.CAN.BatchFrameBuilding.Properties where

open import Aletheia.CAN.BatchFrameBuilding
    using (lookupSignals; lookupSignalsByIndex; listIndex;
           buildFrame; buildFrameByIndex;
           updateFrame; updateFrameByIndex;
           validateAndBuild; injectAll)
open import Aletheia.CAN.DBCHelpers using (findSignalByName; findMessageById; canIdEquals)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- ============================================================================
-- PRECONDITION: per-element signal matching
-- ============================================================================

-- Each index-value pair matches a name-value pair when:
-- (1) the ℚ values are the same, and
-- (2) both lookups resolve to the same DBCSignal
data SignalMatch (msg : DBCMessage) : (String × ℚ) → (ℕ × ℚ) → Set where
  match : ∀ {name idx value} (sig : DBCSignal)
    → findSignalByName name msg ≡ just sig
    → listIndex idx (DBCMessage.signals msg) ≡ just sig
    → SignalMatch msg (name , value) (idx , value)

-- Pointwise matching for two signal lists
data AllMatch (msg : DBCMessage) : List (String × ℚ) → List (ℕ × ℚ) → Set where
  []  : AllMatch msg [] []
  _∷_ : ∀ {nv iv ns is}
    → SignalMatch msg nv iv → AllMatch msg ns is → AllMatch msg (nv ∷ ns) (iv ∷ is)

-- ============================================================================
-- PROPERTY 1: Core lookup equivalence
-- ============================================================================

-- When every element matches, both lookup functions return the same result.
lookupSignalsByIndex-lookupSignals-equiv :
  ∀ (names : List (String × ℚ)) (indices : List (ℕ × ℚ)) (msg : DBCMessage)
  → AllMatch msg names indices
  → lookupSignals names msg ≡ lookupSignalsByIndex indices msg
lookupSignalsByIndex-lookupSignals-equiv [] [] _ [] = refl
lookupSignalsByIndex-lookupSignals-equiv
  ((name , value) ∷ ns) ((idx , .value) ∷ is) msg (match sig name-eq idx-eq ∷ rest)
  with findSignalByName name msg | name-eq
... | .(just sig) | refl
  with listIndex idx (DBCMessage.signals msg) | idx-eq
... | .(just sig) | refl
  with lookupSignals ns msg | lookupSignalsByIndex is msg
     | lookupSignalsByIndex-lookupSignals-equiv ns is msg rest
...   | inj₁ err | .(inj₁ err) | refl = refl
...   | inj₂ sigs | .(inj₂ sigs) | refl = refl

-- ============================================================================
-- PROPERTY 2: Build frame equivalence
-- ============================================================================

-- If lookups agree, buildFrame and buildFrameByIndex produce the same frame.
-- Both call the shared validateAndBuild after lookup, so the proof just
-- bridges the lookup step.
buildFrameByIndex-buildFrame-equiv :
  ∀ (dbc : DBC) (canId : CANId) (dlc : ℕ)
    (names : List (String × ℚ)) (indices : List (ℕ × ℚ))
  → (∀ msg → findMessageById canId dbc ≡ just msg → AllMatch msg names indices)
  → buildFrame dbc canId dlc names ≡ buildFrameByIndex dbc canId dlc indices
buildFrameByIndex-buildFrame-equiv dbc canId dlc names indices pre
  with findMessageById canId dbc
... | nothing = refl
... | just msg
  with lookupSignals names msg | lookupSignalsByIndex indices msg
     | lookupSignalsByIndex-lookupSignals-equiv names indices msg (pre msg refl)
...   | inj₁ err | .(inj₁ err) | refl = refl
...   | inj₂ sigs | .(inj₂ sigs) | refl = refl

-- ============================================================================
-- PROPERTY 3: Update frame equivalence
-- ============================================================================

-- If lookups agree, updateFrame and updateFrameByIndex produce the same result.
-- Both share the same CAN ID check, findMessageById, and injectAll — only
-- the lookup step differs.
updateFrameByIndex-updateFrame-equiv :
  ∀ {n} (dbc : DBC) (canId : CANId) (frame : CANFrame n)
    (names : List (String × ℚ)) (indices : List (ℕ × ℚ))
  → (∀ msg → findMessageById canId dbc ≡ just msg → AllMatch msg names indices)
  → updateFrame dbc canId frame names ≡ updateFrameByIndex dbc canId frame indices
updateFrameByIndex-updateFrame-equiv dbc canId frame names indices pre
  with canIdEquals canId (CANFrame.id frame)
... | false = refl
... | true
  with findMessageById canId dbc
... | nothing = refl
... | just msg
  with lookupSignals names msg | lookupSignalsByIndex indices msg
     | lookupSignalsByIndex-lookupSignals-equiv names indices msg (pre msg refl)
...   | inj₁ err | .(inj₁ err) | refl = refl
...   | inj₂ sigs | .(inj₂ sigs) | refl = refl
