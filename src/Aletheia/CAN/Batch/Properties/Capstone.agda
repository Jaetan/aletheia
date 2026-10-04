-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Capstone theorem: a valid DBC makes batch frame building roundtrip.
--
-- Purpose: from the DBC's validity, the always-present and pairwise distinct
--   signals a request names are physically disjoint and fit the message's
--   frame; with the batch roundtrip, every signal a build injected extracts
--   back to its value.  Acceptance of each value is the injection's own
--   check, so the theorem takes no premise on the values.
-- Key result: validDBC-roundtrip.
module Aletheia.CAN.Batch.Properties.Capstone where

open import Aletheia.CAN.Batch.Properties.Roundtrip using (
  DisjointFromAll; dfa-nil; dfa-cons;
  AllPairsDisjoint; apd-nil; apd-cons;
  AllSignalsFit; asf-nil; asf-cons;
  AllFromMessage; afm-nil; afm-cons;
  pairs;
  injectAll-roundtrip)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.Encoding using (extractSignal)
open import Aletheia.CAN.BatchFrameBuilding using (Request; injectAll)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Decidable using (SignalPairValid; both-always; _≟-DBCSignal_)
open import Aletheia.DBC.Properties using (signalPairValid-sym; extractDisjointness)
open import Aletheia.DBC.Validity using (IsValidDBC; validated; BitsInFrame)
open import Aletheia.Prelude using (Found)
import Data.List.Relation.Unary.All as StdAll
import Data.List.Relation.Unary.AllPairs as StdAP
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just)
open import Data.Sum using (inj₂)
open import Data.Rational using (ℚ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)

-- ============================================================================
-- PREDICATES FOR CAPSTONE PRECONDITIONS
-- ============================================================================

-- All signals in the list are always-present (not multiplexed)
data AllAlwaysPresent : List (DBCSignal × ℚ) → Set where
  aap-nil  : AllAlwaysPresent []
  aap-cons : ∀ {s v rest}
    → DBCSignal.presence s ≡ Always
    → AllAlwaysPresent rest
    → AllAlwaysPresent ((s , v) ∷ rest)

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

-- ============================================================================
-- DECIDABLE CHECKERS FOR CAPSTONE PRECONDITIONS
-- ============================================================================

private
  isAlways? : (p : SignalPresence) → Dec (p ≡ Always)
  isAlways? Always     = yes refl
  isAlways? (When _ _) = no (λ ())

allAlwaysPresent? : (pairs : List (DBCSignal × ℚ)) → Dec (AllAlwaysPresent pairs)
allAlwaysPresent? [] = yes aap-nil
allAlwaysPresent? ((s , v) ∷ rest) with isAlways? (DBCSignal.presence s)
... | no ¬a = no λ { (aap-cons eq _) → ¬a eq }
... | yes a with allAlwaysPresent? rest
...   | no ¬ar = no λ { (aap-cons _ ar) → ¬ar ar }
...   | yes ar = yes (aap-cons a ar)

open import Data.List.Membership.DecPropositional {A = DBCSignal} _≟-DBCSignal_ using (_∈?_)

allFromMessage? : (pairs : List (DBCSignal × ℚ)) → (msg : DBCMessage)
                → Dec (AllFromMessage msg pairs)
allFromMessage? [] msg = yes afm-nil
allFromMessage? ((s , v) ∷ rest) msg with s ∈? DBCMessage.signals msg
... | no ¬s∈ = no λ { (afm-cons s∈ _) → ¬s∈ s∈ }
... | yes s∈ with allFromMessage? rest msg
...   | no ¬ar = no λ { (afm-cons _ ar) → ¬ar ar }
...   | yes ar = yes (afm-cons s∈ ar)

private
  distinctFromAll? : (s : DBCSignal) → (rest : List (DBCSignal × ℚ))
                   → Dec (DistinctFromAll s rest)
  distinctFromAll? s [] = yes dist-nil
  distinctFromAll? s ((s' , v) ∷ rest) with s ≟-DBCSignal s'
  ... | yes eq = no λ { (dist-cons s≢ _) → s≢ eq }
  ... | no s≢ with distinctFromAll? s rest
  ...   | no ¬dr = no λ { (dist-cons _ dr) → ¬dr dr }
  ...   | yes dr = yes (dist-cons s≢ dr)

pairsDistinct? : (pairs : List (DBCSignal × ℚ)) → Dec (PairsDistinct pairs)
pairsDistinct? [] = yes pd-nil
pairsDistinct? ((s , v) ∷ rest) with distinctFromAll? s rest
... | no ¬da = no λ { (pd-cons da _) → ¬da da }
... | yes da with pairsDistinct? rest
...   | no ¬pr = no λ { (pd-cons _ pr) → ¬pr pr }
...   | yes pr = yes (pd-cons da pr)

-- ============================================================================
-- GAP 1: IsValidDBC → AllPairsDisjoint
-- ============================================================================

private
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

  buildDFA : ∀ {n msg} (s : DBCSignal) (rest : List (DBCSignal × ℚ))
    → StdAP.AllPairs (SignalPairValid n) (DBCMessage.signals msg)
    → s ∈ DBCMessage.signals msg
    → DBCSignal.presence s ≡ Always
    → AllFromMessage msg rest
    → AllAlwaysPresent rest
    → DistinctFromAll s rest
    → DisjointFromAll n s rest
  buildDFA _ [] _ _ _ _ _ _ = dfa-nil
  buildDFA s ((s' , _) ∷ rest) ap s∈ refl
      (afm-cons s'∈ afm-rest) (aap-cons refl aap-rest) (dist-cons s≢s' dist-rest) =
    dfa-cons
      (extractDisjointness (allPairs-lookup ap s∈ s'∈ s≢s') both-always)
      (buildDFA s rest ap s∈ refl afm-rest aap-rest dist-rest)

validDBC→allPairsDisjoint : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → IsValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllAlwaysPresent pairs
  → AllFromMessage msg pairs
  → PairsDistinct pairs
  → AllPairsDisjoint (dlcBytes (DBCMessage.dlc msg)) pairs
validDBC→allPairsDisjoint [] _ _ _ _ _ = apd-nil
validDBC→allPairsDisjoint ((s , v) ∷ rest) iv msg∈
    (aap-cons ps aap-rest) (afm-cons s∈ afm-rest) (pd-cons dist pd-rest) =
  apd-cons
    (buildDFA s rest ap s∈ ps afm-rest aap-rest dist)
    (validDBC→allPairsDisjoint rest iv msg∈ aap-rest afm-rest pd-rest)
  where
    ap = StdAll.lookup (IsValidDBC.sigPairsValid iv) msg∈

-- ============================================================================
-- GAP 2: IsValidDBC → AllSignalsFit
-- ============================================================================

private
  buildASF : ∀ {msg} (pairs : List (DBCSignal × ℚ))
    → StdAll.All (BitsInFrame (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
    → AllFromMessage msg pairs
    → AllSignalsFit (dlcBytes (DBCMessage.dlc msg)) pairs
  buildASF [] _ _ = asf-nil
  buildASF ((s , _) ∷ rest) bifs (afm-cons s∈ afm-rest) =
    asf-cons
      (StdAll.lookup bifs s∈)
      (buildASF rest bifs afm-rest)

validDBC→allSignalsFit : ∀ {dbc msg} (pairs : List (DBCSignal × ℚ))
  → IsValidDBC dbc
  → msg ∈ DBC.messages dbc
  → AllFromMessage msg pairs
  → AllSignalsFit (dlcBytes (DBCMessage.dlc msg)) pairs
validDBC→allSignalsFit pairs iv msg∈ afm =
  buildASF pairs
    (StdAll.lookup (IsValidDBC.bitsInFrame iv) msg∈)
    afm

-- ============================================================================
-- CAPSTONE THEOREM
-- ============================================================================

validDBC-roundtrip :
  ∀ (dbc : DBC) (iv : IsValidDBC dbc) (msg : Found (DBC.messages dbc))
    (reqs : List (Request (Found.item msg)))
    (frame frame' : CANFrame (dlcBytes (DBCMessage.dlc (Found.item msg))))
  → Found.item msg ∈ DBC.messages dbc
  → AllAlwaysPresent (pairs {Found.item msg} reqs)
  → AllFromMessage (Found.item msg) (pairs {Found.item msg} reqs)
  → PairsDistinct (pairs {Found.item msg} reqs)
  → injectAll (validated dbc iv) msg frame reqs ≡ inj₂ frame'
  → ∀ {s v} → (s , v) ∈ pairs {Found.item msg} reqs
  → extractSignal frame' (DBCSignal.signalDef s) (DBCSignal.byteOrder s) ≡ just v
validDBC-roundtrip dbc iv msg reqs frame frame' msg∈ aap afm pd eq mem =
  injectAll-roundtrip dbc iv msg reqs frame frame' msg∈ afm
    (validDBC→allPairsDisjoint (pairs {Found.item msg} reqs) iv msg∈ aap afm pd)
    (validDBC→allSignalsFit (pairs {Found.item msg} reqs) iv msg∈ afm)
    eq mem
