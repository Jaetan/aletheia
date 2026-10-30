-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every index the binary extraction reply carries names a signal of the
-- frame's message.
--
-- Purpose: Prove that each key of the indexed extraction's three partitions
--   is below the signal count of the message the frame's id finds, so a
--   binding reads the index straight into that message's signal list.
-- Key result: extractAllSignalsIndexed-below.
module Aletheia.CAN.Batch.Properties.IndexBound where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using
  (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.Error using
  (MuxValueMismatch; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed;
   ValueExceedsWireRange; InContext; SignalPastFrameEnd; FrameError)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.CAN.BatchExtraction using
  ( PartitionedResults; mkPartitionedResults; IndexedExtractionResults
  ; wireFits; categorizeWith; categorizeIndexed; combinePartitioned
  ; extractIndexedFrom; extractAllSignalsIndexedFromMessage; extractAllSignalsIndexed
  )
open import Aletheia.DBC.Types using (DBC; DBCMessage; signalNameStr)

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapAll)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _<_; z<s)
open import Data.Nat.Properties using (+-suc; m<m+n)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

-- Every key of a partitioned result satisfies `P`.
KeysAll : ∀ {E : Set} → (ℕ → Set) → PartitionedResults ℕ E → Set
KeysAll P r = All (P ∘ proj₁) (PartitionedResults.values r)
            × All (P ∘ proj₁) (PartitionedResults.errors r)
            × All P (PartitionedResults.absent r)

-- The categoriser keys every entry it makes with the key it was given.
categorizeWith-keys : ∀ {E : Set} {P : ℕ → Set} (toErr : ℕ → ExtractionResult → E) key r
  → P key → KeysAll P (categorizeWith toErr key r)
categorizeWith-keys _ _ (Success v) pk with wireFits v
... | true  = pk ∷ [] , [] , []
... | false = [] , pk ∷ [] , []
categorizeWith-keys _ _ SignalNotInDBC                             pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent MuxValueMismatch)        pk = [] , [] , pk ∷ []
categorizeWith-keys _ _ (SignalNotPresent (MuxSignalNotFound _))   pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent MuxChainCycle)           pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent (MuxExtractionFailed _)) pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent ValueExceedsWireRange)   pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent (SignalPastFrameEnd _))  pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (SignalNotPresent (InContext _ _))         pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (ValueOutOfBounds _ _ _)                   pk = [] , pk ∷ [] , []
categorizeWith-keys _ _ (ExtractionFailed _)                       pk = [] , pk ∷ [] , []

private
  combine-keys : ∀ {E : Set} {P : ℕ → Set} (a b : PartitionedResults ℕ E)
    → KeysAll P a → KeysAll P b → KeysAll P (combinePartitioned a b)
  combine-keys (mkPartitionedResults _ _ _) (mkPartitionedResults _ _ _) (va , ea , aa) (vb , eb , ab) =
    ++⁺ va vb , ++⁺ ea eb , ++⁺ aa ab

  keys-weaken : ∀ {E : Set} {P Q : ℕ → Set} → (∀ {k} → P k → Q k)
    → (r : PartitionedResults ℕ E) → KeysAll P r → KeysAll Q r
  keys-weaken f _ (v , e , a) = mapAll f v , mapAll f e , mapAll f a

-- The signals from position `idx` on are keyed below `idx` plus their count.
extractIndexedFrom-below : ∀ {n} (frame : CANFrame n) msg idx sigs
  → KeysAll (_< idx + length sigs) (extractIndexedFrom frame msg idx sigs)
extractIndexedFrom-below frame msg idx []           = [] , [] , []
extractIndexedFrom-below frame msg idx (sig ∷ sigs) =
  combine-keys
    (categorizeIndexed (signalNameStr sig) idx (extractSignalDirect msg frame sig))
    (extractIndexedFrom frame msg (suc idx) sigs)
    (categorizeWith-keys _ idx (extractSignalDirect msg frame sig) (m<m+n idx z<s))
    (keys-weaken (λ {k} k< → subst (k <_) (sym (+-suc idx (length sigs))) k<)
       (extractIndexedFrom frame msg (suc idx) sigs)
       (extractIndexedFrom-below frame msg (suc idx) sigs))

extractAllSignalsIndexedFromMessage-below : ∀ {n} (frame : CANFrame n) msg
  → KeysAll (_< length (DBCMessage.signals msg)) (extractAllSignalsIndexedFromMessage frame msg)
extractAllSignalsIndexedFromMessage-below frame msg =
  extractIndexedFrom-below frame msg 0 (DBCMessage.signals msg)

-- An indexed extraction's keys name signals of the message the frame's id
-- finds; a refusal names none.
IndexedBelow : ∀ {n} → DBC → CANFrame n → FrameError ⊎ IndexedExtractionResults → Set
IndexedBelow _   _     (inj₁ _) = ⊤
IndexedBelow dbc frame (inj₂ r) =
  ∃[ msg ] (findMessageById (CANFrame.id frame) dbc ≡ just msg
           × KeysAll (_< length (DBCMessage.signals msg)) r)

-- THEOREM: every signal index the binary extraction reply carries, in its
-- values, its errors and its absent signals, is below the signal count of
-- the message the frame's id finds in the DBC.
extractAllSignalsIndexed-below : ∀ {n} (dbc : DBC) (frame : CANFrame n)
  → IndexedBelow dbc frame (extractAllSignalsIndexed dbc frame)
extractAllSignalsIndexed-below dbc frame with findMessageById (CANFrame.id frame) dbc in found
... | nothing  = tt
... | just msg = msg , found , extractAllSignalsIndexedFromMessage-below frame msg
