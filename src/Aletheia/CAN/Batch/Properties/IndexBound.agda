-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every index the binary extraction reply carries names a signal of the
-- frame's message, and the DBC reply writes that signal's name there.
--
-- Purpose: Prove that each key of the indexed extraction's three partitions
--   is below the signal count of the message the frame's id finds, and that
--   the message's formatted "signals" array holds the message's signals in
--   order, so a binding's name table built from the DBC reply holds, at
--   every index the extraction carries, that signal's name.
-- Key results: extractAllSignalsIndexed-below, extractAllSignalsIndexed-named.
module Aletheia.CAN.Batch.Properties.IndexBound where

open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Standard; Extended)
open import Aletheia.DBC.Formatter using (formatCANId; formatDBCSignal; formatDBCMessage)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.Prelude using (listIndex)
open import Aletheia.Protocol.JSON.Lookup using (getObject; lookupArray; lookupChars)
open import Aletheia.Protocol.JSON.Types using (JSON)
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
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length; map) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapAll)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mapₘ)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z<s)
open import Data.Nat.Properties using (+-suc; m<m+n)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

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

-- ============================================================================
-- THE NAME A READER TAKES AT AN INDEX
-- ============================================================================

-- The name a reader takes from a signal object: its "name" field.
signalEntryName : JSON → Maybe (List Char)
signalEntryName j = getObject j >>= lookupChars "name"

-- The name a reader takes at index `k` of a message object's "signals"
-- array, as a binding's name table built from the DBC reply holds it.
signalNameAt : ℕ → JSON → Maybe (List Char)
signalNameAt k m = getObject m >>= lookupArray "signals" >>= listIndex k >>= signalEntryName

private
  -- The CAN id's fields, which open a message object, are not "signals".
  canId-skips-signals : ∀ (i : CANId) fs
    → lookupArray "signals" (formatCANId i ++ₗ fs) ≡ lookupArray "signals" fs
  canId-skips-signals (Standard _ _) _ = refl
  canId-skips-signals (Extended _ _) _ = refl

  listIndex-below : ∀ {A : Set} k (xs : List A) → k < length xs → ∃[ x ] listIndex k xs ≡ just x
  listIndex-below _       []       ()
  listIndex-below zero    (x ∷ _)  _         = x , refl
  listIndex-below (suc k) (_ ∷ xs) (s≤s k<) = listIndex-below k xs k<

-- THEOREM: the "signals" array a reader takes from a formatted message is
-- the message's signals, each formatted, in the message's order.
formatDBCMessage-signals : ∀ msg
  → (getObject (formatDBCMessage msg) >>= lookupArray "signals")
    ≡ just (map (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg))
formatDBCMessage-signals msg = canId-skips-signals (DBCMessage.id msg) _

-- A formatted signal's "name" is the signal's name.
formatDBCSignal-name : ∀ frameBytes sig
  → signalEntryName (formatDBCSignal frameBytes sig) ≡ just (Identifier.name (DBCSignal.name sig))
formatDBCSignal-name _ _ = refl

-- THEOREM: formatted signals have one entry per signal, and at every index
-- the name a reader takes is the name of the signal at that index; past
-- the last signal there is none.
formatDBCSignals-length : ∀ frameBytes sigs → length (map (formatDBCSignal frameBytes) sigs) ≡ length sigs
formatDBCSignals-length frameBytes = length-map (formatDBCSignal frameBytes)

formatDBCSignals-name-at : ∀ frameBytes sigs k
  → (listIndex k (map (formatDBCSignal frameBytes) sigs) >>= signalEntryName)
    ≡ mapₘ (Identifier.name ∘ DBCSignal.name) (listIndex k sigs)
formatDBCSignals-name-at _          []         _       = refl
formatDBCSignals-name-at frameBytes (sig ∷ _)  zero    = formatDBCSignal-name frameBytes sig
formatDBCSignals-name-at frameBytes (_ ∷ sigs) (suc k) = formatDBCSignals-name-at frameBytes sigs k

-- `k` is the position of a signal of `msg`, the one `extractIndexedFrom`
-- keys by `k`, and the name a reader takes at `k` of the formatted
-- message's "signals" array is that signal's name.
NamedAt : DBCMessage → ℕ → Set
NamedAt msg k = ∃[ sig ] ( listIndex k (DBCMessage.signals msg) ≡ just sig
                         × signalNameAt k (formatDBCMessage msg) ≡ just (Identifier.name (DBCSignal.name sig)))

named-below : ∀ msg {k} → k < length (DBCMessage.signals msg) → NamedAt msg k
named-below msg {k} k< with listIndex-below k (DBCMessage.signals msg) k<
... | sig , found = sig , found ,
  trans (cong (λ s → s >>= listIndex k >>= signalEntryName) (formatDBCMessage-signals msg))
        (trans (formatDBCSignals-name-at (dlcBytes (DBCMessage.dlc msg)) (DBCMessage.signals msg) k)
               (cong (mapₘ (Identifier.name ∘ DBCSignal.name)) found))

-- An indexed extraction's keys are named in the formatted message the
-- frame's id finds; a refusal carries none.
IndexedNamed : ∀ {n} → DBC → CANFrame n → FrameError ⊎ IndexedExtractionResults → Set
IndexedNamed _   _     (inj₁ _) = ⊤
IndexedNamed dbc frame (inj₂ r) =
  ∃[ msg ] (findMessageById (CANFrame.id frame) dbc ≡ just msg × KeysAll (NamedAt msg) r)

-- THEOREM: every signal index the binary extraction reply carries, in its
-- values, its errors and its absent signals, indexes the "signals" array
-- the DBC reply writes for the message the frame's id finds, and the name a
-- reader takes there is the name of the signal the kernel extracted at
-- that index.
extractAllSignalsIndexed-named : ∀ {n} (dbc : DBC) (frame : CANFrame n)
  → IndexedNamed dbc frame (extractAllSignalsIndexed dbc frame)
extractAllSignalsIndexed-named dbc frame =
  join (extractAllSignalsIndexed dbc frame) (extractAllSignalsIndexed-below dbc frame)
  where
    join : ∀ r → IndexedBelow dbc frame r → IndexedNamed dbc frame r
    join (inj₁ _) _                     = tt
    join (inj₂ r) (msg , found , below) = msg , found , keys-weaken (named-below msg) r below
