-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What the cross-message checks group by: a message's CAN ID or name, or a
-- signal's name, each turned into a list of numbers so that one order sorts
-- them all (`Aletheia.Data.KeyConflicts`).  Each message, or each signal of
-- each message, becomes an entry owned by the message's position, and the
-- checks report one issue per group of entries that share a key under
-- different owners.
module Aletheia.DBC.Validator.SharedKeys where

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.Data.KeyConflicts using (module Keyed)
open import Aletheia.DBC.Types using (DBCMessage; signalNameStr; messageNameStr)
open import Data.Char using (Char) renaming (toℕ to charToℕ)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty using (List⁺) renaming (toList to toList⁺)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList) renaming (toList to stringToList; _++_ to _++ₛ_)
open import Function using (_∘_)

-- A CAN ID as a key; a standard and an extended identifier never share one.
canIdKey : CANId → List ℕ
canIdKey (CANId.Standard n _) = 0 ∷ n ∷ []
canIdKey (CANId.Extended n _) = 1 ∷ n ∷ []

-- A CAN ID as text: its number, as the issues name it.
showCanIdText : CANId → String
showCanIdText (CANId.Standard n _) = showℕ n
showCanIdText (CANId.Extended n _) = showℕ n

-- A name as a key.
nameKey : String → List ℕ
nameKey s = map charToℕ (stringToList s)

-- The names of a message's signals, in order.
messageSignalNames : DBCMessage → List String
messageSignalNames msg = map signalNameStr (DBCMessage.signals msg)

-- One element of a group: its position in the list checked, the position of
-- the message it belongs to, its key, that message, and the name the key was
-- made from (empty for a message keyed by its CAN ID).
record Entry : Set where
  constructor entry
  field
    position : ℕ
    owner    : ℕ
    key      : List ℕ
    message  : DBCMessage
    label    : String
open Entry public

-- Each message as an entry owned by itself, keyed by `k`, from position `i`.
messageEntries : (DBCMessage → List ℕ) → (DBCMessage → String) → ℕ → List DBCMessage → List Entry
messageEntries k l i []       = []
messageEntries k l i (m ∷ ms) = entry i i (k m) m (l m) ∷ messageEntries k l (suc i) ms

-- Each signal name of each message, with the message and its position.
ownedSignalNames : ℕ → List DBCMessage → List (ℕ × DBCMessage × String)
ownedSignalNames i []       = []
ownedSignalNames i (m ∷ ms) = map (λ n → i , m , n) (messageSignalNames m) ++ₗ ownedSignalNames (suc i) ms

-- Signal names as entries owned by their message, from position `i`.
numbered : ℕ → List (ℕ × DBCMessage × String) → List Entry
numbered i []                  = []
numbered i ((o , m , n) ∷ ons) = entry i o (nameKey n) m n ∷ numbered (suc i) ons

-- Each message keyed by its CAN ID.
messageIdEntries : List DBCMessage → List Entry
messageIdEntries = messageEntries (canIdKey ∘ DBCMessage.id) (λ _ → "") 0

signalEntries : List DBCMessage → List Entry
signalEntries msgs = numbered 0 (ownedSignalNames 0 msgs)

-- The groups of entries sharing a key under different owners, in order of
-- their first entry.
sharedKeyGroups : List Entry → List (List⁺ Entry)
sharedKeyGroups = Keyed.keyConflicts key owner position

-- A group with one entry per owner, in owner order.
perOwner : List⁺ Entry → List⁺ Entry
perOwner = Keyed.firstPerTag key owner position

-- "A and B", "A, B and C".
joinAnd : List String → String
joinAnd items = fromList (go items)
  where
    go : List String → List Char
    go []           = []
    go (a ∷ [])     = stringToList a
    go (a ∷ b ∷ []) = stringToList a ++ₗ stringToList " and " ++ₗ stringToList b
    go (a ∷ rest)   = stringToList a ++ₗ stringToList ", " ++ₗ go rest

-- A name in quotes.
quoted : String → String
quoted s = "'" ++ₛ s ++ₛ "'"

-- The messages of a group sharing a CAN ID, named.
sharedIdText : List⁺ Entry → String
sharedIdText g =
  "Messages " ++ₛ joinAnd (map (quoted ∘ messageNameStr ∘ message) (toList⁺ g)) ++ₛ " share the same CAN ID"
