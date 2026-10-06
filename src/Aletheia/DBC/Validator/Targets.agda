-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What a reference in a DBC can name, indexed once so that each lookup
-- costs time logarithmic in what it searches: node and environment-variable
-- names as sets, messages by CAN ID.  The validator resolves every sender,
-- receiver and comment target through these, and `formatDBCText` keeps the
-- node names it has already derived in one, so each costs time linear in
-- the references it walks, up to that logarithm.
-- The structures are the standard library's AVL trees; a name is its
-- characters in lexicographic order, a CAN ID its key in
-- `Aletheia.DBC.Validator.SharedKeys`.
module Aletheia.DBC.Validator.Targets where

open import Data.Char using (Char)
open import Data.Char.Properties using () renaming (<-strictTotalOrder to <ᶜ-strictTotalOrder)
open import Data.List using (List; foldr; map)
open import Data.Maybe using (Maybe)
open import Data.Nat.Properties using () renaming (<-strictTotalOrder to <ⁿ-strictTotalOrder)
open import Function using (_∘_)
open import Relation.Binary.Bundles using (StrictTotalOrder)

import Data.List.Relation.Binary.Lex.Strict as Lex
import Data.Tree.AVL.Map as AVLMap
import Data.Tree.AVL.Sets as AVLSets
import Data.Tree.AVL.Sets.Membership as AVLSetMembership
import Data.Tree.AVL.Sets.Membership.Properties as AVLSetMembershipₚ

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.Data.Dec0 using (Dec₀; dec₀)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCMessage; Node; EnvironmentVar)
open import Aletheia.DBC.Validator.SharedKeys using (canIdKey)

nameOrder : StrictTotalOrder _ _ _
nameOrder = Lex.<-strictTotalOrder <ᶜ-strictTotalOrder

canIdOrder : StrictTotalOrder _ _ _
canIdOrder = Lex.<-strictTotalOrder <ⁿ-strictTotalOrder

private
  module Names = AVLSets nameOrder
  module Messages = AVLMap canIdOrder

open AVLSetMembership nameOrder public using (_∈_)

NameSet : Set
NameSet = Names.⟨Set⟩

-- Whether a set holds a name, with the evidence erased.
_∈?_ : (name : List Char) (names : NameSet) → Dec₀ (name ∈ names)
name ∈? names = dec₀ (Names.member name names) (AVLSetMembershipₚ.member-Reflects-∈ nameOrder)

noNames : NameSet
noNames = Names.empty

withName : List Char → NameSet → NameSet
withName = Names.insert

nodeNames : List Node → NameSet
nodeNames = Names.fromList ∘ map (Identifier.name ∘ Node.name)

envVarNames : List EnvironmentVar → NameSet
envVarNames = Names.fromList ∘ map (Identifier.name ∘ EnvironmentVar.name)

MessageIndex : Set
MessageIndex = Messages.Map DBCMessage

-- Each CAN ID's first message: the messages are inserted last to first,
-- and an insert replaces what the key held.
messageIndex : List DBCMessage → MessageIndex
messageIndex = foldr (λ m → Messages.insert (canIdKey (DBCMessage.id m)) m) Messages.empty

findMessage : CANId → MessageIndex → Maybe DBCMessage
findMessage cid index = Messages.lookup index (canIdKey cid)
