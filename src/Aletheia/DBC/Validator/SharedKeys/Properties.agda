-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What an empty set of shared-key groups means for the messages.  No group
-- among the messages keyed by CAN ID: no two messages share a CAN ID.  None
-- among the messages keyed by name: no two share a name.  None among the
-- signal names: no two messages share a signal name.  Each holds both ways.
-- `Aletheia.Data.KeyConflicts.Properties` gives the property for the entries
-- (no two entries owned by different messages share a key); this module
-- carries it to the messages.
module Aletheia.DBC.Validator.SharedKeys.Properties where

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.Types using (DBCMessage; messageNameStr)
open import Aletheia.DBC.Validator.SharedKeys using
  ( Entry; entry; position; owner; key
  ; canIdKey; nameKey; messageSignalNames
  ; messageEntries; messageIdEntries; numbered; ownedSignalNames; signalEntries
  ; sharedKeyGroups )
open import Aletheia.DBC.Validity using (DistinctMessageNames; DisjointSignalNames)
import Aletheia.Data.KeyConflicts.Properties as KC

import Data.Char.Properties as Charₚ
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (map-injective)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsₚ
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (<⇒≢; n<1+n; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
import Data.String.Properties as Stringₚ
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

-- Two entries do not conflict: sharing a key, they share an owner.
NoConflict : Entry → Entry → Set
NoConflict = KC.NoConflict key owner position

map-≡[] : ∀ {A B : Set} (f : A → B) xs → map f xs ≡ [] → xs ≡ []
map-≡[] f []      _  = refl
map-≡[] f (_ ∷ _) ()

groups-sound : ∀ es → sharedKeyGroups es ≡ [] → AllPairs NoConflict es
groups-sound = KC.keyConflicts-sound key owner position

groups-complete : ∀ es → AllPairs NoConflict es → sharedKeyGroups es ≡ []
groups-complete = KC.keyConflicts-complete key owner position

-- ============================================================================
-- Keys name what they were made from
-- ============================================================================

canIdKey-injective : ∀ {c d : CANId} → canIdKey c ≡ canIdKey d → c ≡ d
canIdKey-injective {CANId.Standard _ _} {CANId.Standard _ _} refl = refl
canIdKey-injective {CANId.Extended _ _} {CANId.Extended _ _} refl = refl
canIdKey-injective {CANId.Standard _ _} {CANId.Extended _ _} ()
canIdKey-injective {CANId.Extended _ _} {CANId.Standard _ _} ()

nameKey-injective : ∀ {s t : String} → nameKey s ≡ nameKey t → s ≡ t
nameKey-injective {s} {t} eq =
  Stringₚ.toList-injective s t (map-injective (λ {c} {d} → Charₚ.toℕ-injective c d) eq)

-- ============================================================================
-- Messages as entries of their own
-- ============================================================================

module _ (k : DBCMessage → List ℕ) (l : DBCMessage → String) where
  private
    firstSound : ∀ {i j m} ms → i < j
      → All (NoConflict (entry i i (k m) m (l m))) (messageEntries k l j ms)
      → All (λ m′ → k m ≢ k m′) ms
    firstSound []        _   []         = []
    firstSound (m′ ∷ ms) i<j (nc ∷ ncs) =
      (λ eq → <⇒≢ i<j (nc eq)) ∷ firstSound ms (m<n⇒m<1+n i<j) ncs

    firstComplete : ∀ {i j m} ms → All (λ m′ → k m ≢ k m′) ms
      → All (NoConflict (entry i i (k m) m (l m))) (messageEntries k l j ms)
    firstComplete []        []           = []
    firstComplete (m′ ∷ ms) (neq ∷ neqs) = (λ eq → ⊥-elim (neq eq)) ∷ firstComplete ms neqs

  messageEntries-sound : ∀ i ms → AllPairs NoConflict (messageEntries k l i ms)
    → AllPairs (λ m₁ m₂ → k m₁ ≢ k m₂) ms
  messageEntries-sound i []       []         = []
  messageEntries-sound i (m ∷ ms) (nc ∷ ncs) =
    firstSound ms (n<1+n i) nc ∷ messageEntries-sound (suc i) ms ncs

  messageEntries-complete : ∀ i ms → AllPairs (λ m₁ m₂ → k m₁ ≢ k m₂) ms
    → AllPairs NoConflict (messageEntries k l i ms)
  messageEntries-complete i []       []           = []
  messageEntries-complete i (m ∷ ms) (neq ∷ neqs) =
    firstComplete ms neq ∷ messageEntries-complete (suc i) ms neqs

idsDistinct-sound : ∀ msgs → sharedKeyGroups (messageIdEntries msgs) ≡ []
  → AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
idsDistinct-sound msgs eq =
  AllPairs.map (λ kneq ideq → kneq (cong canIdKey ideq))
    (messageEntries-sound (canIdKey ∘ DBCMessage.id) (λ _ → "") 0 msgs
      (groups-sound (messageIdEntries msgs) eq))

idsDistinct-complete : ∀ msgs
  → AllPairs (λ m₁ m₂ → DBCMessage.id m₁ ≢ DBCMessage.id m₂) msgs
  → sharedKeyGroups (messageIdEntries msgs) ≡ []
idsDistinct-complete msgs ap =
  groups-complete (messageIdEntries msgs)
    (messageEntries-complete (canIdKey ∘ DBCMessage.id) (λ _ → "") 0 msgs
      (AllPairs.map (λ ineq keq → ineq (canIdKey-injective keq)) ap))

namesDistinct-sound : ∀ msgs
  → sharedKeyGroups (messageEntries (nameKey ∘ messageNameStr) messageNameStr 0 msgs) ≡ []
  → AllPairs DistinctMessageNames msgs
namesDistinct-sound msgs eq =
  AllPairs.map (λ kneq neq → kneq (cong nameKey neq))
    (messageEntries-sound (nameKey ∘ messageNameStr) messageNameStr 0 msgs (groups-sound _ eq))

namesDistinct-complete : ∀ msgs → AllPairs DistinctMessageNames msgs
  → sharedKeyGroups (messageEntries (nameKey ∘ messageNameStr) messageNameStr 0 msgs) ≡ []
namesDistinct-complete msgs ap =
  groups-complete _
    (messageEntries-complete (nameKey ∘ messageNameStr) messageNameStr 0 msgs
      (AllPairs.map (λ sneq keq → sneq (nameKey-injective keq)) ap))

-- ============================================================================
-- Signal names as entries owned by their message
-- ============================================================================

-- Two owned names: sharing a name, they share an owner.
SameOwner : ℕ × DBCMessage × String → ℕ × DBCMessage × String → Set
SameOwner (o₁ , _ , n₁) (o₂ , _ , n₂) = nameKey n₁ ≡ nameKey n₂ → o₁ ≡ o₂

-- No two messages share a signal name.
DisjointNames : DBCMessage → DBCMessage → Set
DisjointNames m₁ m₂ = DisjointSignalNames (messageSignalNames m₁) (messageSignalNames m₂)

private
  numbered-sound : ∀ i xs → AllPairs NoConflict (numbered i xs) → AllPairs SameOwner xs
  numbered-sound i []                []         = []
  numbered-sound i ((o , m , n) ∷ xs) (nc ∷ ncs) = go (suc i) xs nc ∷ numbered-sound (suc i) xs ncs
    where
      go : ∀ j ys → All (NoConflict (entry i o (nameKey n) m n)) (numbered j ys)
           → All (SameOwner (o , m , n)) ys
      go j []                   []       = []
      go j ((_ , _ , _) ∷ ys)   (p ∷ ps) = p ∷ go (suc j) ys ps

  numbered-complete : ∀ i xs → AllPairs SameOwner xs → AllPairs NoConflict (numbered i xs)
  numbered-complete i []                 []       = []
  numbered-complete i ((o , m , n) ∷ xs) (p ∷ ps) = go (suc i) xs p ∷ numbered-complete (suc i) xs ps
    where
      go : ∀ j ys → All (SameOwner (o , m , n)) ys
           → All (NoConflict (entry i o (nameKey n) m n)) (numbered j ys)
      go j []                 []       = []
      go j ((_ , _ , _) ∷ ys) (q ∷ qs) = q ∷ go (suc j) ys qs

  AllPairs-++⁻ : ∀ {A : Set} {R : A → A → Set} xs {ys} → AllPairs R (xs ++ₗ ys)
    → AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  AllPairs-++⁻ []       p          = [] , p , []
  AllPairs-++⁻ (x ∷ xs) (px ∷ pxs) with AllPairs-++⁻ xs pxs | Allₚ.++⁻ xs px
  ... | a , b , c | pxs′ , pys = (pxs′ ∷ a) , b , (pys ∷ c)

  transpose : ∀ {A B : Set} {P : A → B → Set} (xs : List A) (ys : List B)
    → All (λ a → All (P a) ys) xs → All (λ b → All (λ a → P a b) xs) ys
  transpose xs []       _ = []
  transpose xs (y ∷ ys) p =
    All.map (λ { (h ∷ _) → h }) p ∷ transpose xs ys (All.map (λ { (_ ∷ t) → t }) p)

  -- One message's names, all owned by it, never disagree on an owner.
  block-pairs : ∀ i m (ns : List String) → AllPairs SameOwner (map (λ n → i , m , n) ns)
  block-pairs i m []       = []
  block-pairs i m (n ∷ ns) = same ns ∷ block-pairs i m ns
    where
      same : ∀ ns′ → All (SameOwner (i , m , n)) (map (λ n′ → i , m , n′) ns′)
      same []        = []
      same (_ ∷ ns′) = (λ _ → refl) ∷ same ns′

  notShared : ∀ {i j : ℕ} {n : String} (ns : List String) → i ≢ j
    → All (λ n′ → nameKey n ≡ nameKey n′ → i ≡ j) ns → ¬ Any (n ≡_) ns
  notShared (_ ∷ ns) i≢j (p ∷ _)  (here eq) = i≢j (p (cong nameKey eq))
  notShared (_ ∷ ns) i≢j (_ ∷ ps) (there a) = notShared ns i≢j ps a

  shareNone : ∀ {i j : ℕ} {n : String} (ns : List String) → ¬ Any (n ≡_) ns
    → All (λ n′ → nameKey n ≡ nameKey n′ → i ≡ j) ns
  shareNone []       _    = []
  shareNone (_ ∷ ns) ¬any = (λ keq → ⊥-elim (¬any (here (nameKey-injective keq)))) ∷ shareNone ns (¬any ∘ there)

  -- A name owned by message `i`, sharing its owner with every name after it,
  -- is a name of no later message.
  crossSound : ∀ {i : ℕ} {m : DBCMessage} {n : String} j ms → i < j → All (SameOwner (i , m , n)) (ownedSignalNames j ms)
    → All (λ m′ → ¬ Any (n ≡_) (messageSignalNames m′)) ms
  crossSound j []        _   _  = []
  crossSound {i} {m} {n} j (m′ ∷ ms) i<j ps
    with Allₚ.++⁻ (map (λ n′ → j , m′ , n′) (messageSignalNames m′)) ps
  ... | pb , pr = notShared (messageSignalNames m′) (<⇒≢ i<j) (Allₚ.map⁻ pb)
                  ∷ crossSound {i} {m} {n} (suc j) ms (m<n⇒m<1+n i<j) pr

  crossComplete : ∀ {i : ℕ} {m : DBCMessage} {n : String} j ms → All (λ m′ → ¬ Any (n ≡_) (messageSignalNames m′)) ms
    → All (SameOwner (i , m , n)) (ownedSignalNames j ms)
  crossComplete j []        []         = []
  crossComplete {i} {m} {n} j (m′ ∷ ms) (¬a ∷ ¬as) =
    Allₚ.++⁺ (Allₚ.map⁺ (shareNone (messageSignalNames m′) ¬a)) (crossComplete {i} {m} {n} (suc j) ms ¬as)

  ownedSignalNames-sound : ∀ i ms → AllPairs SameOwner (ownedSignalNames i ms) → AllPairs DisjointNames ms
  ownedSignalNames-sound i []       _ = []
  ownedSignalNames-sound i (m ∷ ms) p with AllPairs-++⁻ (map (λ n → i , m , n) (messageSignalNames m)) p
  ... | _ , rest , cross =
    transpose (messageSignalNames m) ms
      (All.map (λ {n} → crossSound {i} {m} {n} (suc i) ms (n<1+n i)) (Allₚ.map⁻ cross))
    ∷ ownedSignalNames-sound (suc i) ms rest

  ownedSignalNames-complete : ∀ i ms → AllPairs DisjointNames ms → AllPairs SameOwner (ownedSignalNames i ms)
  ownedSignalNames-complete i []       []       = []
  ownedSignalNames-complete i (m ∷ ms) (d ∷ ds) =
    AllPairsₚ.++⁺ (block-pairs i m (messageSignalNames m)) (ownedSignalNames-complete (suc i) ms ds)
      (Allₚ.map⁺ (All.map (λ {n} → crossComplete {i} {m} {n} (suc i) ms)
                          (transpose ms (messageSignalNames m) d)))

signalNamesDisjoint-sound : ∀ msgs → sharedKeyGroups (signalEntries msgs) ≡ []
  → AllPairs DisjointNames msgs
signalNamesDisjoint-sound msgs eq =
  ownedSignalNames-sound 0 msgs
    (numbered-sound 0 (ownedSignalNames 0 msgs) (groups-sound (signalEntries msgs) eq))

signalNamesDisjoint-complete : ∀ msgs → AllPairs DisjointNames msgs
  → sharedKeyGroups (signalEntries msgs) ≡ []
signalNamesDisjoint-complete msgs d =
  groups-complete (signalEntries msgs)
    (numbered-complete 0 (ownedSignalNames 0 msgs) (ownedSignalNames-complete 0 msgs d))
