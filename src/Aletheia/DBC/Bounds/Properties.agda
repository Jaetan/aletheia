-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What the size-bound checker guarantees beyond its type, which already
-- says an accepted DBC meets every bound: a DBC within every bound is
-- accepted, as itself, and a refused one is outside some bound.  The same
-- for replacing a bounded DBC's node list.
module Aletheia.DBC.Bounds.Properties where

open import Data.Bool using (T; true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary using (¬_)

open import Aletheia.Data.Dec0 using (Dec₀; _because₀_; does₀)
open import Aletheia.DBC.Types using
  ( DBCSignal; SignalPresence; Always; When
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  )
open import Aletheia.DBC.Bounds using
  ( Checked; [_]; _>>=_; decide; bound; count; walk; every
  ; SelectorCount; SignalCounts; MessageCounts; LabelCount; AttributeCounts; DBCCounts
  ; ShortLabels; SignalTexts; ShortType; ShortValue; AttributeTexts; DBCTexts
  ; IsBoundedDBC; BoundedDBC; bounded; isBounded?; checkBounds; withNodes
  ; selectorCount; signalCounts; messageCounts; labelCount; attributeCounts; dbcCounts
  ; shortLabels; signalTexts; shortType; shortValue; attributeTexts; dbcTexts
  )
open import Aletheia.Limits using (ArrayCardinality; max-nodes-per-file)

-- ============================================================================
-- ACCEPTANCE, COMPOSITIONALLY
-- ============================================================================

Accepted : ∀ {P : Set} → Checked P → Set
Accepted (inj₁ _) = ⊥
Accepted (inj₂ _) = ⊤

decide-accepts : ∀ {P : Set} {e} {d : Dec₀ P} → T (does₀ d) → Accepted (decide e d)
decide-accepts {d = true because₀ _} _ = tt

bound-accepts : ∀ {kind tag n limit} → n ≤ limit → Accepted (bound kind tag n limit)
bound-accepts le = decide-accepts (≤⇒≤ᵇ le)

bind-accepts : ∀ {P Q : Set} {c : Checked P} {k : @0 P → Checked Q}
  → Accepted c → ((@0 p : P) → Accepted (k p)) → Accepted (c >>= k)
bind-accepts {c = inj₂ [ p ]} _ h = h p

walk-accepts : ∀ {A : Set} {P : A → Set} {xs : List A} {f : ∀ x → Checked (P x)}
  → (∀ x → P x → Accepted (f x))
  → ∀ {ys} → All P ys → (@0 k : All P ys → All P xs) → Accepted (walk f ys k)
walk-accepts h [] k = tt
walk-accepts {f = f} h {y ∷ _} (py ∷ pys) k with f y | h y py
... | inj₂ [ p ] | _ = walk-accepts h pys (λ ps → k (p ∷ ps))

every-accepts : ∀ {A : Set} {P : A → Set} {f : ∀ x → Checked (P x)}
  → (∀ x → P x → Accepted (f x)) → ∀ {xs} → All P xs → Accepted (every f xs)
every-accepts h ps = walk-accepts h ps (λ qs → qs)

-- ============================================================================
-- COUNTS
-- ============================================================================

selectorCount-accepts : ∀ p → SelectorCount p → Accepted (selectorCount p)
selectorCount-accepts Always      _  = tt
selectorCount-accepts (When _ _)  le = bound-accepts le

signalCounts-accepts : ∀ sig → SignalCounts sig → Accepted (signalCounts sig)
signalCounts-accepts sig c =
  bind-accepts (bound-accepts (SignalCounts.receivers c)) λ _ →
  bind-accepts (selectorCount-accepts (DBCSignal.presence sig) (SignalCounts.selector c)) λ _ → tt

messageCounts-accepts : ∀ msg → MessageCounts msg → Accepted (messageCounts msg)
messageCounts-accepts msg c =
  bind-accepts (bound-accepts (MessageCounts.signals c)) λ _ →
  bind-accepts (bound-accepts (MessageCounts.senders c)) λ _ →
  bind-accepts (every-accepts signalCounts-accepts (MessageCounts.eachSignal c)) λ _ → tt

labelCount-accepts : ∀ t → LabelCount t → Accepted (labelCount t)
labelCount-accepts (ATInt _ _)   _  = tt
labelCount-accepts (ATFloat _ _) _  = tt
labelCount-accepts ATString      _  = tt
labelCount-accepts (ATEnum _)    le = bound-accepts le
labelCount-accepts (ATHex _ _)   _  = tt

attributeCounts-accepts : ∀ a → AttributeCounts a → Accepted (attributeCounts a)
attributeCounts-accepts (DBCAttrDef d)     c = labelCount-accepts (AttrDef.attrType d) c
attributeCounts-accepts (DBCAttrDefault _) _ = tt
attributeCounts-accepts (DBCAttrAssign _)  _ = tt

dbcCounts-accepts : ∀ dbc → DBCCounts dbc → Accepted (dbcCounts dbc)
dbcCounts-accepts dbc c =
  bind-accepts (bound-accepts (DBCCounts.messages c)) λ _ →
  bind-accepts (every-accepts messageCounts-accepts (DBCCounts.eachMessage c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.attributes c)) λ _ →
  bind-accepts (every-accepts attributeCounts-accepts (DBCCounts.eachAttribute c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.comments c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.nodes c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.valueTables c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.valueDescriptions c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.signalGroups c)) λ _ →
  bind-accepts (every-accepts (λ _ → bound-accepts) (DBCCounts.eachSignalGroup c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.environmentVars c)) λ _ →
  bind-accepts (bound-accepts (DBCCounts.unresolvedValueDescs c)) λ _ → tt

-- ============================================================================
-- TEXTS
-- ============================================================================

shortLabels-accepts : ∀ tag vs → ShortLabels vs → Accepted (shortLabels tag vs)
shortLabels-accepts _ _ ps = every-accepts (λ _ → bound-accepts) ps

signalTexts-accepts : ∀ sig → SignalTexts sig → Accepted (signalTexts sig)
signalTexts-accepts sig t =
  bind-accepts (bound-accepts (SignalTexts.unit t)) λ _ →
  bind-accepts (shortLabels-accepts _ _ (SignalTexts.labels t)) λ _ → tt

shortType-accepts : ∀ t → ShortType t → Accepted (shortType t)
shortType-accepts (ATInt _ _)   _  = tt
shortType-accepts (ATFloat _ _) _  = tt
shortType-accepts ATString      _  = tt
shortType-accepts (ATEnum _)    ps = every-accepts (λ _ → bound-accepts) ps
shortType-accepts (ATHex _ _)   _  = tt

shortValue-accepts : ∀ v → ShortValue v → Accepted (shortValue v)
shortValue-accepts (AVInt _)    _  = tt
shortValue-accepts (AVFloat _)  _  = tt
shortValue-accepts (AVString _) le = bound-accepts le
shortValue-accepts (AVEnum _)   _  = tt
shortValue-accepts (AVHex _)    _  = tt

attributeTexts-accepts : ∀ a → AttributeTexts a → Accepted (attributeTexts a)
attributeTexts-accepts (DBCAttrDef d) (n , t) =
  bind-accepts (bound-accepts n) λ _ → bind-accepts (shortType-accepts (AttrDef.attrType d) t) λ _ → tt
attributeTexts-accepts (DBCAttrDefault d) (n , v) =
  bind-accepts (bound-accepts n) λ _ → bind-accepts (shortValue-accepts (AttrDefault.value d) v) λ _ → tt
attributeTexts-accepts (DBCAttrAssign a) (n , v) =
  bind-accepts (bound-accepts n) λ _ → bind-accepts (shortValue-accepts (AttrAssign.value a) v) λ _ → tt

dbcTexts-accepts : ∀ dbc → DBCTexts dbc → Accepted (dbcTexts dbc)
dbcTexts-accepts dbc t =
  bind-accepts (bound-accepts (DBCTexts.version t)) λ _ →
  bind-accepts (every-accepts (λ _ → every-accepts signalTexts-accepts) (DBCTexts.signals t)) λ _ →
  bind-accepts (every-accepts (λ _ → bound-accepts) (DBCTexts.comments t)) λ _ →
  bind-accepts (every-accepts attributeTexts-accepts (DBCTexts.attributes t)) λ _ →
  bind-accepts (every-accepts (λ _ → shortLabels-accepts _ _) (DBCTexts.valueTables t)) λ _ →
  bind-accepts (every-accepts (λ _ → shortLabels-accepts _ _) (DBCTexts.unresolvedValueDescs t)) λ _ → tt

-- ============================================================================
-- THE BOUNDED DBC
-- ============================================================================

isBounded?-accepts : ∀ dbc → IsBoundedDBC dbc → Accepted (isBounded? dbc)
isBounded?-accepts dbc p =
  bind-accepts (dbcCounts-accepts dbc (IsBoundedDBC.counts p)) λ _ →
  bind-accepts (dbcTexts-accepts dbc (IsBoundedDBC.texts p)) λ _ → tt

-- Completeness: a DBC within every bound is accepted, as itself.
checkBounds-accepts : ∀ dbc → IsBoundedDBC dbc
  → ∃[ b ] (checkBounds dbc ≡ inj₂ b × BoundedDBC.dbc b ≡ dbc)
checkBounds-accepts dbc p with isBounded? dbc | isBounded?-accepts dbc p
... | inj₂ [ q ] | _ = bounded dbc q , refl , refl

-- An accepted DBC is the one given.
checkBounds-dbc : ∀ dbc {b} → checkBounds dbc ≡ inj₂ b → BoundedDBC.dbc b ≡ dbc
checkBounds-dbc dbc eq with isBounded? dbc
checkBounds-dbc dbc refl | inj₂ [ _ ] = refl

-- A refused DBC is outside some bound.
checkBounds-refuses : ∀ dbc {e} → checkBounds dbc ≡ inj₁ e → ¬ IsBoundedDBC dbc
checkBounds-refuses dbc eq p with checkBounds-accepts dbc p
... | _ , eq′ , _ with trans (sym eq) eq′
...   | ()

-- ============================================================================
-- REPLACING THE NODE LIST
-- ============================================================================

withNodes-accepts : ∀ b ns → length ns ≤ max-nodes-per-file
  → ∃[ b′ ] (withNodes b ns ≡ inj₂ b′ × BoundedDBC.dbc b′ ≡ record (BoundedDBC.dbc b) { nodes = ns })
withNodes-accepts (bounded d p) ns le with count "nodes array" (length ns) max-nodes-per-file | bound-accepts {ArrayCardinality} {"nodes array"} le
... | inj₂ [ _ ] | _ = _ , refl , refl

withNodes-dbc : ∀ b ns {b′} → withNodes b ns ≡ inj₂ b′
  → BoundedDBC.dbc b′ ≡ record (BoundedDBC.dbc b) { nodes = ns }
withNodes-dbc (bounded d p) ns eq with count "nodes array" (length ns) max-nodes-per-file
withNodes-dbc (bounded d p) ns refl | inj₂ [ _ ] = refl

withNodes-refuses : ∀ b ns {e} → withNodes b ns ≡ inj₁ e → ¬ (length ns ≤ max-nodes-per-file)
withNodes-refuses b ns eq le with withNodes-accepts b ns le
... | _ , eq′ , _ with trans (sym eq) eq′
...   | ()
