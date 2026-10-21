-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What the bounds checker guarantees beyond its type, which already says
-- an accepted DBC meets every bound: a DBC within every bound is accepted,
-- as itself, and a refused one is outside some bound.  The same for
-- replacing a bounded DBC's node list.
module Aletheia.DBC.Bounds.Properties where

open import Data.Bool using (Bool; T; true)
open import Data.Bool.Properties using (T-≡)
open import Data.Char using (Char)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary using (¬_)

open import Aletheia.Data.Dec0 using (Dec₀; _because₀_; does₀)
open import Aletheia.DBC.Identifier using (firstFailing)
open import Aletheia.DBC.Types using
  ( DBCSignal; SignalPresence; Always; When; DBCAttribute; DBCAttrDef
  ; DBCAttrDefault; DBCAttrAssign; AttrDef; AttrDefault; AttrAssign; AttrType
  ; ATInt; ATFloat; ATString; ATEnum; ATHex; AttrValue; AVInt; AVFloat
  ; AVString; AVEnum; AVHex )
open import Aletheia.DBC.Bounds using
  ( Checked; [_]; _>>=_; decide; bound; walk; every; SelectorCount
  ; SignalCounts; MessageCounts; LabelCount; AttributeCounts; DBCCounts
  ; CharsOK; chars; charsAt; TextOK; text; LabelsOK; labels; SignalTexts
  ; TypeOK; ValueOK; AttributeTexts; DBCTexts; IsBoundedDBC; BoundedDBC
  ; bounded; isBounded?; checkBounds; NodesOK; nodesOK; withNodes
  ; selectorCount; signalCounts; messageCounts; labelCount; attributeCounts
  ; dbcCounts; signalTexts; typeOK; valueOK; attributeTexts; dbcTexts
  ; SmallSelectors; SignalMagnitudes; EnvVarMagnitudes; SmallType; SmallValue
  ; AttributeMagnitudes; DBCMagnitudes; smallSelectors; signalMagnitudes
  ; envVarMagnitudes; smallType; smallValue; attributeMagnitudes
  ; dbcMagnitudes )

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
-- CHARACTERS AND TEXTS
-- ============================================================================

-- A list whose every character satisfies `p` has no failing character.
firstFailing-nothing : ∀ (p : Char → Bool) {cs} → CharsOK p cs → ∀ i → firstFailing p i cs ≡ nothing
firstFailing-nothing p []        _ = refl
firstFailing-nothing p (pc ∷ ps) i rewrite Equivalence.to T-≡ pc = firstFailing-nothing p ps (suc i)

charsAt-accepts : ∀ p tag cs r (eq : firstFailing p 0 cs ≡ r) → r ≡ nothing → Accepted (charsAt p tag cs r eq)
charsAt-accepts p tag cs nothing  _ _ = tt
charsAt-accepts p tag cs (just _) _ ()

chars-accepts : ∀ p tag {cs} → CharsOK p cs → Accepted (chars p tag cs)
chars-accepts p tag {cs} ps = charsAt-accepts p tag cs _ refl (firstFailing-nothing p ps 0)

text-accepts : ∀ tag {cs} → TextOK cs → Accepted (text tag cs)
text-accepts tag (s , a) =
  bind-accepts (bound-accepts s) λ _ → bind-accepts (chars-accepts _ tag a) λ _ → tt

labels-accepts : ∀ tag {vs} → LabelsOK vs → Accepted (labels tag vs)
labels-accepts tag ps = every-accepts (λ _ → text-accepts tag) ps

signalTexts-accepts : ∀ sig → SignalTexts sig → Accepted (signalTexts sig)
signalTexts-accepts sig t =
  bind-accepts (text-accepts _ (SignalTexts.unit t)) λ _ →
  bind-accepts (labels-accepts _ (SignalTexts.labels t)) λ _ → tt

typeOK-accepts : ∀ t → TypeOK t → Accepted (typeOK t)
typeOK-accepts (ATInt _ _)   _  = tt
typeOK-accepts (ATFloat _ _) _  = tt
typeOK-accepts ATString      _  = tt
typeOK-accepts (ATEnum _)    ps = every-accepts (λ _ → text-accepts _) ps
typeOK-accepts (ATHex _ _)   _  = tt

valueOK-accepts : ∀ v → ValueOK v → Accepted (valueOK v)
valueOK-accepts (AVInt _)    _ = tt
valueOK-accepts (AVFloat _)  _ = tt
valueOK-accepts (AVString _) t = text-accepts _ t
valueOK-accepts (AVEnum _)   _ = tt
valueOK-accepts (AVHex _)    _ = tt

attributeTexts-accepts : ∀ a → AttributeTexts a → Accepted (attributeTexts a)
attributeTexts-accepts (DBCAttrDef d)     t = typeOK-accepts (AttrDef.attrType d) t
attributeTexts-accepts (DBCAttrDefault d) v = valueOK-accepts (AttrDefault.value d) v
attributeTexts-accepts (DBCAttrAssign a)  v = valueOK-accepts (AttrAssign.value a) v

dbcTexts-accepts : ∀ dbc → DBCTexts dbc → Accepted (dbcTexts dbc)
dbcTexts-accepts dbc t =
  bind-accepts (text-accepts _ (DBCTexts.version t)) λ _ →
  bind-accepts (every-accepts (λ _ → every-accepts signalTexts-accepts) (DBCTexts.signals t)) λ _ →
  bind-accepts (every-accepts (λ _ → text-accepts _) (DBCTexts.comments t)) λ _ →
  bind-accepts (every-accepts attributeTexts-accepts (DBCTexts.attributes t)) λ _ →
  bind-accepts (every-accepts (λ _ → labels-accepts _) (DBCTexts.valueTables t)) λ _ →
  bind-accepts (every-accepts (λ _ → labels-accepts _) (DBCTexts.unresolvedValueDescs t)) λ _ → tt

-- ============================================================================
-- THE BOUNDED DBC
-- ============================================================================

smallSelectors-accepts : ∀ p → SmallSelectors p → Accepted (smallSelectors p)
smallSelectors-accepts Always      _ = tt
smallSelectors-accepts (When _ _)  s = every-accepts (λ _ → bound-accepts) s

signalMagnitudes-accepts : ∀ sig → SignalMagnitudes sig → Accepted (signalMagnitudes sig)
signalMagnitudes-accepts sig m =
  bind-accepts (bound-accepts (SignalMagnitudes.factor m)) λ _ →
  bind-accepts (bound-accepts (SignalMagnitudes.offset m)) λ _ →
  bind-accepts (bound-accepts (SignalMagnitudes.minimum m)) λ _ →
  bind-accepts (bound-accepts (SignalMagnitudes.maximum m)) λ _ →
  bind-accepts (bound-accepts (SignalMagnitudes.startBit m)) λ _ →
  bind-accepts (bound-accepts (SignalMagnitudes.bitLength m)) λ _ →
  bind-accepts (smallSelectors-accepts (DBCSignal.presence sig) (SignalMagnitudes.selectors m)) λ _ →
  bind-accepts (every-accepts (λ _ → bound-accepts) (SignalMagnitudes.keys m)) λ _ → tt

envVarMagnitudes-accepts : ∀ e → EnvVarMagnitudes e → Accepted (envVarMagnitudes e)
envVarMagnitudes-accepts e m =
  bind-accepts (bound-accepts (EnvVarMagnitudes.initial m)) λ _ →
  bind-accepts (bound-accepts (EnvVarMagnitudes.minimum m)) λ _ →
  bind-accepts (bound-accepts (EnvVarMagnitudes.maximum m)) λ _ → tt

smallType-accepts : ∀ t → SmallType t → Accepted (smallType t)
smallType-accepts (ATInt _ _)   (l , h) = bind-accepts (bound-accepts l) λ _ → bind-accepts (bound-accepts h) λ _ → tt
smallType-accepts (ATFloat _ _) (l , h) = bind-accepts (bound-accepts l) λ _ → bind-accepts (bound-accepts h) λ _ → tt
smallType-accepts ATString      _       = tt
smallType-accepts (ATEnum _)    _       = tt
smallType-accepts (ATHex _ _)   (l , h) = bind-accepts (bound-accepts l) λ _ → bind-accepts (bound-accepts h) λ _ → tt

smallValue-accepts : ∀ v → SmallValue v → Accepted (smallValue v)
smallValue-accepts (AVInt _)    s = bound-accepts s
smallValue-accepts (AVFloat _)  s = bound-accepts s
smallValue-accepts (AVString _) _ = tt
smallValue-accepts (AVEnum _)   s = bound-accepts s
smallValue-accepts (AVHex _)    s = bound-accepts s

attributeMagnitudes-accepts : ∀ a → AttributeMagnitudes a → Accepted (attributeMagnitudes a)
attributeMagnitudes-accepts (DBCAttrDef d)     m = smallType-accepts (AttrDef.attrType d) m
attributeMagnitudes-accepts (DBCAttrDefault d) m = smallValue-accepts (AttrDefault.value d) m
attributeMagnitudes-accepts (DBCAttrAssign a)  m = smallValue-accepts (AttrAssign.value a) m

dbcMagnitudes-accepts : ∀ dbc → DBCMagnitudes dbc → Accepted (dbcMagnitudes dbc)
dbcMagnitudes-accepts dbc m =
  bind-accepts (every-accepts (λ _ → every-accepts signalMagnitudes-accepts) (DBCMagnitudes.signals m)) λ _ →
  bind-accepts (every-accepts envVarMagnitudes-accepts (DBCMagnitudes.environmentVars m)) λ _ →
  bind-accepts (every-accepts attributeMagnitudes-accepts (DBCMagnitudes.attributes m)) λ _ →
  bind-accepts (every-accepts (λ _ → every-accepts (λ _ → bound-accepts)) (DBCMagnitudes.valueTables m)) λ _ →
  bind-accepts (every-accepts (λ _ → every-accepts (λ _ → bound-accepts)) (DBCMagnitudes.unresolvedValueDescs m)) λ _ → tt

isBounded?-accepts : ∀ dbc → IsBoundedDBC dbc → Accepted (isBounded? dbc)
isBounded?-accepts dbc p =
  bind-accepts (dbcCounts-accepts dbc (IsBoundedDBC.counts p)) λ _ →
  bind-accepts (dbcTexts-accepts dbc (IsBoundedDBC.texts p)) λ _ →
  bind-accepts (dbcMagnitudes-accepts dbc (IsBoundedDBC.magnitudes p)) λ _ → tt

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

nodesOK-accepts : ∀ ns → NodesOK ns → Accepted (nodesOK ns)
nodesOK-accepts ns le = bound-accepts le

withNodes-accepts : ∀ b ns → NodesOK ns
  → ∃[ b′ ] (withNodes b ns ≡ inj₂ b′ × BoundedDBC.dbc b′ ≡ record (BoundedDBC.dbc b) { nodes = ns })
withNodes-accepts (bounded d p) ns ok with nodesOK ns | nodesOK-accepts ns ok
... | inj₂ [ _ ] | _  = _ , refl , refl
... | inj₁ _     | ()

withNodes-dbc : ∀ b ns {b′} → withNodes b ns ≡ inj₂ b′
  → BoundedDBC.dbc b′ ≡ record (BoundedDBC.dbc b) { nodes = ns }
withNodes-dbc (bounded d p) ns eq with nodesOK ns
withNodes-dbc (bounded d p) ns refl | inj₂ [ _ ] = refl

withNodes-refuses : ∀ b ns {e} → withNodes b ns ≡ inj₁ e → ¬ NodesOK ns
withNodes-refuses b ns eq ok with withNodes-accepts b ns ok
... | _ , eq′ , _ with trans (sym eq) eq′
...   | ()
