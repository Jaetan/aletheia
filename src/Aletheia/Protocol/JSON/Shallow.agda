-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A JSON value within a depth (`Shallow`) has its `jsonDepth` at most that
-- depth, and is within every deeper one; the lemmas a formatter's depth
-- proof is built from.  Every definition is erased, so a runtime module can
-- carry a depth proof beside the JSON it formats and MAlonzo compiles none
-- of it.
module Aletheia.Protocol.JSON.Shallow where

open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step; _⊔′_; z≤n; s≤s)
open import Data.Nat.Properties using (⊔-lub; ⊔≡⊔′; ≤⇒≤′)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst)

open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject; jsonDepth; listDepth; fieldsDepth; Shallow; ListShallow; FieldsShallow)

-- A value within a depth is within the next.
mutual
  @0 shallow-suc : ∀ k j → Shallow k j → Shallow (suc k) j
  shallow-suc _       JNull        _ = tt
  shallow-suc _       (JBool _)    _ = tt
  shallow-suc _       (JNumber _)  _ = tt
  shallow-suc _       (JString _)  _ = tt
  shallow-suc zero    (JArray _)   ()
  shallow-suc (suc k) (JArray xs)  s = list-shallow-suc k xs s
  shallow-suc zero    (JObject _)  ()
  shallow-suc (suc k) (JObject fs) s = fields-shallow-suc k fs s

  @0 list-shallow-suc : ∀ k xs → ListShallow k xs → ListShallow (suc k) xs
  list-shallow-suc k []       _        = tt
  list-shallow-suc k (x ∷ xs) (s , ss) = shallow-suc k x s , list-shallow-suc k xs ss

  @0 fields-shallow-suc : ∀ k fs → FieldsShallow k fs → FieldsShallow (suc k) fs
  fields-shallow-suc k []        _        = tt
  fields-shallow-suc k (kv ∷ fs) (s , ss) = shallow-suc k (proj₂ kv) s , fields-shallow-suc k fs ss

-- A value within a depth is within every deeper one.
@0 shallow-≤ : ∀ {k k′} j → k ≤ k′ → Shallow k j → Shallow k′ j
shallow-≤ j le = go (≤⇒≤′ le)
  where
    go : ∀ {k k′} → k ≤′ k′ → Shallow k j → Shallow k′ j
    go ≤′-refl       s = s
    go (≤′-step le′) s = shallow-suc _ j (go le′ s)

private
  @0 ⊔′-lub : ∀ {m n k} → m ≤ k → n ≤ k → m ⊔′ n ≤ k
  ⊔′-lub {m} {n} {k} p q = subst (_≤ k) (⊔≡⊔′ m n) (⊔-lub p q)

-- What `Shallow` claims, `jsonDepth` measures.
mutual
  @0 shallow-depth : ∀ k j → Shallow k j → jsonDepth j ≤ k
  shallow-depth _       JNull        _ = z≤n
  shallow-depth _       (JBool _)    _ = z≤n
  shallow-depth _       (JNumber _)  _ = z≤n
  shallow-depth _       (JString _)  _ = z≤n
  shallow-depth zero    (JArray _)   ()
  shallow-depth (suc k) (JArray xs)  s = s≤s (list-shallow-depth k xs s)
  shallow-depth zero    (JObject _)  ()
  shallow-depth (suc k) (JObject fs) s = s≤s (fields-shallow-depth k fs s)

  @0 list-shallow-depth : ∀ k xs → ListShallow k xs → listDepth xs ≤ k
  list-shallow-depth k []       _        = z≤n
  list-shallow-depth k (x ∷ xs) (s , ss) = ⊔′-lub (shallow-depth k x s) (list-shallow-depth k xs ss)

  @0 fields-shallow-depth : ∀ k fs → FieldsShallow k fs → fieldsDepth fs ≤ k
  fields-shallow-depth k []        _        = z≤n
  fields-shallow-depth k (kv ∷ fs) (s , ss) = ⊔′-lub (shallow-depth k (proj₂ kv) s) (fields-shallow-depth k fs ss)

-- A list a formatter maps out, each value within a depth.
@0 map-shallow : ∀ {A : Set} {k} (f : A → JSON) → (∀ a → Shallow k (f a)) → ∀ as → ListShallow k (map f as)
map-shallow f s []       = tt
map-shallow f s (a ∷ as) = s a , map-shallow f s as

-- Two lists of fields, one after the other.
@0 fields-++ : ∀ {k} fs gs → FieldsShallow k fs → FieldsShallow k gs → FieldsShallow k (fs ++ₗ gs)
fields-++ []        gs _        t = t
fields-++ (kv ∷ fs) gs (s , ss) t = s , fields-++ fs gs ss t
