{-# OPTIONS --safe --without-K #-}

-- Common imports and utilities used throughout the Aletheia codebase.
--
-- Purpose: Centralize frequently-used standard library imports to reduce boilerplate.
-- Exports: Core types (Bool, Nat, List, Maybe, String), basic operations, proofs.
-- Role: Foundation module imported by most other Aletheia modules.
module Aletheia.Prelude where

-- Basic types
open import Data.Bool public
  using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Unit public
  using (tt)

open import Data.Nat public
  using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _≡ᵇ_)
  -- Note: _≤ᵇ_ not exported to avoid clash with Data.Rational._≤ᵇ_

open import Data.List public
  using (List; []; _∷_; length; map; filter; foldr)

open import Data.Maybe public
  using (Maybe; just; nothing; maybe)

open import Data.String public
  using (String)
  renaming (_++_ to _++ₛ_)

-- Import string equality for utility functions
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)

open import Data.Product public
  using (_×_; _,_; proj₁; proj₂)

open import Data.Sum public
  using (_⊎_; inj₁; inj₂)
  renaming (map₁ to mapₑ)

-- Rationals (common in signal processing)
open import Data.Rational public
  using (ℚ; mkℚ)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)

open import Data.Integer public
  using (ℤ; +_; -[1+_])

-- Equality and decidability
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; cong; sym; trans)

open import Relation.Nullary public
  using (Dec; yes; no; ¬_)

open import Relation.Nullary.Decidable public
  using (⌊_⌋)

-- Function combinators
open import Function public
  using (_∘_; _$_; id; const)

-- COMMON UTILITY FUNCTIONS
-- ============================================================================

-- Find first element in list matching a Bool predicate (stdlib re-export).
open import Data.List.Base public using () renaming (findᵇ to findByPredicate)

-- Look up value by string key in association list.
--
-- Deferred Bool fast path (AA-16.8): the `⌊ _≟ₛ_ ⌋` allocates a Dec heap
-- cell per comparison. Unlike DBCHelpers.findSignalInList (AA-16.2) and
-- Cache.lookupEntries (AA-16.3), this lookup is *not* on the streaming hot
-- path — its sole runtime callers are JSON parsing helpers
-- (Protocol/JSON/Lookup.agda for command field extraction) which run once
-- per JSON command, not per frame. The same `primStringEquality` blocker
-- as AA-16.2 applies (stdlib `_==_` wraps `isYes (_≟_)` so gives no real
-- speedup; the Haskell builtin requires a postulate to bridge into a
-- propositional-equality form). Since the cold-path traffic is per-command
-- not per-frame, the marginal Dec allocation is dominated by JSON parsing
-- itself; left as-is unless `lookupByKey` is later promoted to a hot-path
-- caller, at which point apply the same fix as DBCHelpers/Cache once the
-- string-equality infrastructure is decided.
lookupByKey : ∀ {A : Set} → String → List (String × A) → Maybe A
lookupByKey key [] = nothing
lookupByKey key ((k , v) ∷ rest) =
  if ⌊ k ≟ₛ key ⌋ then just v else lookupByKey key rest

-- List indexing: O(n) lookup by position
listIndex : ∀ {A : Set} → ℕ → List A → Maybe A
listIndex _ [] = nothing
listIndex zero (x ∷ _) = just x
listIndex (suc n) (_ ∷ xs) = listIndex n xs

-- Lift Maybe to E ⊎ A with an error value on Nothing
require : ∀ {E A : Set} → E → Maybe A → E ⊎ A
require err = maybe inj₂ (inj₁ err)

-- Bind operator for Either (⊎) monad (used by parsers and command routing)
_>>=ₑ_ : ∀ {E A B : Set} → E ⊎ A → (A → E ⊎ B) → E ⊎ B
inj₁ err >>=ₑ _ = inj₁ err
inj₂ x >>=ₑ f = f x

-- CAN domain constants re-exported for convenience.
-- Canonical definitions live in Aletheia.CAN.Constants.
open import Aletheia.CAN.Constants public
  using (standard-can-id-max; extended-can-id-max; max-physical-bits; 8≤max-physical-bits)

-- Boolean conditional that provides a T proof in the true branch.
-- Unlike if_then_else_, this passes the T b witness to the true branch,
-- enabling construction of types that embed T (n <ᵇ max).
-- Defined as a regular function (no with), so rewrite works in proofs.
ifᵀ_then_else_ : ∀ {A : Set} (b : Bool) → (T b → A) → A → A
ifᵀ true  then f else _ = f tt
ifᵀ false then _ else x = x

-- T b has at most one inhabitant: T true = ⊤ (unique by η), T false = ⊥ (empty).
-- Essential for decidable equality and roundtrip proofs on bounded types.
open import Data.Bool.Properties public using (T-irrelevant)

-- Convert T b witness to propositional equality b ≡ true.
T→true : ∀ {b : Bool} → T b → b ≡ true
T→true {true} _ = refl

-- Given a T b witness, ifᵀ selects the true branch applied to pf.
-- Splits on b internally; avoids with-abstraction at call sites where
-- the type of `Standard rawId pf` creates a rigid dependency on b.
-- Uses η for ⊤: when b = true, pf : T true = ⊤ is definitionally tt.
ifᵀ-witness : ∀ {A : Set} {b : Bool} (f : T b → A) (e : A) (pf : T b)
  → ifᵀ b then f else e ≡ f pf
ifᵀ-witness {b = true}  f e pf = refl
ifᵀ-witness {b = false} _ _ ()

-- Convert ℕ to ℚ using mkℚ directly (bypasses GCD normalization in _/_).
-- This allows toℚᵘ to reduce by definition: toℚᵘ (mkℚ (+ n) 0 _) = mkℚᵘ (+ n) 0
-- Critical for roundtrip proofs of metric operators and DBC formatter.
ℕtoℚ : ℕ → ℚ
ℕtoℚ n = mkℚ (+ n) 0 (coprime-sym (1-coprimeTo n))

-- Convert ℤ to ℚ — re-exported from stdlib as Prelude-visible name.
-- Same construction as `ℕtoℚ` (mkℚ with denominator-1 = 0), so toℚᵘ still
-- reduces by definition for roundtrip proofs.
open import Data.Rational.Literals public using (fromℤ)

