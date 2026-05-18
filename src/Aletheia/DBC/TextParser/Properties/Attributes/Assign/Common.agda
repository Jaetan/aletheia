{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.3 — shared helpers for the per-target
-- `parseRawAttrAssign` / `parseRawAttrRel` roundtrip proofs.
--
-- The 21-case dispatcher (5 standard targets × 3 emit shapes + 2 rel
-- targets × 3 emit shapes) shares head-classify witnesses and the
-- value-shape `SuffixStops isHSpace` precondition closure.  Per-target
-- specifics (Trace modules, after-keyword bind chains, target-eq
-- witnesses) live in the per-target sub-files
-- (`Assign/{Network,Node,Message,Signal,EnvVar,Rel}.agda`).

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.Integer using (+_; -[1+_])
open import Data.List using (List; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.TextFormatter.Emitter
  using (showDecRat-dec-chars; showInt-chars; showℕ-dec-chars; digitChar)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( SuffixStops; ∷-stop
  ; showNat-chars-head
  ; showDecRat-chars-head-dash; showDecRat-chars-head-digit)

-- ============================================================================
-- digitChar lemmas (re-derived from Default.agda's privately-scoped
-- versions; these are shared across all targets).
-- ============================================================================

digitChar-not-quote : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ '"') ≡ false
digitChar-not-quote 0 _ = refl
digitChar-not-quote 1 _ = refl
digitChar-not-quote 2 _ = refl
digitChar-not-quote 3 _ = refl
digitChar-not-quote 4 _ = refl
digitChar-not-quote 5 _ = refl
digitChar-not-quote 6 _ = refl
digitChar-not-quote 7 _ = refl
digitChar-not-quote 8 _ = refl
digitChar-not-quote 9 _ = refl
digitChar-not-quote (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
digitChar-not-isHSpace 0 = refl
digitChar-not-isHSpace 1 = refl
digitChar-not-isHSpace 2 = refl
digitChar-not-isHSpace 3 = refl
digitChar-not-isHSpace 4 = refl
digitChar-not-isHSpace 5 = refl
digitChar-not-isHSpace 6 = refl
digitChar-not-isHSpace 7 = refl
digitChar-not-isHSpace 8 = refl
digitChar-not-isHSpace 9 = refl
digitChar-not-isHSpace (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

-- B.3.d 3d.5.d 3c-B Path 1: keyword-first-char inequalities used by
-- ATgtNetwork dispatchers' head-class witness construction.  Each of
-- 'B', 'S', 'E' has codepoint distinct from any digitChar d (d < 10).
digitChar-not-B : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ 'B') ≡ false
digitChar-not-B 0 _ = refl
digitChar-not-B 1 _ = refl
digitChar-not-B 2 _ = refl
digitChar-not-B 3 _ = refl
digitChar-not-B 4 _ = refl
digitChar-not-B 5 _ = refl
digitChar-not-B 6 _ = refl
digitChar-not-B 7 _ = refl
digitChar-not-B 8 _ = refl
digitChar-not-B 9 _ = refl
digitChar-not-B (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

digitChar-not-S : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ 'S') ≡ false
digitChar-not-S 0 _ = refl
digitChar-not-S 1 _ = refl
digitChar-not-S 2 _ = refl
digitChar-not-S 3 _ = refl
digitChar-not-S 4 _ = refl
digitChar-not-S 5 _ = refl
digitChar-not-S 6 _ = refl
digitChar-not-S 7 _ = refl
digitChar-not-S 8 _ = refl
digitChar-not-S 9 _ = refl
digitChar-not-S (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

digitChar-not-E : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ 'E') ≡ false
digitChar-not-E 0 _ = refl
digitChar-not-E 1 _ = refl
digitChar-not-E 2 _ = refl
digitChar-not-E 3 _ = refl
digitChar-not-E 4 _ = refl
digitChar-not-E 5 _ = refl
digitChar-not-E 6 _ = refl
digitChar-not-E 7 _ = refl
digitChar-not-E 8 _ = refl
digitChar-not-E 9 _ = refl
digitChar-not-E (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

-- ============================================================================
-- Head-classify witnesses for the 3 emit shapes
-- ============================================================================

-- showInt-chars head — non-quote + non-hspace + (digit-or-dash).  The
-- digit-or-dash refinement is used by the per-target target-eq witness
-- to dispatch on the leading char of value-chars.
showInt-chars-head-classify : ∀ z →
  ∃₂ λ x tail → showInt-chars z ≡ x ∷ tail
              × (x ≈ᵇ '"') ≡ false
              × isHSpace x ≡ false
              × ((Σ ℕ λ d → x ≡ digitChar d × d Data.Nat.< 10) ⊎ (x ≡ '-'))
showInt-chars-head-classify (+ n) with showNat-chars-head n
... | d , tail , d<10 , eq =
      digitChar d , tail , eq , digitChar-not-quote d d<10 ,
      digitChar-not-isHSpace d , inj₁ (d , refl , d<10)
showInt-chars-head-classify -[1+ _ ] =
  '-' , _ , refl , refl , refl , inj₂ refl

showDecRat-chars-head-classify : ∀ d →
  ∃₂ λ x tail → showDecRat-dec-chars d ≡ x ∷ tail
              × (x ≈ᵇ '"') ≡ false
              × isHSpace x ≡ false
              × ((Σ ℕ λ k → x ≡ digitChar k × k Data.Nat.< 10) ⊎ (x ≡ '-'))
showDecRat-chars-head-classify (Aletheia.DBC.DecRat.mkDecRat (+ zero) a b cx)
  with showDecRat-chars-head-digit zero a b cx
... | k , tail , k<10 , eq =
      digitChar k , tail , eq , digitChar-not-quote k k<10 ,
      digitChar-not-isHSpace k , inj₁ (k , refl , k<10)
showDecRat-chars-head-classify (Aletheia.DBC.DecRat.mkDecRat (+ suc n) a b cx)
  with showDecRat-chars-head-digit (suc n) a b cx
... | k , tail , k<10 , eq =
      digitChar k , tail , eq , digitChar-not-quote k k<10 ,
      digitChar-not-isHSpace k , inj₁ (k , refl , k<10)
showDecRat-chars-head-classify (Aletheia.DBC.DecRat.mkDecRat -[1+ n ] a b cx)
  with showDecRat-chars-head-dash n a b cx
... | tail , eq =
      '-' , tail , eq , refl , refl , inj₂ refl

-- ============================================================================
-- value-stops-isHSpace witnesses for the 3 emit shapes
-- ============================================================================

-- For RavString, the value starts with '"' which is not hspace.
value-stops-isHSpace-RavString : ∀ s outer-suffix
  → SuffixStops isHSpace
      (Aletheia.DBC.TextFormatter.Emitter.quoteStringLit-chars s
        ++ₗ ';' ∷ '\n' ∷ outer-suffix)
value-stops-isHSpace-RavString _ _ = ∷-stop refl

-- For RavDecRat-frac, the value's leading char is digit-or-dash, both
-- non-hspace.
value-stops-isHSpace-RavDecRatFrac : ∀ d outer-suffix
  → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ ';' ∷ '\n' ∷ outer-suffix)
value-stops-isHSpace-RavDecRatFrac d outer-suffix
  with showDecRat-chars-head-classify d
... | x , tail , eq , _ , x-not-hsp , _ =
  subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
        (sym eq) (∷-stop x-not-hsp)

-- For RavDecRat-bareInt, same head shape as frac.
value-stops-isHSpace-RavDecRatBareInt : ∀ z outer-suffix
  → SuffixStops isHSpace (showInt-chars z ++ₗ ';' ∷ '\n' ∷ outer-suffix)
value-stops-isHSpace-RavDecRatBareInt z outer-suffix
  with showInt-chars-head-classify z
... | x , tail , eq , _ , x-not-hsp , _ =
  subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
        (sym eq) (∷-stop x-not-hsp)

-- ============================================================================
-- showℕ-dec-chars head non-isHSpace (used by Message/Signal/Rel where
-- parseNatural reads the CAN ID before parseWS).
-- ============================================================================

showNat-chars-head-stop-isHSpace : ∀ (n : ℕ) (rest : List Char)
  → SuffixStops isHSpace (showℕ-dec-chars n ++ₗ rest)
showNat-chars-head-stop-isHSpace n rest with showNat-chars-head n
... | d , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digitChar-not-isHSpace d))
