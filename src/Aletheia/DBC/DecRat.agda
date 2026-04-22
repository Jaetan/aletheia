{-# OPTIONS --safe --without-K #-}

-- DBC decimal rational — rationals representable as n / (2^a · 5^b).
--
-- Purpose: DBC scale/offset fields are stored as terminating decimals
-- (e.g. 0.1, 25.375, 10.5).  Every terminating decimal is exactly
-- representable as n / (2^a · 5^b) for some integer n and naturals a, b.
-- The round-trip proof in B.3.d hinges on an exact parse/emit pair for
-- these numerics — a general ℚ would require an arbitrary prime-factor
-- denominator that the DBC grammar cannot emit.
--
-- Design:
--   * numerator : ℤ — signed, no magnitude restriction.
--   * twoExp / fiveExp : ℕ — denominator factorization 2^twoExp · 5^fiveExp.
--   * canonical : invariant that locks the representation so structural
--     equality agrees with ℚ equivalence.  Marked `.` (irrelevant): any
--     two proofs are definitionally equal, which (a) closes `_≟ᵈ_` via
--     `yes refl` once the numerical fields unify, and (b) is erased by
--     the compiler just like `@0` — zero runtime cost.
--
-- Canonical form (no common factor between numerator and denominator):
--   * zero: numerator = 0 ∧ twoExp = 0 ∧ fiveExp = 0.
--   * nonzero: twoExp > 0 ⇒ 2 ∤ |numerator|, fiveExp > 0 ⇒ 5 ∤ |numerator|.
--
-- `canonicalize` strips shared factors of 2 and 5 via a pair of
-- structurally-recursive helpers (`stripShared2-abs`, `stripShared5-abs`)
-- that decrement the exponent while it's still positive and a matching
-- factor is present.  No fuel, no termination puzzle.
--
-- Bridge to ℚ: `toℚ : DecRat → ℚ` via stdlib `_/_` which normalises by
-- gcd.  Two DecRat values with equal canonical fields project to equal
-- ℚ values by construction; the `canonicalize-value` lemma exposes this
-- at the ℚ surface for callers that only see post-canonicalisation.
--
-- Used by: DBC text-parser / formatter roundtrip (B.3.d) — signal
-- scale/offset/min/max, value-table keys, environment-variable bounds.
-- Not used on signal-extraction hot path: `CAN/Signal.agda` keeps ℚ.
module Aletheia.DBC.DecRat where

open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; _>_; z<s; s<s; NonZero)
  renaming (_/_ to _/ₙ_)
open import Data.Nat.Properties
  using (*-identityʳ; *-identityˡ; *-assoc; *-comm; *-zeroˡ; *-zeroʳ;
         *-cancelʳ-≡; *-cancelˡ-≡;
         m^n≢0; m*n≢0; m*n≡0⇒m≡0;
         +-identityˡ; +-identityʳ;
         suc-pred)
  renaming (_≟_ to _≟ₙ_)
open import Data.Nat.Divisibility
  using (_∣_; _∤_; _∣?_; divides; quotient; m∣n⇒n≡m*quotient; ∣-trans;
         _∣0)
open import Data.Nat.DivMod using (m/n*n≡m)
open import Data.Integer.Base
  using (ℤ; +_; -[1+_]; +0; +[1+_]; ∣_∣; sign; _◃_; 0ℤ)
open import Data.Integer.Properties
  using (signᵢ◃∣i∣≡i; ◃-cong; abs-◃; sign-◃; abs-*; +◃n≡+n;
         ◃-distrib-*)
  renaming (_≟_ to _≟ℤ_)
open import Data.Rational.Base using (ℚ; _/_; fromℚᵘ; mkℚ)
open import Data.Rational.Properties using (fromℚᵘ-cong)
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; mkℚᵘ; *≡*)
  renaming (_≃_ to _≃ᵘ_; ↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_)
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤP
import Data.Nat.Base as ℕ
open import Data.Sign.Base using (Sign)
import Data.Sign.Base as S
import Data.Sign.Properties as SP
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (isYes; map′)

------------------------------------------------------------------------
-- Canonical invariant

-- Boolean decision of canonicality on (|numerator|, twoExp, fiveExp).
-- Exhaustive pattern-match on all three arguments to avoid `∨`'s
-- left-biased reduction order getting stuck mid-proof.
isCanonicalᵇ : ℕ → ℕ → ℕ → Bool
isCanonicalᵇ zero    zero    zero    = true
isCanonicalᵇ zero    zero    (suc _) = false
isCanonicalᵇ zero    (suc _) _       = false
isCanonicalᵇ (suc _) zero    zero    = true
isCanonicalᵇ (suc n) zero    (suc _) = not (isYes (5 ∣? suc n))
isCanonicalᵇ (suc n) (suc _) zero    = not (isYes (2 ∣? suc n))
isCanonicalᵇ (suc n) (suc _) (suc _) =
  not (isYes (2 ∣? suc n)) ∧ not (isYes (5 ∣? suc n))

-- The canonical-form witness.  T-based so the field is proof-irrelevant;
-- `_≟ᵈ_` discharges it via `cong (mkDecRat …) (T-irrelevant cx cy)` once
-- the three numerical fields unify.
IsCanonical : ℕ → ℕ → ℕ → Set
IsCanonical n a b = T (isCanonicalᵇ n a b)

------------------------------------------------------------------------
-- The record

record DecRat : Set where
  constructor mkDecRat
  field
    numerator  : ℤ
    twoExp     : ℕ
    fiveExp    : ℕ
    .canonical : IsCanonical ∣ numerator ∣ twoExp fiveExp

------------------------------------------------------------------------
-- Constructors

-- Zero.
0ᵈ : DecRat
0ᵈ = mkDecRat (+ 0) 0 0 tt

-- Embed any ℤ with denominator 1.
fromℤ : ℤ → DecRat
fromℤ (+ 0)      = 0ᵈ
fromℤ (+ suc n)  = mkDecRat (+ suc n) 0 0 tt
fromℤ -[1+ n ]   = mkDecRat -[1+ n ]  0 0 tt

------------------------------------------------------------------------
-- Projection to ℚ

-- 2^a · 5^b is never zero.
2^a·5^b-NonZero : ∀ a b → NonZero (2 ^ a * 5 ^ b)
2^a·5^b-NonZero a b = m*n≢0 (2 ^ a) (5 ^ b)
  {{m^n≢0 2 a}} {{m^n≢0 5 b}}

-- The rational represented by a DecRat.  Denominator is always positive
-- so the ℚ is well-formed without explicit coprimality reasoning.
toℚ : DecRat → ℚ
toℚ (mkDecRat num a b _) = _/_ num (2 ^ a * 5 ^ b)
  {{2^a·5^b-NonZero a b}}

------------------------------------------------------------------------
-- Decidable equality

-- Two DecRat values are equal iff their three numerical fields agree.
-- The canonical witness is marked `.` (irrelevant), so any two proofs
-- are definitionally equal — `yes refl` closes the equality case once
-- the numerical fields unify, no `T-irrelevant` needed.
--
-- Refutation via `cong DecRat.field eq` rather than `λ { refl → … }`.
-- Direct refl-matching on `mkDecRat nx … ≡ mkDecRat nx …` requires K
-- (unify `nx = nx` at a concrete constructor position); routing through
-- `cong` keeps the refl match generic and `--without-K`-safe.
_≟ᵈ_ : (x y : DecRat) → Dec (x ≡ y)
mkDecRat nx ax bx cx ≟ᵈ mkDecRat ny ay by cy
  with nx ≟ℤ ny
... | no  nx≢ny = no (λ eq → nx≢ny (cong DecRat.numerator eq))
... | yes refl with ax ≟ₙ ay
...   | no  ax≢ay = no (λ eq → ax≢ay (cong DecRat.twoExp eq))
...   | yes refl with bx ≟ₙ by
...     | no  bx≢by = no (λ eq → bx≢by (cong DecRat.fiveExp eq))
...     | yes refl = yes refl

------------------------------------------------------------------------
-- Canonicalisation primitives (ℕ-level magnitudes)
--
-- Both helpers recurse structurally on the exponent (suc → predecessor).
-- The `yes` branch consumes one exponent step and divides the magnitude;
-- the `no` branch exits, guaranteeing the returned exponent witnesses
-- non-divisibility of the returned magnitude.  No fuel.

-- Strip factors of 2 shared between the magnitude and 2^twoExp.
-- Returns (magnitude-after, twoExp-after).
stripShared2-abs : (n : ℕ) (twoExp : ℕ) → ℕ × ℕ
stripShared2-abs n zero    = n , zero
stripShared2-abs n (suc a) with 2 ∣? n
... | yes 2∣n = stripShared2-abs (n /ₙ 2) a
... | no  _   = n , suc a

-- Strip factors of 5 shared between the magnitude and 5^fiveExp.
stripShared5-abs : (n : ℕ) (fiveExp : ℕ) → ℕ × ℕ
stripShared5-abs n zero    = n , zero
stripShared5-abs n (suc b) with 5 ∣? n
... | yes 5∣n = stripShared5-abs (n /ₙ 5) b
... | no  _   = n , suc b

-- Compose: strip 2s, then strip 5s.  Cross-prime preservation keeps
-- the 2-canonicality stable across the 5-strip.
canonicalizeNat : (n a b : ℕ) → ℕ × ℕ × ℕ
canonicalizeNat n a b with stripShared2-abs n a
... | n₂ , a₂ with stripShared5-abs n₂ b
...             | n₅ , b₅ = n₅ , a₂ , b₅

-- Signed canonicalisation: magnitude through canonicalizeNat, sign
-- reattached via `_◃_`.  `_◃_` treats `_ ◃ 0 = +0`, so the zero case
-- coalesces to `+0` regardless of the original sign.
canonicalize : (num : ℤ) (a b : ℕ) → ℤ × ℕ × ℕ
canonicalize num a b with canonicalizeNat ∣ num ∣ a b
... | n' , a' , b' = sign num ◃ n' , a' , b'

------------------------------------------------------------------------
-- stripShared-abs properties (ℕ-level)
--
-- Three invariants per stripper, proven by straight structural
-- induction on the exponent:
--   * -value    : cross-multiplication denominator preservation.
--   * -nonzero  : magnitude of a nonzero numerator stays nonzero.
--   * -canonical: a positive returned exponent witnesses non-divisibility
--                 of the returned magnitude by the stripped prime.

-- 2-strip: value preservation.  Denominator 2^a is redistributed between
-- numerator and exponent, but the product is invariant.
stripShared2-abs-value : ∀ n a →
  n * 2 ^ proj₂ (stripShared2-abs n a) ≡ proj₁ (stripShared2-abs n a) * 2 ^ a
stripShared2-abs-value n zero    = refl
stripShared2-abs-value n (suc a) with 2 ∣? n
... | no  _   = refl
... | yes 2∣n = begin
    n * 2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a)
      ≡⟨ cong (_* 2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a)) (sym (m/n*n≡m 2∣n)) ⟩
    (n /ₙ 2) * 2 * 2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a)
      ≡⟨ *-assoc (n /ₙ 2) 2 (2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a)) ⟩
    (n /ₙ 2) * (2 * 2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a))
      ≡⟨ cong ((n /ₙ 2) *_) (*-comm 2 (2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a))) ⟩
    (n /ₙ 2) * (2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a) * 2)
      ≡⟨ sym (*-assoc (n /ₙ 2) (2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a)) 2) ⟩
    (n /ₙ 2) * 2 ^ proj₂ (stripShared2-abs (n /ₙ 2) a) * 2
      ≡⟨ cong (_* 2) (stripShared2-abs-value (n /ₙ 2) a) ⟩
    proj₁ (stripShared2-abs (n /ₙ 2) a) * 2 ^ a * 2
      ≡⟨ *-assoc (proj₁ (stripShared2-abs (n /ₙ 2) a)) (2 ^ a) 2 ⟩
    proj₁ (stripShared2-abs (n /ₙ 2) a) * (2 ^ a * 2)
      ≡⟨ cong (proj₁ (stripShared2-abs (n /ₙ 2) a) *_) (*-comm (2 ^ a) 2) ⟩
    proj₁ (stripShared2-abs (n /ₙ 2) a) * (2 * 2 ^ a)
      ≡⟨⟩
    proj₁ (stripShared2-abs (n /ₙ 2) a) * 2 ^ suc a
    ∎
  where open ≡-Reasoning

-- 2-strip: nonzero preservation.  Zero → zero/2 = zero → recurses from
-- (0, a-1); nonzero stays nonzero because n/2 = 0 would back-multiply
-- to n = 0 via `m/n*n≡m`.
stripShared2-abs-nonzero : ∀ n a → n ≢ 0 →
  proj₁ (stripShared2-abs n a) ≢ 0
stripShared2-abs-nonzero n zero    n≢0 = n≢0
stripShared2-abs-nonzero n (suc a) n≢0 with 2 ∣? n
... | no  _   = n≢0
... | yes 2∣n = stripShared2-abs-nonzero (n /ₙ 2) a
                  (λ n/2≡0 → n≢0 (trans (sym (m/n*n≡m 2∣n))
                                        (cong (_* 2) n/2≡0)))

-- 2-strip: canonicality.  A positive returned exponent witnesses that
-- no further factor of 2 is extractable from the returned magnitude.
stripShared2-abs-canonical : ∀ n a → proj₂ (stripShared2-abs n a) > 0 →
  2 ∤ proj₁ (stripShared2-abs n a)
stripShared2-abs-canonical n zero    ()
stripShared2-abs-canonical n (suc a) h   with 2 ∣? n
... | no  2∤n = 2∤n
... | yes 2∣n = stripShared2-abs-canonical (n /ₙ 2) a h

-- 5-strip: value preservation.  Symmetric to stripShared2-abs-value.
stripShared5-abs-value : ∀ n b →
  n * 5 ^ proj₂ (stripShared5-abs n b) ≡ proj₁ (stripShared5-abs n b) * 5 ^ b
stripShared5-abs-value n zero    = refl
stripShared5-abs-value n (suc b) with 5 ∣? n
... | no  _   = refl
... | yes 5∣n = begin
    n * 5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b)
      ≡⟨ cong (_* 5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b)) (sym (m/n*n≡m 5∣n)) ⟩
    (n /ₙ 5) * 5 * 5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b)
      ≡⟨ *-assoc (n /ₙ 5) 5 (5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b)) ⟩
    (n /ₙ 5) * (5 * 5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b))
      ≡⟨ cong ((n /ₙ 5) *_) (*-comm 5 (5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b))) ⟩
    (n /ₙ 5) * (5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b) * 5)
      ≡⟨ sym (*-assoc (n /ₙ 5) (5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b)) 5) ⟩
    (n /ₙ 5) * 5 ^ proj₂ (stripShared5-abs (n /ₙ 5) b) * 5
      ≡⟨ cong (_* 5) (stripShared5-abs-value (n /ₙ 5) b) ⟩
    proj₁ (stripShared5-abs (n /ₙ 5) b) * 5 ^ b * 5
      ≡⟨ *-assoc (proj₁ (stripShared5-abs (n /ₙ 5) b)) (5 ^ b) 5 ⟩
    proj₁ (stripShared5-abs (n /ₙ 5) b) * (5 ^ b * 5)
      ≡⟨ cong (proj₁ (stripShared5-abs (n /ₙ 5) b) *_) (*-comm (5 ^ b) 5) ⟩
    proj₁ (stripShared5-abs (n /ₙ 5) b) * (5 * 5 ^ b)
      ≡⟨⟩
    proj₁ (stripShared5-abs (n /ₙ 5) b) * 5 ^ suc b
    ∎
  where open ≡-Reasoning

-- 5-strip: nonzero preservation.
stripShared5-abs-nonzero : ∀ n b → n ≢ 0 →
  proj₁ (stripShared5-abs n b) ≢ 0
stripShared5-abs-nonzero n zero    n≢0 = n≢0
stripShared5-abs-nonzero n (suc b) n≢0 with 5 ∣? n
... | no  _   = n≢0
... | yes 5∣n = stripShared5-abs-nonzero (n /ₙ 5) b
                  (λ n/5≡0 → n≢0 (trans (sym (m/n*n≡m 5∣n))
                                        (cong (_* 5) n/5≡0)))

-- 5-strip: canonicality.
stripShared5-abs-canonical : ∀ n b → proj₂ (stripShared5-abs n b) > 0 →
  5 ∤ proj₁ (stripShared5-abs n b)
stripShared5-abs-canonical n zero    ()
stripShared5-abs-canonical n (suc b) h   with 5 ∣? n
... | no  5∤n = 5∤n
... | yes 5∣n = stripShared5-abs-canonical (n /ₙ 5) b h

-- Cross-prime preservation.  Stripping 5s preserves 2∤ because any
-- 2-divisor of (n /ₙ 5) back-multiplies through 5 to a 2-divisor of n.
-- Same shape carries 5∤ through the 2-strip (symmetric helper below).
stripShared5-abs-preserves-2∤ : ∀ n b → 2 ∤ n →
  2 ∤ proj₁ (stripShared5-abs n b)
stripShared5-abs-preserves-2∤ n zero    2∤n = 2∤n
stripShared5-abs-preserves-2∤ n (suc b) 2∤n with 5 ∣? n
... | no  _   = 2∤n
... | yes 5∣n = stripShared5-abs-preserves-2∤ (n /ₙ 5) b 2∤n/5
  where
    2∤n/5 : 2 ∤ (n /ₙ 5)
    2∤n/5 2∣n/5 = 2∤n (∣-trans 2∣n/5
                     (divides 5 (trans (sym (m/n*n≡m 5∣n))
                                       (*-comm (n /ₙ 5) 5))))

-- 2-strip preserves 5∤ (mirror of the above, needed if we ever invert
-- the composition order; kept for symmetry with the 5-first direction).
stripShared2-abs-preserves-5∤ : ∀ n a → 5 ∤ n →
  5 ∤ proj₁ (stripShared2-abs n a)
stripShared2-abs-preserves-5∤ n zero    5∤n = 5∤n
stripShared2-abs-preserves-5∤ n (suc a) 5∤n with 2 ∣? n
... | no  _   = 5∤n
... | yes 2∣n = stripShared2-abs-preserves-5∤ (n /ₙ 2) a 5∤n/2
  where
    5∤n/2 : 5 ∤ (n /ₙ 2)
    5∤n/2 5∣n/2 = 5∤n (∣-trans 5∣n/2
                     (divides 2 (trans (sym (m/n*n≡m 2∣n))
                                       (*-comm (n /ₙ 2) 2))))

-- Zero-collapse for 2-strip.  `2 ∣ 0` always holds, so the recursion
-- walks the exponent down while the magnitude stays pinned to 0
-- (definitionally `0 /ₙ 2 ≡ 0`).  Needed to close canonicalize-witness
-- on the zero branch where the nonzero lemma does not apply.
stripShared2-abs-zero : ∀ a → stripShared2-abs 0 a ≡ (0 , 0)
stripShared2-abs-zero zero    = refl
stripShared2-abs-zero (suc a) with 2 ∣? 0
... | yes _   = stripShared2-abs-zero a
... | no  2∤0 = ⊥-elim (2∤0 (2 ∣0))

-- 5-strip zero-collapse (mirror).
stripShared5-abs-zero : ∀ b → stripShared5-abs 0 b ≡ (0 , 0)
stripShared5-abs-zero zero    = refl
stripShared5-abs-zero (suc b) with 5 ∣? 0
... | yes _   = stripShared5-abs-zero b
... | no  5∤0 = ⊥-elim (5∤0 (5 ∣0))

------------------------------------------------------------------------
-- Canonicality from algebraic preconditions
--
-- `isCanonicalᵇ-T` lifts the three stripShared-abs invariants
-- (nonzero, 2-stripped, 5-stripped) into the `T`-valued canonical
-- predicate.  Pattern-matching mirrors `isCanonicalᵇ`'s 7 clauses; the
-- extra `with 2 ∣? suc n` / `with 5 ∣? suc n` splits force Agda to
-- reduce `not (isYes …)` in each branch so the goal becomes `⊥` or
-- `⊤` concretely.
isCanonicalᵇ-T : ∀ n a b → n ≢ 0 →
  (0 < a → 2 ∤ n) →
  (0 < b → 5 ∤ n) →
  T (isCanonicalᵇ n a b)
isCanonicalᵇ-T zero    zero    zero    _    _  _  = tt
isCanonicalᵇ-T zero    zero    (suc _) n≢0  _  _  = ⊥-elim (n≢0 refl)
isCanonicalᵇ-T zero    (suc _) _       n≢0  _  _  = ⊥-elim (n≢0 refl)
isCanonicalᵇ-T (suc _) zero    zero    _    _  _  = tt
isCanonicalᵇ-T (suc n) zero    (suc _) _    _  h5 with 5 ∣? suc n
... | yes 5∣sn = ⊥-elim (h5 z<s 5∣sn)
... | no  _    = tt
isCanonicalᵇ-T (suc n) (suc _) zero    _    h2 _  with 2 ∣? suc n
... | yes 2∣sn = ⊥-elim (h2 z<s 2∣sn)
... | no  _    = tt
isCanonicalᵇ-T (suc n) (suc _) (suc _) _    h2 h5 with 2 ∣? suc n
... | yes 2∣sn = ⊥-elim (h2 z<s 2∣sn)
... | no  _    with 5 ∣? suc n
...   | yes 5∣sn = ⊥-elim (h5 z<s 5∣sn)
...   | no  _    = tt

------------------------------------------------------------------------
-- canonicalizeNat witness: the composed output is canonical.
--
-- Zero case collapses both strippers to (0, 0); the canonical form
-- of 0 is (0, 0, 0) which `isCanonicalᵇ` accepts as `true`.
--
-- Positive case: `stripShared2-abs-nonzero` and `-canonical` give the
-- 2-stripped magnitude's invariants; `stripShared5-abs-…` extend
-- through the 5-strip; `stripShared5-abs-preserves-2∤` carries the
-- 2-canonicality across the 5-strip (cross-prime preservation).
canonicalize-witness : ∀ n a b →
  IsCanonical (proj₁ (canonicalizeNat n a b))
              (proj₁ (proj₂ (canonicalizeNat n a b)))
              (proj₂ (proj₂ (canonicalizeNat n a b)))
canonicalize-witness zero    a b
  with stripShared2-abs 0 a | stripShared2-abs-zero a
... | .(0 , 0) | refl
  with stripShared5-abs 0 b | stripShared5-abs-zero b
...   | .(0 , 0) | refl = tt
canonicalize-witness (suc n) a b
  with stripShared2-abs (suc n) a
     | stripShared2-abs-nonzero (suc n) a (λ ())
     | stripShared2-abs-canonical (suc n) a
... | (n₂ , a₂) | n₂≢0 | canon-2
  with stripShared5-abs n₂ b
     | stripShared5-abs-nonzero n₂ b n₂≢0
     | stripShared5-abs-canonical n₂ b
     | stripShared5-abs-preserves-2∤ n₂ b
...   | (n₅ , b₅) | n₅≢0 | canon-5 | preserve-2 =
  isCanonicalᵇ-T n₅ a₂ b₅ n₅≢0
    (λ a₂>0 → preserve-2 (canon-2 a₂>0))
    canon-5

------------------------------------------------------------------------
-- canonicalizeNat value preservation (ℕ-level).
--
-- Rearranges the product `n * 2^a * 5^b` so that the denominator
-- factors migrate from the exponents to the magnitude (2-strip then
-- 5-strip) and back via the per-stripper `-value` lemmas.  Chain is
-- assoc/comm gymnastics only.
canonicalizeNat-value : ∀ n a b →
  n * (2 ^ proj₁ (proj₂ (canonicalizeNat n a b)) *
       5 ^ proj₂ (proj₂ (canonicalizeNat n a b))) ≡
  proj₁ (canonicalizeNat n a b) * (2 ^ a * 5 ^ b)
canonicalizeNat-value n a b
  with stripShared2-abs n a | stripShared2-abs-value n a
... | (n₂ , a₂) | val-2
  with stripShared5-abs n₂ b | stripShared5-abs-value n₂ b
...   | (n₅ , b₅) | val-5 = begin
      n * (2 ^ a₂ * 5 ^ b₅)
        ≡⟨ sym (*-assoc n (2 ^ a₂) (5 ^ b₅)) ⟩
      (n * 2 ^ a₂) * 5 ^ b₅
        ≡⟨ cong (_* 5 ^ b₅) val-2 ⟩
      (n₂ * 2 ^ a) * 5 ^ b₅
        ≡⟨ *-assoc n₂ (2 ^ a) (5 ^ b₅) ⟩
      n₂ * (2 ^ a * 5 ^ b₅)
        ≡⟨ cong (n₂ *_) (*-comm (2 ^ a) (5 ^ b₅)) ⟩
      n₂ * (5 ^ b₅ * 2 ^ a)
        ≡⟨ sym (*-assoc n₂ (5 ^ b₅) (2 ^ a)) ⟩
      (n₂ * 5 ^ b₅) * 2 ^ a
        ≡⟨ cong (_* 2 ^ a) val-5 ⟩
      (n₅ * 5 ^ b) * 2 ^ a
        ≡⟨ *-assoc n₅ (5 ^ b) (2 ^ a) ⟩
      n₅ * (5 ^ b * 2 ^ a)
        ≡⟨ cong (n₅ *_) (*-comm (5 ^ b) (2 ^ a)) ⟩
      n₅ * (2 ^ a * 5 ^ b)
      ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Sign-distributive helper: (s ◃ m) * + n ≡ s ◃ (m * n).
--
-- Sitting one step below `canonicalize-value-ℚᵘ`: the ℚᵘ cross-multiplication
-- identity reassembles the signed numerator as `sign num ◃ ∣ num ∣`, then
-- needs to push the signless denominator `+ (2^a * 5^b)` through the
-- sign.  No direct stdlib lemma; derived from `◃-distrib-*` + `+◃n≡+n` +
-- the `+` sign-identity.
◃-*-+ : ∀ s m n → (s ◃ m) ℤ.* (+ n) ≡ s ◃ (m * n)
◃-*-+ s m n = begin
    (s ◃ m) ℤ.* (+ n)
      ≡⟨ cong ((s ◃ m) ℤ.*_) (sym (+◃n≡+n n)) ⟩
    (s ◃ m) ℤ.* (S.+ ◃ n)
      ≡⟨ sym (◃-distrib-* s S.+ m n) ⟩
    (s S.* S.+) ◃ (m * n)
      ≡⟨ cong (_◃ (m * n)) (SP.*-identityʳ s) ⟩
    s ◃ (m * n)
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- canonicalize value preservation at the ℚᵘ layer.
--
-- Strategy: reduce ℚᵘ `≃` to integer cross-multiplication via `*≡*`, then
-- bridge the two `suc (2^_ * 5^_ ∸ 1)` denominators through `suc-pred`
-- (both exponent products are NonZero via `2^a·5^b-NonZero`).  The
-- signed-numerator side reassembles `num ≡ sign num ◃ ∣ num ∣` through
-- `signᵢ◃∣i∣≡i`, then the ℕ-level `canonicalizeNat-value` does the real
-- work under `cong (sign num ◃_)`.
--
-- The nested `with stripShared2-abs | stripShared2-abs-value` / second
-- level analogue is load-bearing: we bring the `-value` equations into
-- the with-abstraction so their types refine in lockstep with the
-- pattern-bound names `(n₂ , a₂)` / `(n₅ , b₅)`.  Calling the composed
-- `canonicalizeNat-value` externally fails because its own internal
-- with-abstraction makes its return type opaque to the outer goal.
-- The ℕ-level chain here re-derives the same equality inline using
-- the primitive `stripShared*-value` witnesses.
canonicalize-value-ℚᵘ : ∀ num a b →
  mkℚᵘ num (2 ^ a * 5 ^ b ∸ 1) ≃ᵘ
  mkℚᵘ (proj₁ (canonicalize num a b))
       (2 ^ proj₁ (proj₂ (canonicalize num a b)) *
        5 ^ proj₂ (proj₂ (canonicalize num a b)) ∸ 1)
canonicalize-value-ℚᵘ num a b
  with stripShared2-abs ∣ num ∣ a | stripShared2-abs-value ∣ num ∣ a
... | (n₂ , a₂) | val-2
  with stripShared5-abs n₂ b | stripShared5-abs-value n₂ b
...   | (n₅ , b₅) | val-5 = *≡* (begin
    num ℤ.* (+ suc (2 ^ a₂ * 5 ^ b₅ ∸ 1))
      ≡⟨ cong (λ k → num ℤ.* (+ k))
              (suc-pred (2 ^ a₂ * 5 ^ b₅) {{2^a·5^b-NonZero a₂ b₅}}) ⟩
    num ℤ.* (+ (2 ^ a₂ * 5 ^ b₅))
      ≡⟨ cong (ℤ._* (+ (2 ^ a₂ * 5 ^ b₅))) (sym (signᵢ◃∣i∣≡i num)) ⟩
    (sign num ◃ ∣ num ∣) ℤ.* (+ (2 ^ a₂ * 5 ^ b₅))
      ≡⟨ ◃-*-+ (sign num) ∣ num ∣ (2 ^ a₂ * 5 ^ b₅) ⟩
    sign num ◃ (∣ num ∣ * (2 ^ a₂ * 5 ^ b₅))
      ≡⟨ cong (sign num ◃_) chain-val ⟩
    sign num ◃ (n₅ * (2 ^ a * 5 ^ b))
      ≡⟨ sym (◃-*-+ (sign num) n₅ (2 ^ a * 5 ^ b)) ⟩
    (sign num ◃ n₅) ℤ.* (+ (2 ^ a * 5 ^ b))
      ≡⟨ cong (λ k → (sign num ◃ n₅) ℤ.* (+ k))
              (sym (suc-pred (2 ^ a * 5 ^ b) {{2^a·5^b-NonZero a b}})) ⟩
    (sign num ◃ n₅) ℤ.* (+ suc (2 ^ a * 5 ^ b ∸ 1))
    ∎)
  where
    open ≡-Reasoning
    chain-val : ∣ num ∣ * (2 ^ a₂ * 5 ^ b₅) ≡ n₅ * (2 ^ a * 5 ^ b)
    chain-val = begin
        ∣ num ∣ * (2 ^ a₂ * 5 ^ b₅)
          ≡⟨ sym (*-assoc ∣ num ∣ (2 ^ a₂) (5 ^ b₅)) ⟩
        (∣ num ∣ * 2 ^ a₂) * 5 ^ b₅
          ≡⟨ cong (_* 5 ^ b₅) val-2 ⟩
        (n₂ * 2 ^ a) * 5 ^ b₅
          ≡⟨ *-assoc n₂ (2 ^ a) (5 ^ b₅) ⟩
        n₂ * (2 ^ a * 5 ^ b₅)
          ≡⟨ cong (n₂ *_) (*-comm (2 ^ a) (5 ^ b₅)) ⟩
        n₂ * (5 ^ b₅ * 2 ^ a)
          ≡⟨ sym (*-assoc n₂ (5 ^ b₅) (2 ^ a)) ⟩
        (n₂ * 5 ^ b₅) * 2 ^ a
          ≡⟨ cong (_* 2 ^ a) val-5 ⟩
        (n₅ * 5 ^ b) * 2 ^ a
          ≡⟨ *-assoc n₅ (5 ^ b) (2 ^ a) ⟩
        n₅ * (5 ^ b * 2 ^ a)
          ≡⟨ cong (n₅ *_) (*-comm (5 ^ b) (2 ^ a)) ⟩
        n₅ * (2 ^ a * 5 ^ b)
        ∎

------------------------------------------------------------------------
-- Bridge: `fromℚᵘ (mkℚᵘ n (d ∸ 1)) ≡ n / d` for any NonZero d.
--
-- The RHS `_/_` requires an instance for its NonZero argument.  Pattern-
-- matching `d = suc d-1` exposes the definitional equation `fromℚᵘ
-- (mkℚᵘ n d-1) = n / suc d-1` (see Data.Rational.Base:149-150); `d ∸ 1`
-- reduces to `d-1` on `suc d-1`.  Zero is unreachable by the instance.
fromℚᵘ-mkℚᵘ-/ : ∀ n d .{{nz : NonZero d}} →
  fromℚᵘ (mkℚᵘ n (d ∸ 1)) ≡ _/_ n d {{nz}}
fromℚᵘ-mkℚᵘ-/ n (suc d-1) = refl

------------------------------------------------------------------------
-- canonicalize value preservation at the ℚ layer.
--
-- Lift `canonicalize-value-ℚᵘ` through `fromℚᵘ-cong`, then pin both
-- sides to the `_/_` normaliser with `fromℚᵘ-mkℚᵘ-/`.  The caller-facing
-- form matches `toℚ`'s denominator shape `2^a * 5^b`.
canonicalize-value : ∀ num a b →
  _/_ num (2 ^ a * 5 ^ b) {{2^a·5^b-NonZero a b}} ≡
  _/_ (proj₁ (canonicalize num a b))
      (2 ^ proj₁ (proj₂ (canonicalize num a b)) *
       5 ^ proj₂ (proj₂ (canonicalize num a b)))
      {{2^a·5^b-NonZero (proj₁ (proj₂ (canonicalize num a b)))
                        (proj₂ (proj₂ (canonicalize num a b)))}}
canonicalize-value num a b = begin
    _/_ num (2 ^ a * 5 ^ b) {{2^a·5^b-NonZero a b}}
      ≡⟨ sym (fromℚᵘ-mkℚᵘ-/ num (2 ^ a * 5 ^ b) {{2^a·5^b-NonZero a b}}) ⟩
    fromℚᵘ (mkℚᵘ num (2 ^ a * 5 ^ b ∸ 1))
      ≡⟨ fromℚᵘ-cong (canonicalize-value-ℚᵘ num a b) ⟩
    fromℚᵘ (mkℚᵘ (proj₁ (canonicalize num a b))
                 (2 ^ proj₁ (proj₂ (canonicalize num a b)) *
                  5 ^ proj₂ (proj₂ (canonicalize num a b)) ∸ 1))
      ≡⟨ fromℚᵘ-mkℚᵘ-/ (proj₁ (canonicalize num a b))
                       (2 ^ proj₁ (proj₂ (canonicalize num a b)) *
                        5 ^ proj₂ (proj₂ (canonicalize num a b)))
                       {{2^a·5^b-NonZero (proj₁ (proj₂ (canonicalize num a b)))
                                         (proj₂ (proj₂ (canonicalize num a b)))}} ⟩
    _/_ (proj₁ (canonicalize num a b))
        (2 ^ proj₁ (proj₂ (canonicalize num a b)) *
         5 ^ proj₂ (proj₂ (canonicalize num a b)))
        {{2^a·5^b-NonZero (proj₁ (proj₂ (canonicalize num a b)))
                          (proj₂ (proj₂ (canonicalize num a b)))}}
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Canonicaliser as a total DecRat builder.
--
-- Takes `(num, a, b)` with no canonicality precondition, strips common
-- factors of 2 and 5 between `∣ num ∣` and the denominator, and emits a
-- DecRat with the canonical invariant provably satisfied.  Two transports:
--   1. An inner `subst` along the captured equation
--      `can-eq : canonicalizeNat ∣ num ∣ a b ≡ (n' , a' , b')` to project
--      `canonicalize-witness`'s return type onto the pattern-bound names.
--      (A plain outer with-abstraction on `canonicalizeNat` doesn't suffice
--      because `canonicalize-witness` has its own internal with-chain that
--      keeps `canonicalizeNat`'s projections in reduced-but-opaque form.)
--   2. An outer `subst` along `sym (abs-◃ (sign num) n')` to bridge the
--      raw magnitude `n'` to the record-level magnitude `∣ sign num ◃ n' ∣`.
canonicalizeDecRat : (num : ℤ) (a b : ℕ) → DecRat
canonicalizeDecRat num a b
  with canonicalizeNat ∣ num ∣ a b in can-eq
... | (n' , a' , b') =
  mkDecRat (sign num ◃ n') a' b'
    (subst (λ m → IsCanonical m a' b')
           (sym (abs-◃ (sign num) n'))
           (subst (λ p → IsCanonical (proj₁ p)
                                     (proj₁ (proj₂ p))
                                     (proj₂ (proj₂ p)))
                  can-eq
                  (canonicalize-witness ∣ num ∣ a b)))
