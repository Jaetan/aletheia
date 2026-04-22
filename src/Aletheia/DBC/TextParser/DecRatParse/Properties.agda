{-# OPTIONS --safe --without-K #-}

-- DBC DecRat parser — roundtrip proof scaffolding (Phase B.3.d pre-gate,
-- commit 2/6).  Target theorem:
--
--   parseDecRat-roundtrip : ∀ d → runParser parseDecRat
--                              (showDecRat-dec-chars d) ≡ just (d , _)
--
-- stated over `List Char` (not `String`) per the Option-1-scoped-to-
-- per-primitive decision captured in `memory/project_b3d_stdlib_audit.md`.
-- Sidesteps the `toList-++ₛ` substrate gap: the emitter primitive
-- `showDecRat-dec-chars` and the parser's input list stream stay in
-- `List Char` end-to-end, so no `String`-level append lemma is needed.
--
-- Proof structure (advisor 3-phase plan):
--
--   * Phase 1 (this file, below): arithmetic and list-level lemmas.
--     No parser machinery — pure ℕ / List Char content over
--     `digitChar`, `charToDigit`, `digitToNat`, `parseDigitList`,
--     `showNat-chars`, `showℕ-padded-chars`.  Self-contained; can
--     type-check without Phase 2/3.
--
--     Digit-converter-generic foldl lemmas underpin everything: the
--     parser pipeline uses two digit converters — `digitToNat` from
--     `Protocol/JSON/Parse` via `parseNatural` (integer part) and
--     `charToDigit` via the local `parseDigitList` (fractional part).
--     Rather than duplicate the fuel/padded proofs, the core lemmas
--     below take `f : Char → ℕ` as a parameter with a hypothesis
--     `f ∘ digitChar ≡ id` on [0..9]; specialisations pin `f` to each
--     concrete converter.
--
--   * Phase 2 (future): `manyHelper-satisfy-prefix` — general-form
--     lemma about `some (satisfy P)` reading back the concatenation
--     of a List Char prefix.  Reusable for B.3.d layers 2–3.
--
--   * Phase 3 (future): top-level composition.  `parseNatural-showNat-
--     chars`, `some-digit-showℕ-padded-chars`, sign branch, then
--     `parseDecRat-roundtrip` invoking
--     `canonicalizeNat-scale-pos` to strip the emitter's scaling.
--
-- Each phase builds on the previous without reopening earlier ones.
module Aletheia.DBC.TextParser.DecRatParse.Properties where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char; toℕ)
open import Data.Char.Base using (isDigit; _≈ᵇ_)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as EmptyI
open import Data.List using (List; []; _∷_; length; foldl) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (length-++ to length-++ₗ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _^_; _⊔_;
         _<_; _≤_; z≤n; s≤s; NonZero)
open import Data.Nat.Base using (≢-nonZero⁻¹)
open import Data.Nat.Properties
  using (*-comm; +-comm; +-identityʳ; ≤-<-trans; n<1+n; ^-monoʳ-<;
         m≤m+n; m∸n+n≡m; m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl;
         m*n≢0; m^n≢0)
open import Data.Nat.DivMod
  using (m%n<n; m≡m%n+[m/n]*n; m<n*o⇒m/o<n)
open import Data.Nat.Divisibility using (_∣_; _∣?_; _∤_)
open import Data.Product using (Σ; _×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; value; position; remaining;
         advancePosition; advancePositions;
         satisfy; digit; some; many; manyHelper; sameLengthᵇ;
         char; optional;
         _>>=_; pure; _<$>_; _<*>_; _*>_; _<|>_)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars;
         emitMagnitude-chars; showDecRat-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse
  using (charToDigit; parseDigitList; parseDecRat; applySign; buildDecRat)
open import Aletheia.DBC.TextParser.Lexer using (parseNatural)
open import Aletheia.Protocol.JSON.Parse using (digitToNat)
open import Data.Integer using (ℤ; sign; _◃_; ∣_∣)
  renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Aletheia.DBC.DecRat
  using (DecRat; mkDecRat; isCanonicalᵇ; IsCanonical;
         canonicalizeDecRat; canonicalizeNat)
open import Aletheia.DBC.DecRat.ScaleLemmas using (canonicalizeNat-scale-pos)

-- ============================================================================
-- Phase 1.1: Digit-character roundtrip (concrete 0..9 reductions)
-- ============================================================================

-- `digitToNat ∘ digitChar ≡ id` on [0..9].  Used by `parseNatural`'s
-- foldl-side reasoning on the integer part: `parseNatural` calls
-- `foldl (λ acc d → acc * 10 + digitToNat d) 0 digits`, and Phase 3
-- needs this lemma (instantiated as `f-digitChar`) to discharge
-- `digitToNat (digitChar k) ≡ k` for each emitted digit `k = x % 10 <
-- 10`.
--
-- Ten concrete reductions: each side reduces to `k` via
-- `primCharToNat '0'..'9' ≡ 48..57` and `digitToNat`'s explicit case
-- list.  The catch-all absurd branch forces the `d < 10` precondition
-- to do work (without it the emitter's `digitChar d` for `d ≥ 10`
-- would collapse to `'0'` silently).
digitToNat-digitChar : ∀ d → d < 10 → digitToNat (digitChar d) ≡ d
digitToNat-digitChar 0 _ = refl
digitToNat-digitChar 1 _ = refl
digitToNat-digitChar 2 _ = refl
digitToNat-digitChar 3 _ = refl
digitToNat-digitChar 4 _ = refl
digitToNat-digitChar 5 _ = refl
digitToNat-digitChar 6 _ = refl
digitToNat-digitChar 7 _ = refl
digitToNat-digitChar 8 _ = refl
digitToNat-digitChar 9 _ = refl
digitToNat-digitChar (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- `charToDigit ∘ digitChar ≡ id` on [0..9].  Used by `parseDigitList`'s
-- foldl-side reasoning on the fractional part.  `charToDigit` is
-- defined as `toℕ c ∸ 48`, so this reduces via the built-in
-- `primCharToNat '0'..'9' ≡ 48..57` on each branch.  Separate lemma
-- from `digitToNat-digitChar` because DBC's DecRatParse uses a
-- different digit-to-ℕ converter from Protocol/JSON/Parse's
-- parseNatural (`digitToNat`), and the roundtrip proof goes through
-- both.
charToDigit-digitChar : ∀ d → d < 10 → charToDigit (digitChar d) ≡ d
charToDigit-digitChar 0 _ = refl
charToDigit-digitChar 1 _ = refl
charToDigit-digitChar 2 _ = refl
charToDigit-digitChar 3 _ = refl
charToDigit-digitChar 4 _ = refl
charToDigit-digitChar 5 _ = refl
charToDigit-digitChar 6 _ = refl
charToDigit-digitChar 7 _ = refl
charToDigit-digitChar 8 _ = refl
charToDigit-digitChar 9 _ = refl
charToDigit-digitChar (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- ============================================================================
-- Phase 1.2: Generic foldl snoc over any digit converter
-- ============================================================================

-- Inner helper: left-fold over `xs ++ [d]` from an arbitrary starting
-- accumulator `acc` equals the left-fold over `xs` from `acc`, then
-- one more step `* 10 + f d`.  `acc` must vary in the statement for
-- the induction step to type-check (the recursive call threads
-- `acc * 10 + f x` through).  Parameterised over the digit converter
-- `f : Char → ℕ` so the same proof serves both `parseDigitList`
-- (`f = charToDigit`) and `parseNatural`'s inner foldl
-- (`f = digitToNat`).  Pure list-level fact independent of parsing.
foldl-digit-++-snoc : (f : Char → ℕ) → ∀ xs d (acc : ℕ) →
  foldl (λ a e → a * 10 + f e) acc (xs ++ₗ d ∷ []) ≡
  foldl (λ a e → a * 10 + f e) acc xs * 10 + f d
foldl-digit-++-snoc f []       d acc = refl
foldl-digit-++-snoc f (x ∷ xs) d acc =
  foldl-digit-++-snoc f xs d (acc * 10 + f x)

-- Specialisation to `parseDigitList = foldl charToDigit 0`.  Used by
-- the fractional-part roundtrip in `parseDigitList-showℕ-padded-chars`.
parseDigitList-++-snoc : ∀ xs d →
  parseDigitList (xs ++ₗ d ∷ []) ≡ parseDigitList xs * 10 + charToDigit d
parseDigitList-++-snoc xs d = foldl-digit-++-snoc charToDigit xs d 0

-- ============================================================================
-- Phase 1.3: showNat-chars fuel bound
-- ============================================================================

-- `n < 10 ^ suc n` for every `n`.  Precondition needed to drive
-- `foldl-digit-showNat-chars-fuel` on `showNat-chars n =
-- showNat-chars-fuel (suc n) n`.  Loose bound — the actual digit
-- count of `n` is `⌊log₁₀ n⌋ + 1`, far less than `suc n` — but
-- `suc n` is easy to establish without `log`, and the fuel only
-- needs to be *enough*, not *tight*.
--
-- Induction on n:
--   * 0 < 10               (base; `s≤s z≤n`).
--   * suc n < 10^(suc (suc n)): chain IH `n < 10^(suc n)` (giving
--     `suc n ≤ 10^(suc n)`) with `10^(suc n) < 10^(suc (suc n))`
--     (from `^-monoʳ-<` at base `10 > 1` and `suc n < suc (suc n)`).
n<10^suc-n : ∀ n → n < 10 ^ suc n
n<10^suc-n zero    = s≤s z≤n
n<10^suc-n (suc n) =
  ≤-<-trans (n<10^suc-n n) (^-monoʳ-< 10 (s≤s (s≤s z≤n)) (n<1+n (suc n)))

-- `n / 10 < 10^w` given `n < 10^(suc w) = 10 * 10^w`.  Used by both
-- the fuel theorem below (recursive step) and
-- `foldl-digit-showℕ-padded-chars` (recursive step) to shrink the
-- fuel / width precondition to the IH's form.  Built on stdlib's
-- `m<n*o⇒m/o<n`; the `*-comm` is needed because the exponent
-- convention `10^(suc w) = 10 * 10^w` does not match the lemma's
-- `n * o` order directly (it wants `10^w * 10`).
n/10<10^w : ∀ w n → n < 10 ^ suc w → n / 10 < 10 ^ w
n/10<10^w w n n<10^[1+w] =
  m<n*o⇒m/o<n (subst (n <_) (*-comm 10 (10 ^ w)) n<10^[1+w])

-- ============================================================================
-- Phase 1.4: foldl-f ∘ showNat-chars ≡ id (digit-converter-generic)
-- ============================================================================

-- Fuel-parameterised roundtrip core over an arbitrary digit converter
-- `f : Char → ℕ` satisfying `f (digitChar d) ≡ d` for `d < 10`.
-- Induction on `fuel`:
--   * `fuel = 0`: `n < 10^0 = 1` forces `n ≡ 0`; `showNat-chars-fuel
--     0 _ = []` so `foldl f 0 [] = 0 = n`.
--   * `fuel = suc f'`: case-split on `n / 10 in eq`:
--     - `n / 10 = 0`: emitter writes `[digitChar (n % 10)]`.
--       `foldl f 0 [d] = 0 * 10 + f d = f d`.
--       `f (digitChar (n % 10)) ≡ n % 10` by `f-digitChar` (valid
--       since `n % 10 < 10`).  `n ≡ n % 10` because `n ≡ n % 10 +
--       (n / 10) * 10 ≡ n % 10 + 0 * 10 ≡ n % 10` (via
--       `m≡m%n+[m/n]*n` + `eq` + `+-identityʳ`).
--     - `n / 10 = suc m`: emitter writes `showNat-chars-fuel f' (suc
--       m) ++ [digitChar (n % 10)]`.  `foldl-digit-++-snoc` splits
--       off the last digit; IH applied at `f'` and `suc m` (with
--       bound `suc m < 10^f'` via `n/10<10^w` + `eq`) closes the
--       prefix; `m≡m%n+[m/n]*n` + `+-comm` + `eq` reassemble `n`.
foldl-digit-showNat-chars-fuel :
  (f : Char → ℕ) →
  (f-digitChar : ∀ d → d < 10 → f (digitChar d) ≡ d) →
  ∀ fuel n → n < 10 ^ fuel →
  foldl (λ a e → a * 10 + f e) 0 (showNat-chars-fuel fuel n) ≡ n
foldl-digit-showNat-chars-fuel _ _ zero    zero    _ = refl
foldl-digit-showNat-chars-fuel _ _ zero    (suc _) (s≤s ())
foldl-digit-showNat-chars-fuel f f-digitChar (suc f') n n<10^[1+f'] with n / 10 in eq
... | zero  = lemma-zero
  where
    open ≡-Reasoning
    -- `n ≡ n % 10` under `n / 10 ≡ 0`.  `zero * 10` reduces to `zero`
    -- definitionally; the final `+-identityʳ` strips the trailing `+ 0`.
    n≡n%10 : n ≡ n % 10
    n≡n%10 =
      trans (m≡m%n+[m/n]*n n 10)
            (trans (cong (λ k → n % 10 + k * 10) eq)
                   (+-identityʳ (n % 10)))
    lemma-zero : foldl (λ a e → a * 10 + f e) 0
                   (digitChar (n % 10) ∷ []) ≡ n
    lemma-zero =
      begin
        foldl (λ a e → a * 10 + f e) 0 (digitChar (n % 10) ∷ [])
          ≡⟨⟩
        f (digitChar (n % 10))
          ≡⟨ f-digitChar (n % 10) (m%n<n n 10) ⟩
        n % 10
          ≡⟨ sym n≡n%10 ⟩
        n
      ∎
... | suc m = lemma-suc
  where
    open ≡-Reasoning
    -- `suc m < 10^f'`: transport the generic `n / 10 < 10^f'` through `eq`.
    1+m<10^f' : suc m < 10 ^ f'
    1+m<10^f' = subst (_< 10 ^ f') eq (n/10<10^w f' n n<10^[1+f'])
    lemma-suc : foldl (λ a e → a * 10 + f e) 0
                  (showNat-chars-fuel f' (suc m) ++ₗ digitChar (n % 10) ∷ [])
                  ≡ n
    lemma-suc =
      begin
        foldl (λ a e → a * 10 + f e) 0
              (showNat-chars-fuel f' (suc m) ++ₗ digitChar (n % 10) ∷ [])
          ≡⟨ foldl-digit-++-snoc f (showNat-chars-fuel f' (suc m))
                                   (digitChar (n % 10)) 0 ⟩
        foldl (λ a e → a * 10 + f e) 0 (showNat-chars-fuel f' (suc m)) * 10
          + f (digitChar (n % 10))
          ≡⟨ cong (λ k → k * 10 + f (digitChar (n % 10)))
                  (foldl-digit-showNat-chars-fuel f f-digitChar f' (suc m)
                     1+m<10^f') ⟩
        suc m * 10 + f (digitChar (n % 10))
          ≡⟨ cong ((suc m * 10) +_) (f-digitChar (n % 10) (m%n<n n 10)) ⟩
        suc m * 10 + n % 10
          ≡⟨ sym (cong (λ k → k * 10 + n % 10) eq) ⟩
        n / 10 * 10 + n % 10
          ≡⟨ +-comm (n / 10 * 10) (n % 10) ⟩
        n % 10 + n / 10 * 10
          ≡⟨ sym (m≡m%n+[m/n]*n n 10) ⟩
        n
      ∎

-- Specialisations: pin `f` to each concrete digit converter.

-- `parseDigitList ∘ showNat-chars ≡ id`.  Not directly consumed by
-- the top-level DecRat roundtrip (the integer part is parsed by
-- `parseNatural`, not `parseDigitList`), but free from the
-- abstraction and exported for sibling per-primitive lemmas.
parseDigitList-showNat-chars : ∀ n → parseDigitList (showNat-chars n) ≡ n
parseDigitList-showNat-chars n =
  foldl-digit-showNat-chars-fuel charToDigit charToDigit-digitChar
    (suc n) n (n<10^suc-n n)

-- Parser-ready form for `parseNatural`.  `parseNatural` extracts the
-- digit list via `some (satisfy isDigit)` then applies
-- `foldl (λ acc d → acc * 10 + digitToNat d) 0`.  Phase 3 composes
-- this lemma with `manyHelper-satisfy-prefix` (Phase 2) to close
-- `parseNatural (showNat-chars n) ≡ (n , _)`.
foldl-digitToNat-showNat-chars : ∀ n →
  foldl (λ acc d → acc * 10 + digitToNat d) 0 (showNat-chars n) ≡ n
foldl-digitToNat-showNat-chars n =
  foldl-digit-showNat-chars-fuel digitToNat digitToNat-digitChar
    (suc n) n (n<10^suc-n n)

-- ============================================================================
-- Phase 1.5: foldl-f ∘ showℕ-padded-chars ≡ id (under n < 10^w)
-- ============================================================================

-- Width-bounded roundtrip for the fractional-digit emitter, generic
-- over the digit converter `f`.  Unlike `showNat-chars`,
-- `showℕ-padded-chars` is structurally recursive on `width` (not on a
-- separate `fuel` argument), so we induct on `width` directly.  The
-- precondition `n < 10^w` is exactly the statement that `n` fits in
-- `w` base-10 digits; the Shape B emitter enforces it at every call
-- site via `n = scaledNum % 10^m`.
--
-- The suc-case reasoning mirrors the `suc m` case of the fuel
-- theorem above (same snoc + IH + `m≡m%n+[m/n]*n` rearrangement).
foldl-digit-showℕ-padded-chars :
  (f : Char → ℕ) →
  (f-digitChar : ∀ d → d < 10 → f (digitChar d) ≡ d) →
  ∀ w n → n < 10 ^ w →
  foldl (λ a e → a * 10 + f e) 0 (showℕ-padded-chars w n) ≡ n
foldl-digit-showℕ-padded-chars _ _ zero    zero    _ = refl
foldl-digit-showℕ-padded-chars _ _ zero    (suc _) (s≤s ())
foldl-digit-showℕ-padded-chars f f-digitChar (suc w) n n<10^[1+w] =
  begin
    foldl (λ a e → a * 10 + f e) 0
          (showℕ-padded-chars w (n / 10) ++ₗ digitChar (n % 10) ∷ [])
      ≡⟨ foldl-digit-++-snoc f (showℕ-padded-chars w (n / 10))
                               (digitChar (n % 10)) 0 ⟩
    foldl (λ a e → a * 10 + f e) 0 (showℕ-padded-chars w (n / 10)) * 10
      + f (digitChar (n % 10))
      ≡⟨ cong (λ k → k * 10 + f (digitChar (n % 10)))
              (foldl-digit-showℕ-padded-chars f f-digitChar w (n / 10)
                 (n/10<10^w w n n<10^[1+w])) ⟩
    n / 10 * 10 + f (digitChar (n % 10))
      ≡⟨ cong ((n / 10 * 10) +_) (f-digitChar (n % 10) (m%n<n n 10)) ⟩
    n / 10 * 10 + n % 10
      ≡⟨ +-comm (n / 10 * 10) (n % 10) ⟩
    n % 10 + n / 10 * 10
      ≡⟨ sym (m≡m%n+[m/n]*n n 10) ⟩
    n
  ∎
  where open ≡-Reasoning

-- Specialisation used by the fractional-part roundtrip: the
-- fractional digits are emitted by `showℕ-padded-chars m (scaledNum %
-- 10^m)` and consumed by `parseDigitList` inside `buildDecRat`.
parseDigitList-showℕ-padded-chars : ∀ w n → n < 10 ^ w →
  parseDigitList (showℕ-padded-chars w n) ≡ n
parseDigitList-showℕ-padded-chars =
  foldl-digit-showℕ-padded-chars charToDigit charToDigit-digitChar

-- ============================================================================
-- Phase 2: many (satisfy P) reads back a uniform prefix
-- ============================================================================
--
-- Reusable for future B.3.d layers 2–3: any primitive whose parser is
-- `some (satisfy P)` or `many (satisfy P)` over a `List Char` suffix
-- that stops via `P c ≡ false` (or end-of-input) closes through this
-- layer.  For DecRat specifically: `parseNatural` (integer part,
-- `P = isDigit`) and `some digit` (fractional part, `P = isDigit`)
-- both land on `some-satisfy-prefix` below.
--
-- The workhorse lemma `manyHelper-satisfy-exhaust` is parameterised
-- over the predicate `P` and pattern-matches on the `manyHelper`
-- structure exposed publicly in `Aletheia.Parser.Combinators`
-- (unprivatised 2026-04-22 to enable this proof).

-- ----------------------------------------------------------------------------
-- Phase 2.1: sameLengthᵇ cons (manyHelper termination-guard discharge)
-- ----------------------------------------------------------------------------

-- `manyHelper` checks `sameLengthᵇ input (remaining result)` to
-- detect zero-progress parsers.  When `satisfy P` consumes a real
-- character, the post-result remaining is exactly one shorter than
-- the pre-input (i.e. `remaining ≡ tail input`), so the check must
-- discharge to `false`.
sameLengthᵇ-cons : ∀ {A : Set} (x : A) (l : List A) →
  sameLengthᵇ (x ∷ l) l ≡ false
sameLengthᵇ-cons _ []       = refl
sameLengthᵇ-cons _ (y ∷ ys) = sameLengthᵇ-cons y ys

-- ----------------------------------------------------------------------------
-- Phase 2.2: SuffixStops P — characterises a stop boundary
-- ----------------------------------------------------------------------------

-- `SuffixStops P suffix` — either the suffix is empty, or its first
-- character fails `P`.  In both cases `manyHelper (satisfy P)` on
-- `suffix` (with any fuel ≥ 0) returns the empty-result base.
data SuffixStops (P : Char → Bool) : List Char → Set where
  []-stop : SuffixStops P []
  ∷-stop  : ∀ {c cs} → P c ≡ false → SuffixStops P (c ∷ cs)

-- ----------------------------------------------------------------------------
-- Phase 2.3: digitChar d is an ASCII digit (under d < 10)
-- ----------------------------------------------------------------------------

-- Same pattern as `digitToNat-digitChar` / `charToDigit-digitChar`:
-- ten refl branches (primitive evaluation of `primIsDigit '0'..'9'`)
-- plus a suc-chain absurd on the catch-all (per
-- `feedback_literaltoobig_suc_chain.md`).
digitChar-isDigit : ∀ d → d < 10 → isDigit (digitChar d) ≡ true
digitChar-isDigit 0 _ = refl
digitChar-isDigit 1 _ = refl
digitChar-isDigit 2 _ = refl
digitChar-isDigit 3 _ = refl
digitChar-isDigit 4 _ = refl
digitChar-isDigit 5 _ = refl
digitChar-isDigit 6 _ = refl
digitChar-isDigit 7 _ = refl
digitChar-isDigit 8 _ = refl
digitChar-isDigit 9 _ = refl
digitChar-isDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- ----------------------------------------------------------------------------
-- Phase 2.4: All emitted characters are digits
-- ----------------------------------------------------------------------------

-- Every character in `showNat-chars-fuel f n` passes `isDigit`
-- (independent of fuel — `f = 0` returns `[]` vacuously).  Mirrors
-- the `with n / 10` case-split in the emitter: both branches emit
-- `digitChar (n % 10)` at the low position, and the `suc m` branch
-- has an IH-covered prefix to its left.
All-isDigit-showNat-chars-fuel : ∀ f n →
  All (λ c → isDigit c ≡ true) (showNat-chars-fuel f n)
All-isDigit-showNat-chars-fuel zero     _ = []
All-isDigit-showNat-chars-fuel (suc f') n with n / 10
... | zero  = digitChar-isDigit (n % 10) (m%n<n n 10) ∷ []
... | suc m = All-++⁺ (All-isDigit-showNat-chars-fuel f' (suc m))
                      (digitChar-isDigit (n % 10) (m%n<n n 10) ∷ [])

-- Specialisation at the public `showNat-chars n = showNat-chars-fuel
-- (suc n) n` entry point.
All-isDigit-showNat-chars : ∀ n →
  All (λ c → isDigit c ≡ true) (showNat-chars n)
All-isDigit-showNat-chars n = All-isDigit-showNat-chars-fuel (suc n) n

-- Every character in `showℕ-padded-chars w n` passes `isDigit`.
-- Structural recursion on `w`; no precondition on `n` needed — the
-- digit property is orthogonal to the width-bounded roundtrip.
All-isDigit-showℕ-padded-chars : ∀ w n →
  All (λ c → isDigit c ≡ true) (showℕ-padded-chars w n)
All-isDigit-showℕ-padded-chars zero    _ = []
All-isDigit-showℕ-padded-chars (suc w) n =
  All-++⁺ (All-isDigit-showℕ-padded-chars w (n / 10))
          (digitChar-isDigit (n % 10) (m%n<n n 10) ∷ [])

-- ----------------------------------------------------------------------------
-- Phase 2.5: manyHelper-satisfy-exhaust — the workhorse lemma
-- ----------------------------------------------------------------------------

-- Given enough fuel, `manyHelper (satisfy P)` on `xs ++ suffix` with
-- every `xs` character `P`-true and `suffix` at a stop boundary
-- returns `xs` and leaves `suffix` unconsumed (with a correctly
-- advanced position).
--
-- Six coverage cases after splitting on fuel / `xs` / `suffix`:
--   * fuel = 0, xs = [], suffix = []:             manyHelper short-
--     circuits on fuel before inspecting the parser; reduces to
--     `just (mkResult [] pos [])` directly.
--   * fuel = 0, xs = [], suffix = c ∷ cs:         same short-circuit.
--   * fuel = 0, xs = x ∷ xs':                     absurd via
--                                                  `suc _ ≤ 0`.
--   * fuel = suc n', xs = [], suffix = []:        satisfy fails on
--     empty input; manyHelper falls through the `nothing` branch.
--   * fuel = suc n', xs = [], suffix = c ∷ cs:    `rewrite h` (the
--     `P c ≡ false` component of `∷-stop`) makes satisfy return
--     `nothing`; manyHelper's `nothing` branch.
--   * fuel = suc n', xs = x ∷ xs':                inductive step.
--     Three-step rewrite: (1) `px : P x ≡ true` makes satisfy
--     return `just`; (2) `sameLengthᵇ-cons` discharges the zero-
--     progress guard to `false`; (3) IH resolves the recursive
--     manyHelper call.
manyHelper-satisfy-exhaust : (P : Char → Bool) (pos : Position)
  → (xs suffix : List Char)
  → All (λ c → P c ≡ true) xs
  → SuffixStops P suffix
  → (n : ℕ) → length xs ≤ n
  → manyHelper (satisfy P) pos (xs ++ₗ suffix) n
    ≡ just (mkResult xs (advancePositions pos xs) suffix)
manyHelper-satisfy-exhaust P pos []        []       _          _          zero     _            = refl
manyHelper-satisfy-exhaust P pos []        (c ∷ cs) _          _          zero     _            = refl
manyHelper-satisfy-exhaust P pos (x ∷ xs') _        _          _          zero     ()
manyHelper-satisfy-exhaust P pos []        []       _          _          (suc n') _            = refl
manyHelper-satisfy-exhaust P pos []        (c ∷ cs) _          (∷-stop h) (suc n') _
  rewrite h = refl
manyHelper-satisfy-exhaust P pos (x ∷ xs') suffix   (px ∷ pxs) ss         (suc n') (s≤s len≤)
  rewrite px
        | sameLengthᵇ-cons x (xs' ++ₗ suffix)
        | manyHelper-satisfy-exhaust P (advancePosition pos x) xs' suffix pxs ss n' len≤
  = refl

-- ----------------------------------------------------------------------------
-- Phase 2.6: many-fuel specialisation
-- ----------------------------------------------------------------------------

-- `many p pos input = manyHelper p pos input (length input)`.  For
-- `input = xs ++ suffix`, the fuel is `length (xs ++ suffix)`, which
-- is `≥ length xs` via `length-++ₗ` + `m≤m+n`.  This wrapper
-- specialises the exhaustion lemma to exactly the shape that
-- `some-satisfy-prefix` needs.
manyHelper-satisfy-exhaust-many : (P : Char → Bool) (pos : Position)
  → (xs suffix : List Char)
  → All (λ c → P c ≡ true) xs
  → SuffixStops P suffix
  → manyHelper (satisfy P) pos (xs ++ₗ suffix) (length (xs ++ₗ suffix))
    ≡ just (mkResult xs (advancePositions pos xs) suffix)
manyHelper-satisfy-exhaust-many P pos xs suffix pxs ss =
  manyHelper-satisfy-exhaust P pos xs suffix pxs ss
    (length (xs ++ₗ suffix)) len-xs≤len-xs++suffix
  where
    len-xs≤len-xs++suffix : length xs ≤ length (xs ++ₗ suffix)
    len-xs≤len-xs++suffix
      rewrite length-++ₗ xs {suffix}
      = m≤m+n (length xs) (length suffix)

-- ----------------------------------------------------------------------------
-- Phase 2.7: some-satisfy-prefix — the reusable entry point
-- ----------------------------------------------------------------------------

-- `some p = p ∷ many p` (in list form).  Applied to `(x ∷ xs') ++
-- suffix` with head `P`-true, tail `P`-true, and `suffix` at a stop
-- boundary, `some (satisfy P)` returns the whole prefix.  Two-step
-- rewrite: (1) `rewrite px` resolves the leading `satisfy` call
-- inside `<$>`/`<*>`; (2) `rewrite manyHelper-satisfy-exhaust-many`
-- resolves the recursive `many` call, letting the remaining `<$>`
-- reduce to the final `mkResult`.
--
-- Shared by `parseNatural-showNat-chars` (integer part) and the
-- fractional `some digit` call in `parseDecRat` — both use `P =
-- isDigit`.
some-satisfy-prefix : (P : Char → Bool) (pos : Position)
  → (x : Char) (xs' suffix : List Char)
  → P x ≡ true
  → All (λ c → P c ≡ true) xs'
  → SuffixStops P suffix
  → some (satisfy P) pos ((x ∷ xs') ++ₗ suffix)
    ≡ just (mkResult (x ∷ xs') (advancePositions pos (x ∷ xs')) suffix)
some-satisfy-prefix P pos x xs' suffix px pxs ss
  rewrite px
        | manyHelper-satisfy-exhaust-many P (advancePosition pos x) xs' suffix pxs ss
  = refl

-- ============================================================================
-- Phase 3.1: Non-emptiness and position/length lemmas
-- ============================================================================
--
-- Prerequisites for Part B's `parseNatural-showNat-chars` and Part C's
-- final roundtrip.  Three threads:
--
--   * `advancePositions-++` — position tracking distributes over `_++ₗ_`,
--     needed to align `advancePositions pos (intChars ++ₗ '.' ∷ fracChars)`
--     with the composed-parser's step-by-step position math.
--
--   * `length-showℕ-padded-chars` — the fractional part has exactly
--     `m = (a ⊔ b) ⊔ 1` characters, so `k = length fracChars = m` in
--     `buildDecRat`.  Used in Part C to identify the parser-rebuilt
--     exponents with the emitter's `m`.
--
--   * `*-nonempty` family — `showNat-chars n` and `showℕ-padded-chars
--     (suc w) n` are never empty.  Needed because `some (satisfy P)`
--     (= `parseNatural`, fractional `some digit`) requires a non-empty
--     prefix to succeed; `some-satisfy-prefix` expects `x ∷ xs'` shape.

advancePositions-++ : ∀ pos xs ys →
  advancePositions pos (xs ++ₗ ys) ≡ advancePositions (advancePositions pos xs) ys
advancePositions-++ pos []       ys = refl
advancePositions-++ pos (x ∷ xs) ys = advancePositions-++ (advancePosition pos x) xs ys

length-showℕ-padded-chars : ∀ w n → length (showℕ-padded-chars w n) ≡ w
length-showℕ-padded-chars zero    _ = refl
length-showℕ-padded-chars (suc w) n
  rewrite length-++ₗ (showℕ-padded-chars w (n / 10)) {digitChar (n % 10) ∷ []}
        | length-showℕ-padded-chars w (n / 10)
        | +-comm w 1
  = refl

++-snoc-nonempty : ∀ {A : Set} (xs : List A) (d : A) →
  ∃₂ λ x ys → xs ++ₗ d ∷ [] ≡ x ∷ ys
++-snoc-nonempty []       d = d , [] , refl
++-snoc-nonempty (x ∷ xs) d = x , xs ++ₗ d ∷ [] , refl

showNat-chars-fuel-nonempty : ∀ f n → 0 < f →
  ∃₂ λ x xs → showNat-chars-fuel f n ≡ x ∷ xs
showNat-chars-fuel-nonempty zero    _ ()
showNat-chars-fuel-nonempty (suc f) n _ with n / 10
... | zero  = digitChar (n % 10) , [] , refl
... | suc m = ++-snoc-nonempty (showNat-chars-fuel f (suc m)) (digitChar (n % 10))

showNat-chars-nonempty : ∀ n → ∃₂ λ x xs → showNat-chars n ≡ x ∷ xs
showNat-chars-nonempty n = showNat-chars-fuel-nonempty (suc n) n (s≤s z≤n)

showℕ-padded-chars-nonempty : ∀ w n → 0 < w →
  ∃₂ λ x xs → showℕ-padded-chars w n ≡ x ∷ xs
showℕ-padded-chars-nonempty zero    _ ()
showℕ-padded-chars-nonempty (suc w) n _ =
  ++-snoc-nonempty (showℕ-padded-chars w (n / 10)) (digitChar (n % 10))

-- ============================================================================
-- Phase 3.2: parseNatural reads back showNat-chars
-- ============================================================================
--
-- Wraps `some-satisfy-prefix` (Phase 2) with `parseNatural`'s `do`-block
-- continuation `foldl (λ acc d → acc * 10 + digitToNat d) 0`.  The fold
-- result reduces to `n` via `foldl-digitToNat-showNat-chars` (Phase 1).
--
-- The four-term `with` abstracts `showNat-chars n` alongside the three
-- lemmas that mention it (`-nonempty`, `All-isDigit-`, `foldl-`).  The
-- `(x , xs' , refl)` pattern on `-nonempty` forces `showNat-chars n ≡
-- x ∷ xs'`, which flows through the other two via abstraction: `All-`
-- unifies as `px ∷ pxs`, and `foldl-` keeps its equation as `fold-eq`.
-- The RHS `rewrite` chain then resolves `some` via the prefix lemma
-- and closes the fold via `fold-eq`.
parseNatural-showNat-chars : ∀ pos n (suffix : List Char) →
  SuffixStops isDigit suffix →
  parseNatural pos (showNat-chars n ++ₗ suffix)
    ≡ just (mkResult n (advancePositions pos (showNat-chars n)) suffix)
parseNatural-showNat-chars pos n suffix ss
  with showNat-chars n
     | showNat-chars-nonempty n
     | All-isDigit-showNat-chars n
     | foldl-digitToNat-showNat-chars n
... | .(x ∷ xs') | x , xs' , refl | px ∷ pxs | fold-eq
  rewrite some-satisfy-prefix isDigit pos x xs' suffix px pxs ss
        | fold-eq
  = refl

-- ============================================================================
-- Phase 3.3: canonicalizeDecRat-from-canonicalizeNat — sign-agnostic wrapper
-- ============================================================================
--
-- The direct `rewrite` route fails because `canonicalizeDecRat`'s
-- internal `with canonicalizeNat ∣ num ∣ a b in can-eq` does not
-- auto-step on abstract arguments.  Rewriting with the applied-lemma
-- `canonicalizeNat-scale-pos` targets `canonicalizeNat (...) ...` which
-- is not literally present in the goal (`canonicalizeDecRat` unfolds
-- into explicit `stripShared2-abs` / `stripShared5-abs` chains, not
-- back to `canonicalizeNat`).
--
-- Route 2: an explicit wrapper that takes `canonicalizeNat`'s value as
-- a hypothesis and produces `canonicalizeDecRat`'s output.  The proof
-- mirrors `canonicalizeDecRat`'s body with `with canonicalizeNat …`,
-- unifies via the hypothesis, and uses `refl` (the `.canonical` field
-- is irrelevant so equal numerical fields imply record equality).
-- Proof-irrelevant congruence on `mkDecRat`: three numerical
-- equalities imply record equality, regardless of the two
-- `.canonical` witnesses' types (which differ before the equality is
-- proven but share the numerical fields' equivalence class).
mkDecRat-≡ : ∀ n₁ n₂ a₁ a₂ b₁ b₂
  .{cx₁ : IsCanonical (∣ n₁ ∣) a₁ b₁}
  .{cx₂ : IsCanonical (∣ n₂ ∣) a₂ b₂} →
  n₁ ≡ n₂ → a₁ ≡ a₂ → b₁ ≡ b₂ →
  mkDecRat n₁ a₁ b₁ cx₁ ≡ mkDecRat n₂ a₂ b₂ cx₂
mkDecRat-≡ n₁ .n₁ a₁ .a₁ b₁ .b₁ refl refl refl = refl

-- From a known `canonicalizeNat` value, produce `canonicalizeDecRat`'s
-- output.  Sign-agnostic: works for both `ℤ+ _` and `ℤ-[1+ _ ]` by
-- routing the sign through `sign num ◃ _`.  Bridges
-- `canonicalizeNat-scale-pos` into the main roundtrip theorem.
-- `canonicalizeDecRat num a b` reduces (past its `with canonicalizeNat
-- … in can-eq`) into the triple of stripShared projections, because
-- `canonicalizeNat` itself is definitionally the nested stripShared
-- pair.  We bridge by rewriting each projection of the `can-eq`
-- hypothesis onto the three fields of the emitted `mkDecRat`.
-- `cx'` is explicit and irrelevant: caller supplies any proof of
-- IsCanonical on the canonicalised triple; `mkDecRat-≡` collapses
-- witnesses via irrelevance.
canonicalizeDecRat-from-canonicalizeNat : ∀ num a b n' a' b' →
  canonicalizeNat (∣ num ∣) a b ≡ (n' , a' , b') →
  .(cx' : IsCanonical (∣ sign num ◃ n' ∣) a' b') →
  canonicalizeDecRat num a b
    ≡ mkDecRat (sign num ◃ n') a' b' cx'
canonicalizeDecRat-from-canonicalizeNat num a b n' a' b' can-eq cx' =
  mkDecRat-≡ _ _ _ _ _ _
    (cong (λ tp → sign num ◃ proj₁ tp) can-eq)
    (cong (proj₁ ∘ proj₂) can-eq)
    (cong (proj₂ ∘ proj₂) can-eq)

-- Public canonicalisation bridge at budget `(m, m)` where `m = (a ⊔
-- b) ⊔ 1`.  Composes `canonicalizeNat-scale-pos` at `(p, q) = (m ∸ a,
-- m ∸ b)` with two `m∸n+n≡m` rewrites to align `(p + a)` → `m` and `(q
-- + b)` → `m`.  Cannot use `rewrite sym (m∸n+n≡m …)` on the goal: that
-- globally expands `m` into `(m ∸ a) + a`, including inside the `m ∸
-- a` and `m ∸ b` subterms, corrupting them.  The `cong₂ + trans`
-- direction does exactly one surgical rewrite on the budget arguments.
--
-- Factored out of `canonicalizeDecRat-scale-pos` so the main theorem's
-- `-[1+ k ]` neg branch can reuse it (via `sucn-scaled-suc`-supplied
-- `scaled-eq : scaledNum ≡ suc k`) without duplicating the trans/cong₂
-- routing.
canonicalizeNat-scale-pos-max : ∀ n a b →
  (h2 : 0 < a → 2 ∤ suc n) →
  (h5 : 0 < b → 5 ∤ suc n) →
  canonicalizeNat
    (suc n * 2 ^ (((a ⊔ b) ⊔ 1) ∸ a) * 5 ^ (((a ⊔ b) ⊔ 1) ∸ b))
    ((a ⊔ b) ⊔ 1) ((a ⊔ b) ⊔ 1)
    ≡ (suc n , a , b)
canonicalizeNat-scale-pos-max n a b h2 h5 =
  trans
    (cong₂ (canonicalizeNat (suc n * 2 ^ (m ∸ a) * 5 ^ (m ∸ b)))
           (sym (m∸n+n≡m {m} {a} a≤m))
           (sym (m∸n+n≡m {m} {b} b≤m)))
    (canonicalizeNat-scale-pos (suc n) a b h2 h5 (m ∸ a) (m ∸ b))
  where
    m = (a ⊔ b) ⊔ 1
    a≤m : a ≤ m
    a≤m = ≤-trans (m≤m⊔n a b) (m≤m⊔n (a ⊔ b) 1)
    b≤m : b ≤ m
    b≤m = ≤-trans (m≤n⊔m a b) (m≤m⊔n (a ⊔ b) 1)

-- Compose the wrapper with `canonicalizeNat-scale-pos-max` via the
-- sign-agnostic bridge `canonicalizeDecRat-from-canonicalizeNat`.
-- Specialised to the positive-sign emitter shape `ℤ+ (suc n · …)`; the
-- `-[1+ k ]` sign case is handled directly in the main theorem's neg
-- branch via `canonicalizeDecRat-from-canonicalizeNat` + `sucn-scaled-
-- suc` (which witnesses `scaledNum ≡ suc k`, forcing `applySign` to
-- emit `-[1+ k ]`).
canonicalizeDecRat-scale-pos : ∀ n a b →
  (h2 : 0 < a → 2 ∤ suc n) →
  (h5 : 0 < b → 5 ∤ suc n) →
  .(cx : IsCanonical (∣ ℤ+ suc n ∣) a b) →
  canonicalizeDecRat
    (ℤ+ (suc n * 2 ^ (((a ⊔ b) ⊔ 1) ∸ a) * 5 ^ (((a ⊔ b) ⊔ 1) ∸ b)))
    ((a ⊔ b) ⊔ 1) ((a ⊔ b) ⊔ 1)
    ≡ mkDecRat (ℤ+ suc n) a b cx
canonicalizeDecRat-scale-pos n a b h2 h5 cx
  = canonicalizeDecRat-from-canonicalizeNat
      (ℤ+ (suc n * 2 ^ (((a ⊔ b) ⊔ 1) ∸ a) * 5 ^ (((a ⊔ b) ⊔ 1) ∸ b)))
      ((a ⊔ b) ⊔ 1) ((a ⊔ b) ⊔ 1)
      (suc n) a b
      (canonicalizeNat-scale-pos-max n a b h2 h5)
      cx

-- ============================================================================
-- Phase 3.4: Canonicality extractors (positive-magnitude path)
-- ============================================================================
--
-- Extract divisibility witnesses from `IsCanonical (suc n) a b`.  Used
-- by the main theorem's `+ suc n` / `-[1+ n ]` cases to supply the
-- `h2 : 0 < a → 2 ∤ suc n` and `h5 : 0 < b → 5 ∤ suc n` preconditions
-- of `canonicalizeNat-scale-pos`.
--
-- `cx` is `.irrelevant`, so absurd branches close via `EmptyI.⊥-elim`.
-- Each `(a, b)` subcase dispatches on the corresponding `∣?` decision.
-- The `(suc _, suc _)` branch exploits the asymmetry in `isCanonicalᵇ`'s
-- `∧` ordering (2 first, 5 second): splitting on `2 ∣?` alone suffices
-- for `2∤` (left-biased `false ∧ _` absorbs), but `5 ∤` needs both
-- splits because `5 ∣?` is the right conjunct and `_∧_` on Bool does
-- not reduce without the left argument.
isCanonicalᵇ-pos-2∤ : ∀ n a b → .(cx : IsCanonical (suc n) a b) →
  0 < a → 2 ∤ suc n
isCanonicalᵇ-pos-2∤ n zero    _       _  ()
isCanonicalᵇ-pos-2∤ n (suc _) zero    cx _ with 2 ∣? suc n
... | no  h = h
... | yes _ = EmptyI.⊥-elim cx
isCanonicalᵇ-pos-2∤ n (suc _) (suc _) cx _ with 2 ∣? suc n
... | no  h = h
... | yes _ = EmptyI.⊥-elim cx

isCanonicalᵇ-pos-5∤ : ∀ n a b → .(cx : IsCanonical (suc n) a b) →
  0 < b → 5 ∤ suc n
isCanonicalᵇ-pos-5∤ n _       zero    _  ()
isCanonicalᵇ-pos-5∤ n zero    (suc _) cx _ with 5 ∣? suc n
... | no  h = h
... | yes _ = EmptyI.⊥-elim cx
isCanonicalᵇ-pos-5∤ n (suc _) (suc _) cx _ with 2 ∣? suc n | 5 ∣? suc n
... | _     | no  h = h
... | yes _ | yes _ = EmptyI.⊥-elim cx
... | no  _ | yes _ = EmptyI.⊥-elim cx

-- ============================================================================
-- Phase 3.5: Digit-dash discrimination + optional-dash fail-through
-- ============================================================================
--
-- For the non-negative sign case the main theorem needs to show that
-- `optional (char '-')` returns `nothing` without consuming the first
-- character when that character is not `'-'`.  The first character of
-- `showNat-chars (suc n / 10^k)` is always `digitChar d` for some
-- `d < 10` (never `'0'` via the absurd default, since the precondition
-- rules that out) — and `digitChar d ≈ᵇ '-'` is a concrete Boolean
-- reduction on ASCII code points.

-- Each `digitChar 0..9` gives a concrete `Char`, and `c ≈ᵇ '-'` reduces
-- via `toℕ c ≡ᵇ 45` on the `Agda.Builtin.Char` primitives.  Ten
-- refl-closed cases + a single absurd catch-all mirror
-- `digitChar-isDigit` at line 400.
digitChar-≢-dash : ∀ d → d < 10 → (digitChar d ≈ᵇ '-') ≡ false
digitChar-≢-dash 0 _ = refl
digitChar-≢-dash 1 _ = refl
digitChar-≢-dash 2 _ = refl
digitChar-≢-dash 3 _ = refl
digitChar-≢-dash 4 _ = refl
digitChar-≢-dash 5 _ = refl
digitChar-≢-dash 6 _ = refl
digitChar-≢-dash 7 _ = refl
digitChar-≢-dash 8 _ = refl
digitChar-≢-dash 9 _ = refl
digitChar-≢-dash (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- Given a non-dash leading character, `optional (char '-')` leaves
-- position and input unchanged and returns `nothing`.  Trace:
--
--   optional (char '-') pos (x ∷ xs')
--     = (just <$> char '-') <|> pure nothing) pos (x ∷ xs')
--     = case char '-' pos (x ∷ xs') of
--         nothing        → pure nothing pos (x ∷ xs')
--         just result    → just (mkResult (just …) …)
--     = case satisfy (λ c → c ≈ᵇ '-') pos (x ∷ xs') of
--         -- (x ≈ᵇ '-') = false by hypothesis ⟹ satisfy returns nothing
--         nothing        → just (mkResult nothing pos (x ∷ xs'))
--
-- `rewrite eq` is enough: the normalised goal mentions `x ≈ᵇ '-'`
-- exactly once (inside the nested `satisfy`/`<$>`/`<|>` unfolding),
-- and after rewriting both sides reduce to the same constructor tree.
optional-dash-fail : ∀ pos x xs' → (x ≈ᵇ '-') ≡ false →
  optional (char '-') pos (x ∷ xs')
    ≡ just (mkResult nothing pos (x ∷ xs'))
optional-dash-fail pos x xs' eq rewrite eq = refl

-- ============================================================================
-- Phase 3.6: Padded-fraction `some digit` reader (named wrapper)
-- ============================================================================
--
-- General-suffix padded-fraction reader.  Takes the `0 < w` precondition
-- directly (matches `showℕ-padded-chars-nonempty`'s signature) so the main
-- theorem can apply it at `w = (a ⊔ b) ⊔ 1` without first needing to
-- rewrite the width into `suc _` form.
some-digit-showℕ-padded-chars : ∀ w n pos (suffix : List Char) →
  0 < w → SuffixStops isDigit suffix →
  some digit pos (showℕ-padded-chars w n ++ₗ suffix)
    ≡ just (mkResult (showℕ-padded-chars w n)
                     (advancePositions pos (showℕ-padded-chars w n))
                     suffix)
some-digit-showℕ-padded-chars w n pos suffix 0<w ss
  with showℕ-padded-chars w n
     | showℕ-padded-chars-nonempty w n 0<w
     | All-isDigit-showℕ-padded-chars w n
... | .(x ∷ xs') | x , xs' , refl | px ∷ pxs
  = some-satisfy-prefix isDigit pos x xs' suffix px pxs ss

-- ============================================================================
-- Phase 3.7: Nonzero positivity of the scaled magnitude
-- ============================================================================
--
-- `canonicalizeNat-scale-pos` is stated on `suc n`, but the
-- emitter's `scaledNum` in the positive case is `suc n * 2^(m-a) *
-- 5^(m-b)`.  To reuse the scale-pos lemma on the canonicalisation
-- side, we need `scaledNum = suc k` for some `k` — i.e., `scaledNum
-- ≠ 0`.  This follows from the product being `NonZero` since each
-- factor is.
--
-- The `with ... in scaled-eq` pattern provides the definitional
-- equation that lets the `suc k` branch return `k , refl` directly.
-- The `zero` branch is closed by contradicting the product's non-
-- zeroness (`≢-nonZero⁻¹` applied to the constructed `NonZero`
-- proof).  Instance arguments resolve `NonZero (suc n)` automatically;
-- we supply `NonZero (2^p)` / `NonZero (5^q)` via `m^n≢0`, and
-- compose through `m*n≢0`.
open import Data.Nat.Base using (≢-nonZero⁻¹)
open import Data.Nat.Properties using (m*n≢0; m^n≢0)

sucn-scaled-suc : ∀ n p q → ∃ λ k → suc n * 2 ^ p * 5 ^ q ≡ suc k
sucn-scaled-suc n p q with suc n * 2 ^ p * 5 ^ q in scaled-eq
... | zero  = ⊥-elim (≢-nonZero⁻¹ (suc n * 2 ^ p * 5 ^ q) {{nz}} scaled-eq)
  where
    nz : NonZero (suc n * 2 ^ p * 5 ^ q)
    nz = m*n≢0 (suc n * 2 ^ p) (5 ^ q)
                {{m*n≢0 (suc n) (2 ^ p) {{_}} {{m^n≢0 2 p}}}}
                {{m^n≢0 5 q}}
... | suc k = k , refl

-- ============================================================================
-- Phase 3.8: showNat-chars head digit
-- ============================================================================
--
-- The first character of `showNat-chars n` is `digitChar d` for some
-- `d < 10`.  Used by the main theorem's sign-branch discrimination:
-- the `(+ n)` case needs `optional (char '-')` to fail without
-- consuming, which requires the first character of the emitted
-- magnitude to not be `'-'`.  `digitChar-≢-dash` turns `d < 10` into
-- `digitChar d ≈ᵇ '-' ≡ false`, which `optional-dash-fail` consumes.
--
-- Structurally recursive on fuel; both branches of `with n / 10`
-- emit `digitChar (n % 10)` somewhere.  The `zero` branch emits it
-- as the whole output (head = last = only); the `suc m` branch
-- recurses then snoc-appends it, so the head comes from the IH.
showNat-chars-fuel-head : ∀ f n → 0 < f →
  ∃₂ λ d tail → d < 10 × showNat-chars-fuel f n ≡ digitChar d ∷ tail
showNat-chars-fuel-head (suc f') n _ with n / 10
... | zero  = n % 10 , [] , m%n<n n 10 , refl
... | suc m with f'
...   | zero    = n % 10 , [] , m%n<n n 10 , refl
...   | suc f'' with showNat-chars-fuel-head (suc f'') (suc m) (s≤s z≤n)
...     | d , tail , d<10 , eq =
            d , tail ++ₗ digitChar (n % 10) ∷ []
              , d<10
              , cong (_++ₗ digitChar (n % 10) ∷ []) eq

showNat-chars-head : ∀ n →
  ∃₂ λ d tail → d < 10 × showNat-chars n ≡ digitChar d ∷ tail
showNat-chars-head n = showNat-chars-fuel-head (suc n) n (s≤s z≤n)

-- Packaged form: the head character is not `'-'`.  Consumed directly
-- by `optional-dash-fail` inside the `+` sign branch of the main
-- theorem.
showNat-chars-head-≢-dash : ∀ n →
  ∃₂ λ x tail → showNat-chars n ≡ x ∷ tail × (x ≈ᵇ '-') ≡ false
showNat-chars-head-≢-dash n with showNat-chars-head n
... | d , tail , d<10 , eq =
      digitChar d , tail , eq , digitChar-≢-dash d d<10

-- ============================================================================
-- Phase 3.9: Suffix-exhausting parser variants + scalar helpers
-- ============================================================================
--
-- These variants correspond to Phase 2.5 / 2.7 but for the `suffix =
-- []` case.  Directly unfolding `some-satisfy-prefix P pos x xs' []
-- px pxs []-stop` would succeed, but the returned parser call shape
-- is `some (satisfy P) pos ((x ∷ xs') ++ₗ [])`, which is
-- definitionally `x ∷ (xs' ++ₗ [])` — not `x ∷ xs'`.  The outer
-- `(xs' ++ₗ [])` does not reduce under `--without-K` abstraction, so
-- the main theorem's final `some digit` call on `fracChars` needs a
-- `-all` variant that threads `[]` from the start without appealing
-- to `++-identityʳ`.
--
-- Same structural recursion as Phase 2.5, with the `++ₗ suffix`
-- dropped throughout.
manyHelper-satisfy-exhaust-all : (P : Char → Bool) (pos : Position)
  → (xs : List Char)
  → All (λ c → P c ≡ true) xs
  → (n : ℕ) → length xs ≤ n
  → manyHelper (satisfy P) pos xs n
    ≡ just (mkResult xs (advancePositions pos xs) [])
manyHelper-satisfy-exhaust-all P pos []        _          zero     _            = refl
manyHelper-satisfy-exhaust-all P pos (x ∷ xs') _          zero     ()
manyHelper-satisfy-exhaust-all P pos []        _          (suc n') _            = refl
manyHelper-satisfy-exhaust-all P pos (x ∷ xs') (px ∷ pxs) (suc n') (s≤s len≤)
  rewrite px
        | sameLengthᵇ-cons x xs'
        | manyHelper-satisfy-exhaust-all P (advancePosition pos x) xs' pxs n' len≤
  = refl

-- Entry point at the public `many` (length-fuel) specialisation.
-- Parallel to `some-satisfy-prefix` but at empty suffix: both use the
-- `px` / `sameLengthᵇ-cons` / inner-exhaust rewrite sequence.
some-satisfy-prefix-all : (P : Char → Bool) (pos : Position)
  → ∀ x (xs' : List Char)
  → P x ≡ true
  → All (λ c → P c ≡ true) xs'
  → some (satisfy P) pos (x ∷ xs')
    ≡ just (mkResult (x ∷ xs') (advancePositions pos (x ∷ xs')) [])
some-satisfy-prefix-all P pos x xs' px pxs
  rewrite px
        | manyHelper-satisfy-exhaust-all P (advancePosition pos x) xs'
            pxs (length xs') ≤-refl
  = refl

-- ----------------------------------------------------------------------------
-- Phase 3.9.b: Padded-fraction reader at empty suffix
-- ----------------------------------------------------------------------------
--
-- `some-digit-showℕ-padded-chars` (Phase 3.6) reads back `showℕ-
-- padded-chars w n ++ₗ suffix`.  When `suffix = []`, we want the LHS
-- at `showℕ-padded-chars w n` literally — not `++ₗ []`.  Same
-- derivation as Phase 3.6 but via `some-satisfy-prefix-all`.
some-digit-showℕ-padded-chars-end : ∀ w n pos →
  0 < w →
  some digit pos (showℕ-padded-chars w n)
    ≡ just (mkResult (showℕ-padded-chars w n)
                     (advancePositions pos (showℕ-padded-chars w n))
                     [])
some-digit-showℕ-padded-chars-end w n pos 0<w
  with showℕ-padded-chars w n
     | showℕ-padded-chars-nonempty w n 0<w
     | All-isDigit-showℕ-padded-chars w n
... | .(x ∷ xs') | x , xs' , refl | px ∷ pxs
  = some-satisfy-prefix-all isDigit pos x xs' px pxs

-- ----------------------------------------------------------------------------
-- Phase 3.9.c: Scalar helpers (budget positivity + '.' non-digit)
-- ----------------------------------------------------------------------------

-- The emitter's budget is `m = (a ⊔ b) ⊔ 1`, strictly positive by
-- construction (the `⊔ 1` lifts the min above zero).  Consumed as the
-- `0 < w` precondition of `some-digit-showℕ-padded-chars-end` inside
-- the main theorem's `some digit` step, and as the width-lower-bound
-- for `showℕ-padded-chars-nonempty`.
0<[a⊔b]⊔1 : ∀ a b → 0 < (a ⊔ b) ⊔ 1
0<[a⊔b]⊔1 a b = m≤n⊔m (a ⊔ b) 1

-- `'.'` is not a digit: the primitive `isDigit '.'` reduces to `false`
-- (ASCII 46 is outside '0'..'9').  Packaged as a named lemma because
-- the main theorem consumes it inside a `∷-stop` constructor argument
-- where Agda needs the equation literally, not via primitive
-- evaluation under abstraction.
isDigit-dot-false : isDigit '.' ≡ false
isDigit-dot-false = refl

-- ----------------------------------------------------------------------------
-- Phase 3.9.d: Arithmetic bridge — `rawAbs ≡ scaledNum`
-- ----------------------------------------------------------------------------
--
-- `buildDecRat` reassembles `rawAbs = intPart * 10^k + fracVal`.
-- When `intPart = scaledNum / scale`, `fracVal = scaledNum % scale`,
-- and `k = m` (so `scale = 10^m`), this expression equals
-- `scaledNum`.  Direct consequence of the division-remainder identity
-- `m ≡ m % n + (m / n) * n` (stdlib `m≡m%n+[m/n]*n`) after `+-comm`.
rawAbs≡scaledNum : ∀ scaledNum m .{{_ : NonZero (10 ^ m)}} →
  (scaledNum / 10 ^ m) * 10 ^ m + scaledNum % 10 ^ m ≡ scaledNum
rawAbs≡scaledNum scaledNum m =
  trans (+-comm ((scaledNum / 10 ^ m) * 10 ^ m) (scaledNum % 10 ^ m))
        (sym (m≡m%n+[m/n]*n scaledNum (10 ^ m)))

-- ----------------------------------------------------------------------------
-- Phase 3.9.e: Symbolic wrappers that keep `showNat-chars n` un-destructured
-- ----------------------------------------------------------------------------
--
-- The main theorem wants to `rewrite` with `optional-dash-fail` and
-- `some-digit-showℕ-padded-chars-end` in sequence.  Both lemmas want
-- the parser's input argument to be the emitted characters literally
-- — not the destructured `x ∷ xs'` form.  `optional-dash-fail`'s
-- signature forces the call site to destructure `showNat-chars n ≡ x
-- ∷ xs'` via `showNat-chars-head-≢-dash`, which leaks the `x ∷ xs'`
-- shape into the goal and breaks subsequent rewrites that expect
-- `showNat-chars n` symbolically.
--
-- Workaround: this wrapper quarantines the destructure.  Its LHS
-- mentions `showNat-chars n` symbolically; internally it does the
-- `with`-abstraction on `showNat-chars-head-≢-dash n` and applies
-- `optional-dash-fail` in the destructured branch.  From the main
-- theorem's perspective, only `showNat-chars n ++ₗ rest` appears in
-- the rewrite LHS, and subsequent lemmas that mention
-- `showNat-chars n` still unify.
optional-dash-fail-on-showNat : ∀ pos n rest →
  optional (char '-') pos (showNat-chars n ++ₗ rest)
    ≡ just (mkResult nothing pos (showNat-chars n ++ₗ rest))
optional-dash-fail-on-showNat pos n rest
  with showNat-chars n | showNat-chars-head-≢-dash n
... | .(x ∷ tail) | x , tail , refl , ≢-dash
    = optional-dash-fail pos x (tail ++ₗ rest) ≢-dash

-- `optional (char '-')` on a `'-' ∷ rest` input consumes the dash and
-- returns `just '-'`.  Used by the neg sign branch of the main theorem.
-- Pure definitional reduction: `'-' ≈ᵇ '-'` evaluates to `true` on the
-- Agda.Builtin.Char primitives, and the `optional`/`<$>`/`<|>` chain
-- threads the result through to `just (just '-')`.
optional-dash-succ : ∀ pos (rest : List Char) →
  optional (char '-') pos ('-' ∷ rest)
    ≡ just (mkResult (just '-') (advancePosition pos '-') rest)
optional-dash-succ _ _ = refl

-- ----------------------------------------------------------------------------
-- Phase 3.11: Arithmetic bindings for Phase 4
-- ----------------------------------------------------------------------------
--
-- `emitMagnitude-chars` carries its `m` / `scaledNum` / `scale` as
-- internal `let`-bindings.  The +suc and neg branches in Phase 4 need
-- those names in `rewrite` clauses to line up with the parser's
-- reductions.  Agda 2.8 does not put `where`-bound names in scope for
-- `rewrite` clauses, so the bindings are lifted to private module-level
-- definitions here.  Each unfolds definitionally to the same normal form
-- as the corresponding `let` inside `emitMagnitude-chars`, so the rewrite
-- LHS shapes match without extra conversion lemmas.
-- NonZero witness used throughout this section.  NOT declared `instance`:
-- when the `rewrite` clauses in Phase 4 abstract the goal, Agda's unifier
-- tries to re-resolve any in-scope instance search against unknown
-- `NonZero (10 ^ _n)` constraints and fails (the `^` operator is not
-- injective in stdlib — `10 ^ _n = 10 ^ (a ⊔ b ⊔ 1)` is unsolvable
-- through instance resolution).  Passing the witness *explicitly* at
-- `mag-quot` / `mag-rem` definition sites bakes in the NonZero as a
-- concrete argument, so the with-abstracted goals in Phase 4 never
-- re-search instances.
10^n≢0 : ∀ n → NonZero (10 ^ n)
10^n≢0 n = m^n≢0 10 n

private
  mag-m : ℕ → ℕ → ℕ
  mag-m a b = (a ⊔ b) ⊔ 1

  mag-scaledNum : ℕ → ℕ → ℕ → ℕ
  mag-scaledNum n a b = n * 2 ^ (mag-m a b ∸ a) * 5 ^ (mag-m a b ∸ b)

  mag-scale : ℕ → ℕ → ℕ
  mag-scale a b = 10 ^ mag-m a b

  -- Quotient and remainder wrappers — elaborate `_/_` / `_%_` with an
  -- explicit NonZero witness at this definition site.  Downstream uses
  -- (including the Phase 4 rewrite chains) never trigger further
  -- instance resolution, so the "instance unresolvable inside rewrite-
  -- generated with-function" error does not arise even when `/` / `%`
  -- appear deeply inside the abstracted goal shape.
  mag-quot : ℕ → ℕ → ℕ → ℕ
  mag-quot n a b = _/_ (mag-scaledNum n a b) (mag-scale a b) ⦃ 10^n≢0 (mag-m a b) ⦄

  mag-rem : ℕ → ℕ → ℕ → ℕ
  mag-rem n a b = _%_ (mag-scaledNum n a b) (mag-scale a b) ⦃ 10^n≢0 (mag-m a b) ⦄

  mag-fracChars : ℕ → ℕ → ℕ → List Char
  mag-fracChars n a b = showℕ-padded-chars (mag-m a b) (mag-rem n a b)

-- `emitMagnitude-chars` unfolds to the mag-* shape.  Should hold by
-- `refl` (definitional unfolding of the `let` bindings to the module-
-- level names above — same ℕ terms at normal form).  If this fails, the
-- rewrite chain in Phase 4 needs this as an explicit rewrite step.
emitMagnitude-chars-mag : ∀ n a b →
  emitMagnitude-chars n a b
    ≡ showNat-chars (mag-quot n a b)
        ++ₗ '.' ∷ mag-fracChars n a b
emitMagnitude-chars-mag _ _ _ = refl

-- `build-eq-+suc` / `build-eq-neg` — `buildDecRat` on the emitter-shape
-- inputs reconstructs the original canonical record.  Lifted to module-
-- level (out of `parseDecRat-roundtrip-+suc`'s / `-neg`'s `where` block)
-- because Agda 2.8 does not put `where`-bound names in scope for
-- `rewrite` clauses, and each appears as the last step in its branch's
-- outer rewrite chain.
--
-- Shared inner structure:
--   * `length-showℕ-padded-chars` folds `length fracChars → m`.
--   * `parseDigitList-showℕ-padded-chars m (… % 10^m) (m%n<n)` replays
--     the fractional parse to give back `scaledNum % 10^m`.
--   * `rawAbs≡scaledNum` glues `(q · 10^m + r) ≡ scaledNum`.
-- Then +suc closes via `canonicalizeDecRat-scale-pos`; neg closes via a
-- `sucn-scaled-suc`-witnessed `scaledNum ≡ suc k`, transporting through
-- `applySign (just '-')` and `canonicalizeDecRat-from-canonicalizeNat`.
-- Proof strategy: avoid top-level `rewrite` because its with-function
-- abstraction makes the instance resolution for `NonZero (10 ^ _)` in
-- the goal unsolvable (Agda unifier cannot invert `10 ^ _n = 10 ^ k`).
-- Instead, chain three `cong`s (folding `length fc → m`, `parseDigitList
-- fc → r`, `q * 10^m + r → scaledNum`) then close by `canonicalizeDecRat-
-- scale-pos`.  Each `cong` introduces a fresh lambda, so instance
-- resolution happens once per lemma at its call site.
build-eq-+suc : ∀ n a b .(cx : IsCanonical (suc n) a b) →
  buildDecRat nothing (mag-quot (suc n) a b) (mag-fracChars (suc n) a b)
  ≡ mkDecRat (ℤ+ suc n) a b cx
build-eq-+suc n a b cx =
  trans (cong (λ k → canonicalizeDecRat
                       (ℤ+ (mag-quot (suc n) a b * 10 ^ k
                              + parseDigitList (mag-fracChars (suc n) a b)))
                       k k)
              len-eq)
    (trans (cong (λ v → canonicalizeDecRat
                          (ℤ+ (mag-quot (suc n) a b * 10 ^ mag-m a b + v))
                          (mag-m a b) (mag-m a b))
                 pdl-eq)
      (trans (cong (λ x → canonicalizeDecRat (ℤ+ x) (mag-m a b) (mag-m a b))
                   raw-eq)
             (canonicalizeDecRat-scale-pos n a b
                (isCanonicalᵇ-pos-2∤ n a b cx)
                (isCanonicalᵇ-pos-5∤ n a b cx)
                cx)))
  where
    len-eq : length (mag-fracChars (suc n) a b) ≡ mag-m a b
    len-eq = length-showℕ-padded-chars (mag-m a b) (mag-rem (suc n) a b)
    pdl-eq : parseDigitList (mag-fracChars (suc n) a b) ≡ mag-rem (suc n) a b
    pdl-eq = parseDigitList-showℕ-padded-chars (mag-m a b) (mag-rem (suc n) a b)
               (m%n<n (mag-scaledNum (suc n) a b) (mag-scale a b) ⦃ 10^n≢0 (mag-m a b) ⦄)
    raw-eq : mag-quot (suc n) a b * 10 ^ mag-m a b + mag-rem (suc n) a b
             ≡ mag-scaledNum (suc n) a b
    raw-eq = rawAbs≡scaledNum (mag-scaledNum (suc n) a b) (mag-m a b) ⦃ 10^n≢0 (mag-m a b) ⦄

build-eq-neg : ∀ n a b .(cx : IsCanonical (suc n) a b) →
  buildDecRat (just '-') (mag-quot (suc n) a b) (mag-fracChars (suc n) a b)
  ≡ mkDecRat ℤ-[1+ n ] a b cx
build-eq-neg n a b cx =
  trans (cong (λ k → canonicalizeDecRat
                       (applySign (just '-')
                          (mag-quot (suc n) a b * 10 ^ k
                             + parseDigitList (mag-fracChars (suc n) a b)))
                       k k)
              len-eq)
    (trans (cong (λ v → canonicalizeDecRat
                          (applySign (just '-')
                             (mag-quot (suc n) a b * 10 ^ mag-m a b + v))
                          (mag-m a b) (mag-m a b))
                 pdl-eq)
      (trans (cong (λ x → canonicalizeDecRat
                            (applySign (just '-') x)
                            (mag-m a b) (mag-m a b))
                   raw-eq)
             (neg-helper (sucn-scaled-suc n (mag-m a b ∸ a) (mag-m a b ∸ b)))))
  where
    len-eq : length (mag-fracChars (suc n) a b) ≡ mag-m a b
    len-eq = length-showℕ-padded-chars (mag-m a b) (mag-rem (suc n) a b)
    pdl-eq : parseDigitList (mag-fracChars (suc n) a b) ≡ mag-rem (suc n) a b
    pdl-eq = parseDigitList-showℕ-padded-chars (mag-m a b) (mag-rem (suc n) a b)
               (m%n<n (mag-scaledNum (suc n) a b) (mag-scale a b) ⦃ 10^n≢0 (mag-m a b) ⦄)
    raw-eq : mag-quot (suc n) a b * 10 ^ mag-m a b + mag-rem (suc n) a b
             ≡ mag-scaledNum (suc n) a b
    raw-eq = rawAbs≡scaledNum (mag-scaledNum (suc n) a b) (mag-m a b) ⦃ 10^n≢0 (mag-m a b) ⦄

    -- `applySign (just '-') scaledNum` doesn't reduce until `scaledNum
    -- ≡ suc k` is witnessed.  `sucn-scaled-suc` supplies that witness;
    -- `cong` transports through `applySign` to give `canonicalizeDecRat
    -- -[1+ k ] m m` on the RHS.  The final step is `canonicalizeDecRat-
    -- from-canonicalizeNat` with a proof obtained by rewriting
    -- `canonicalizeNat-scale-pos-max` along `sym scaled-eq`.
    neg-helper : (∃ λ k → mag-scaledNum (suc n) a b ≡ suc k) →
                 canonicalizeDecRat
                   (applySign (just '-') (mag-scaledNum (suc n) a b))
                   (mag-m a b) (mag-m a b)
                   ≡ mkDecRat ℤ-[1+ n ] a b cx
    neg-helper (k , scaled-eq) =
      trans (cong (λ x → canonicalizeDecRat (applySign (just '-') x)
                                            (mag-m a b) (mag-m a b))
                  scaled-eq)
            (canonicalizeDecRat-from-canonicalizeNat
              ℤ-[1+ k ] (mag-m a b) (mag-m a b) (suc n) a b
              (trans (cong (λ x → canonicalizeNat x (mag-m a b) (mag-m a b))
                           (sym scaled-eq))
                     (canonicalizeNat-scale-pos-max n a b
                       (isCanonicalᵇ-pos-2∤ n a b cx)
                       (isCanonicalᵇ-pos-5∤ n a b cx)))
              cx)

-- ============================================================================
-- Phase 4: parseDecRat roundtrip — per-sign branches
-- ============================================================================
--
-- Three mirror-image theorems, one per `showDecRat-dec-chars` sign
-- clause (`+ zero`, `+ suc n`, `-[1+ n ]`).  Pattern-match on the
-- `mkDecRat` numerator at the top-level dispatcher (`parseDecRat-
-- roundtrip`) to route to the right branch.  The parser trace is
-- shared: `optional dash → parseNatural → char '.' → some digit →
-- buildDecRat`; each branch differs only in the sign-specific
-- `optional-dash-*` call and the `applySign` + canonicalisation
-- arithmetic at the tail.
--
-- Arithmetic bridge (same for all three branches up to sign):
--   * `length-showℕ-padded-chars`   collapses `length fracChars → m`.
--   * `parseDigitList-showℕ-padded-chars` + `m%n<n`   reconstructs
--     the fractional-part value as `scaledNum % 10^m`.
--   * `rawAbs≡scaledNum`            glues `(q · 10^m + r) ≡ scaledNum`.
--   * `canonicalizeDecRat-scale-pos` (+suc) or
--     `canonicalizeDecRat-from-canonicalizeNat` + `canonicalizeNat-
--     scale-pos-max` + `sucn-scaled-suc` (neg)   close the
--     canonicalisation step.
--   * `advancePositions-++` aligns the step-by-step parser position
--     chain with the RHS's whole-emit-string position.

-- ----------------------------------------------------------------------------
-- Phase 4: Shared bind-chain helpers
-- ----------------------------------------------------------------------------
--
-- `bind-just-step` + `past-dot-char-dot-eq` let Phase 4's per-sign branches
-- advance `parseDecRat`'s `_>>=_` chain without `rewrite`.  `rewrite` fails
-- under `--without-K` here because the goal contains `div-helper` with-
-- abstractions (via `advancePositions pos (showDecRat-dec-chars …)` in the
-- RHS and `parseNatural`/`some digit` in the LHS); the induced `refl`
-- pattern-match on `X ≡ X` where `X` contains a with-abstracted subterm
-- requires K to eliminate.  `bind-just-step` sidesteps this by performing
-- the `with p pos input | eq` abstraction at a fresh variable, so the
-- internal `refl` sees only `variable ≡ just (mkResult …)` (no with-
-- abstraction exposure in the equation's type).
--
-- Generic `_>>=_` reduction lemma: if a parser propositionally returns
-- `just (mkResult v p' i')` at a given pos/input, the bind reduces to
-- the continuation at `v`, `p'`, `i'`.
bind-just-step : ∀ {A B : Set} (p : Parser A) (f : A → Parser B)
  (pos : Position) (input : List Char) v p' i' →
  p pos input ≡ just (mkResult v p' i') →
  (p >>= f) pos input ≡ f v p' i'
bind-just-step p f pos input v p' i' eq
  with p pos input | eq
... | just .(mkResult v p' i') | refl = refl

-- `char '.'` on `'.' ∷ xs` reduces definitionally; expose that via a
-- generic-`rest` lemma so specific instances compose via `trans` without
-- tripping `div-helper` normalisation in the goal.  Kept generic in `neg`
-- so both `-neg` and `-+suc` branches share it.
past-dot-char-dot-eq :
  ∀ (neg : Maybe Char) (nₚ : ℕ) (pos : Position) (fracChars : List Char) →
  (char '.' >>= λ _ → some digit >>= λ fd →
     pure (buildDecRat neg nₚ fd))
    pos ('.' ∷ fracChars)
  ≡ (some digit >>= λ fd →
       pure (buildDecRat neg nₚ fd))
    (advancePosition pos '.') fracChars
past-dot-char-dot-eq _ _ _ _ = refl

-- ----------------------------------------------------------------------------
-- Phase 4.1: `+ suc n` case
-- ----------------------------------------------------------------------------
parseDecRat-roundtrip-+suc : ∀ n a b pos
  .(cx : IsCanonical (suc n) a b) →
  parseDecRat pos (showDecRat-dec-chars (mkDecRat (ℤ+ suc n) a b cx))
    ≡ just (mkResult (mkDecRat (ℤ+ suc n) a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat (ℤ+ suc n) a b cx)))
                     [])
-- Structure mirrors `-neg` below.  Differences:
--   * Input has no `'-'` prefix, so `optional (char '-')` returns
--     `just (mkResult nothing pos emag)` via `optional-dash-fail-on-showNat`
--     (propositional equality, not `refl` — hence the `bind-just-step`).
--   * `neg = nothing` threads through `buildDecRat`; `build-eq-+suc` closes
--     the canonicalisation arithmetic.
--   * No `'-'` in position arithmetic — `advancePositions-++` needs only the
--     two-piece split `showNat-chars ++ '.' ∷ mag-fracChars`.
parseDecRat-roundtrip-+suc n a b pos cx =
  trans step-dash-fail
    (trans step-parseNat
      (trans step-some-digit
        (cong₂ (λ v p → just (mkResult v p []))
               (build-eq-+suc n a b cx)
               pos-eq)))
  where
    posAfterNat : Position
    posAfterNat = advancePositions pos (showNat-chars (mag-quot (suc n) a b))

    posAfterDot : Position
    posAfterDot = advancePosition posAfterNat '.'

    posAfterFrac : Position
    posAfterFrac = advancePositions posAfterDot (mag-fracChars (suc n) a b)

    step-dash-fail :
      parseDecRat pos (emitMagnitude-chars (suc n) a b)
      ≡ (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing nₚ fd))
        pos (emitMagnitude-chars (suc n) a b)
    step-dash-fail =
      bind-just-step (optional (char '-'))
                     (λ neg → parseNatural >>= λ nₚ → char '.' >>= λ _ →
                              some digit >>= λ fd →
                              pure (buildDecRat neg nₚ fd))
                     pos (emitMagnitude-chars (suc n) a b)
                     nothing pos (emitMagnitude-chars (suc n) a b)
                     (optional-dash-fail-on-showNat pos
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b))

    step-parseNat :
      (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat nothing nₚ fd))
        pos (emitMagnitude-chars (suc n) a b)
      ≡ (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b)
    step-parseNat =
      bind-just-step parseNatural
                     (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                              pure (buildDecRat nothing nₚ fd))
                     pos (emitMagnitude-chars (suc n) a b)
                     (mag-quot (suc n) a b) posAfterNat
                     ('.' ∷ mag-fracChars (suc n) a b)
                     (parseNatural-showNat-chars pos
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b)
                        (∷-stop isDigit-dot-false))

    step-some-digit :
      (char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat nothing (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b)
      ≡ just (mkResult
                (buildDecRat nothing (mag-quot (suc n) a b)
                              (mag-fracChars (suc n) a b))
                posAfterFrac [])
    step-some-digit =
      trans (past-dot-char-dot-eq nothing (mag-quot (suc n) a b)
               posAfterNat (mag-fracChars (suc n) a b))
            (bind-just-step (some digit)
                            (λ fd → pure (buildDecRat nothing
                                                      (mag-quot (suc n) a b) fd))
                            posAfterDot (mag-fracChars (suc n) a b)
                            (mag-fracChars (suc n) a b) posAfterFrac []
                            (some-digit-showℕ-padded-chars-end (mag-m a b)
                               (mag-rem (suc n) a b) posAfterDot
                               (0<[a⊔b]⊔1 a b)))

    pos-eq : posAfterFrac ≡ advancePositions pos
                              (emitMagnitude-chars (suc n) a b)
    pos-eq = sym (advancePositions-++ pos
                    (showNat-chars (mag-quot (suc n) a b))
                    ('.' ∷ mag-fracChars (suc n) a b))

-- ----------------------------------------------------------------------------
-- Phase 4.2: `-[1+ n ]` (neg) case
-- ----------------------------------------------------------------------------
--
-- Parallel to 4.1 but with two structural differences:
--   * Input prefix `'-' ∷ emitMagnitude-chars (suc n) a b` — the dash
--     is consumed by `optional-dash-succ` instead of failing-through
--     via `optional-dash-fail-on-showNat`.
--   * After the arithmetic rewrites, the numerator is `applySign
--     (just '-') scaledNum`.  This does *not* reduce without knowing
--     `scaledNum ≠ 0`; we call `sucn-scaled-suc` to get
--     `scaledNum ≡ suc k`, then `cong`-rewrite to turn `applySign
--     (just '-') scaledNum` into `applySign (just '-') (suc k) =
--     -[1+ k ]` (definitional).  The canonicalisation step then
--     routes through `canonicalizeDecRat-from-canonicalizeNat` with
--     `canonicalizeNat-scale-pos-max` composed via a `sym scaled-eq`
--     rewrite on the magnitude argument.
parseDecRat-roundtrip-neg : ∀ n a b pos
  .(cx : IsCanonical (suc n) a b) →
  parseDecRat pos (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx))
    ≡ just (mkResult (mkDecRat ℤ-[1+ n ] a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx)))
                     [])
parseDecRat-roundtrip-neg n a b pos cx =
  trans step-parseNat
    (trans step-some-digit
      (cong₂ (λ v p → just (mkResult v p []))
             (build-eq-neg n a b cx)
             pos-eq))
  where
    -- After `optional (char '-')` consumes the dash (definitional),
    -- then `parseNatural` consumes `showNat-chars (mag-quot …)`.
    posAfterDash : Position
    posAfterDash = advancePosition pos '-'

    posAfterNat : Position
    posAfterNat = advancePositions posAfterDash (showNat-chars (mag-quot (suc n) a b))

    posAfterDot : Position
    posAfterDot = advancePosition posAfterNat '.'

    posAfterFrac : Position
    posAfterFrac = advancePositions posAfterDot (mag-fracChars (suc n) a b)

    -- Step 2: `parseNatural posAfterDash emag` → `just (mkResult (mag-quot …) posAfterNat
    -- ('.' ∷ mag-fracChars …))`, lifted through the remainder of the bind chain.
    step-parseNat :
      parseDecRat pos ('-' ∷ emitMagnitude-chars (suc n) a b)
      ≡ (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat (just '-') (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b)
    step-parseNat =
      bind-just-step parseNatural
                     (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                              pure (buildDecRat (just '-') nₚ fd))
                     posAfterDash (emitMagnitude-chars (suc n) a b)
                     (mag-quot (suc n) a b) posAfterNat
                     ('.' ∷ mag-fracChars (suc n) a b)
                     (parseNatural-showNat-chars posAfterDash
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b)
                        (∷-stop isDigit-dot-false))

    -- Step 4: `char '.'` consumes `.` (definitional), then `some digit` consumes
    -- `mag-fracChars …` via `some-digit-showℕ-padded-chars-end`.
    step-some-digit :
      (char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat (just '-') (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b)
      ≡ just (mkResult
                (buildDecRat (just '-') (mag-quot (suc n) a b)
                              (mag-fracChars (suc n) a b))
                posAfterFrac [])
    step-some-digit =
      trans (past-dot-char-dot-eq (just '-') (mag-quot (suc n) a b)
               posAfterNat (mag-fracChars (suc n) a b))
            (bind-just-step (some digit)
                            (λ fd → pure (buildDecRat (just '-')
                                                      (mag-quot (suc n) a b) fd))
                            posAfterDot (mag-fracChars (suc n) a b)
                            (mag-fracChars (suc n) a b) posAfterFrac []
                            (some-digit-showℕ-padded-chars-end (mag-m a b)
                               (mag-rem (suc n) a b) posAfterDot
                               (0<[a⊔b]⊔1 a b)))

    -- Position-equality piece: the stepped-through final position equals
    -- `advancePositions pos ('-' ∷ emag)`.
    pos-eq : posAfterFrac ≡ advancePositions pos
                              ('-' ∷ emitMagnitude-chars (suc n) a b)
    pos-eq = sym (advancePositions-++ posAfterDash
                    (showNat-chars (mag-quot (suc n) a b))
                    ('.' ∷ mag-fracChars (suc n) a b))

-- ----------------------------------------------------------------------------
-- Phase 4.3: `+ zero` case
-- ----------------------------------------------------------------------------
--
-- `cx : IsCanonical 0 a b` forces `a = b = 0` structurally
-- (`isCanonicalᵇ` returns `false` at `(0, 0, suc _)` and
-- `(0, suc _, _)`), so three clauses suffice: the valid `(0, 0, 0)`
-- case closes by `refl` (pure compute — `emitMagnitude-chars 0 0 0 =
-- '0' ∷ '.' ∷ '0' ∷ []`, and `parseDecRat` on this string reduces
-- entirely by pattern matching; `canonicalizeNat 0 1 1 = (0, 0, 0)`
-- definitionally), and the two impossible sub-cases close via
-- `EmptyI.⊥-elim cx`.
parseDecRat-roundtrip-+zero : ∀ a b pos
  .(cx : IsCanonical 0 a b) →
  parseDecRat pos (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx))
    ≡ just (mkResult (mkDecRat (ℤ+ zero) a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx)))
                     [])
parseDecRat-roundtrip-+zero zero    zero    _   _  = refl
parseDecRat-roundtrip-+zero zero    (suc _) _   cx = EmptyI.⊥-elim cx
parseDecRat-roundtrip-+zero (suc _) _       _   cx = EmptyI.⊥-elim cx

-- ============================================================================
-- Phase 5: Top-level dispatcher
-- ============================================================================
--
-- Pattern-match on the numerator constructor (`+ zero` / `+ suc n` /
-- `-[1+ n ]`) and route to the corresponding per-branch theorem.
-- Each branch's theorem carries the same statement shape, so the
-- dispatcher is three one-liners.
parseDecRat-roundtrip : ∀ d pos →
  parseDecRat pos (showDecRat-dec-chars d)
    ≡ just (mkResult d (advancePositions pos (showDecRat-dec-chars d)) [])
parseDecRat-roundtrip (mkDecRat (ℤ+ zero)  a b cx) pos =
  parseDecRat-roundtrip-+zero a b pos cx
parseDecRat-roundtrip (mkDecRat (ℤ+ suc n) a b cx) pos =
  parseDecRat-roundtrip-+suc n a b pos cx
parseDecRat-roundtrip (mkDecRat ℤ-[1+ n ]  a b cx) pos =
  parseDecRat-roundtrip-neg n a b pos cx
