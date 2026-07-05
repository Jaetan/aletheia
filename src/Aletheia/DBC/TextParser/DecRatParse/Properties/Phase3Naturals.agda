-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Phase 3 of the `parseDecRat` roundtrip proof — `parseNatural`
-- roundtrip, canonicalisation extractors, and arithmetic bindings
-- consumed by Phase 4.  Carved out of the historical
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` mega-module under
-- the R21 cluster 9 split (closes AGDA-D-15.1 for this file).
--
-- Phase organisation (preserved from the original section headers):
--   * 3.1: Non-emptiness and position/length lemmas.
--   * 3.2: parseNatural reads back showNat-chars.
--   * 3.3: canonicalizeDecRat-from-canonicalizeNat — sign-agnostic wrapper.
--   * 3.4: Canonicality extractors (positive-magnitude path).
--   * 3.5: Digit-dash discrimination + optional-dash fail-through.
--   * 3.6: Padded-fraction `some digit` reader (named wrapper).
--   * 3.7: Nonzero positivity of the scaled magnitude.
--   * 3.8: showNat-chars head digit.
--   * 3.9 / 3.9.b-e: Suffix-exhausting parser variants + scalar helpers + arithmetic bridge.
--   * 3.11: Arithmetic bindings for Phase 4 (mag-* private defs,
--           emitMagnitude-chars-mag, showDecRat-chars-head-*, build-eq-+suc/-neg).
--
-- Depends on Phase 1 (foldl-digitToNat-showNat-chars) and Phase 2
-- (some-satisfy-prefix, SuffixStops, isDigit predicate machinery).
module Aletheia.DBC.TextParser.DecRatParse.Properties.Phase3Naturals where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Base using (isDigit; _≈ᵇ_)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as EmptyI
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (length-++ to length-++ₗ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _^_; _⊔_;
         _<_; _≤_; z≤n; s≤s; NonZero)
open import Data.Nat.Base using ()
open import Data.Nat.Properties
  using (+-comm;
         m∸n+n≡m; m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl)
open import Data.Nat.DivMod
  using (m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Divisibility using (_∣?_; _∤_)
open import Data.Product using (_×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Aletheia.Parser.Combinators
  using (Position; mkResult;
         advancePosition; advancePositions;
         satisfy; digit; some; manyHelper;
         char; optional)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars;
         emitMagnitude-chars; showDecRat-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse
  using (parseDigitList; applySign; buildDecRat)
open import Aletheia.DBC.TextParser.Lexer using (parseNatural)
open import Data.Integer using (sign; _◃_; ∣_∣)
  renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Aletheia.DBC.DecRat
  using (mkDecRat; IsCanonical;
         canonicalizeDecRat; canonicalizeNat)
open import Aletheia.DBC.DecRat.ScaleLemmas using (canonicalizeNat-scale-pos)

-- Phase 1 + Phase 2 lemmas consumed by Phase 3.
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits
  using (foldl-digitToNat-showNat-chars; parseDigitList-showℕ-padded-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many
  using (SuffixStops; some-satisfy-prefix;
         All-isDigit-showNat-chars; All-isDigit-showℕ-padded-chars;
         sameLengthᵇ-cons)

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
-- A second simultaneous `with` on the `some` call + the outcome-level
-- prefix lemma resolves the digits read (the lemma is `proj₂`-level,
-- so it cannot fire as a rewrite on the pair-typed scrutinee); the
-- final `rewrite fold-eq` closes the fold.
parseNatural-showNat-chars : ∀ pos n (suffix : List Char) →
  SuffixStops isDigit suffix →
  proj₂ (parseNatural pos (showNat-chars n ++ₗ suffix))
    ≡ just (mkResult n (advancePositions pos (showNat-chars n)) suffix)
parseNatural-showNat-chars pos n suffix ss
  with showNat-chars n
     | showNat-chars-nonempty n
     | All-isDigit-showNat-chars n
     | foldl-digitToNat-showNat-chars n
... | .(x ∷ xs') | x , xs' , refl | px ∷ pxs | fold-eq
  with some (satisfy isDigit) pos ((x ∷ xs') ++ₗ suffix)
     | some-satisfy-prefix isDigit pos x xs' suffix px pxs ss
...   | w , just r | refl rewrite fold-eq = refl

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
  proj₂ (optional (char '-') pos (x ∷ xs'))
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
  proj₂ (some digit pos (showℕ-padded-chars w n ++ₗ suffix))
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
  → proj₂ (manyHelper (satisfy P) pos xs n)
    ≡ just (mkResult xs (advancePositions pos xs) [])
manyHelper-satisfy-exhaust-all P pos []        _          zero     _            = refl
manyHelper-satisfy-exhaust-all P pos (x ∷ xs') _          zero     ()
manyHelper-satisfy-exhaust-all P pos []        _          (suc n') _            = refl
manyHelper-satisfy-exhaust-all P pos (x ∷ xs') (px ∷ pxs) (suc n') (s≤s len≤)
  rewrite px
        | sameLengthᵇ-cons x xs'
  with manyHelper (satisfy P) (advancePosition pos x) xs' n'
     | manyHelper-satisfy-exhaust-all P (advancePosition pos x) xs' pxs n' len≤
... | w' , just restResult | refl = refl

-- Entry point at the public `many` (length-fuel) specialisation.
-- Parallel to `some-satisfy-prefix` but at empty suffix: both use the
-- `px` / `sameLengthᵇ-cons` / inner-exhaust rewrite sequence.
some-satisfy-prefix-all : (P : Char → Bool) (pos : Position)
  → ∀ x (xs' : List Char)
  → P x ≡ true
  → All (λ c → P c ≡ true) xs'
  → proj₂ (some (satisfy P) pos (x ∷ xs'))
    ≡ just (mkResult (x ∷ xs') (advancePositions pos (x ∷ xs')) [])
some-satisfy-prefix-all P pos x xs' px pxs
  rewrite px
  with manyHelper (satisfy P) (advancePosition pos x) xs' (length xs')
     | manyHelper-satisfy-exhaust-all P (advancePosition pos x) xs'
         pxs (length xs') ≤-refl
... | w' , just restResult | refl = refl

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
  proj₂ (some digit pos (showℕ-padded-chars w n))
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
  proj₂ (optional (char '-') pos (showNat-chars n ++ₗ rest))
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
  proj₂ (optional (char '-') pos ('-' ∷ rest))
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

-- R21 cluster 9 — split: these were `private` in the original mega-module
-- because they were internal helpers above the consumer code in the same
-- file.  After the split, Phase 4+ live in the parent `Properties.agda`
-- facade (or further submodules) and need to reach `mag-quot` / `mag-rem`
-- / `mag-fracChars` etc. in `rewrite` chains, so the qualifier is
-- dropped.  Same effective visibility — they were never consumed outside
-- this module's translation unit, just below it in source order.
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

-- Head-of-`showDecRat-dec-chars` decomposition.  Negative DecRat values
-- emit `'-'` first; non-negative values emit `digitChar k` (`showNat-
-- chars`'s head from `showNat-chars-head`).  The `mag-quot` reference in
-- the digit case stays opaque to the caller — it surfaces only inside
-- the equation's RHS, never in the type.
--
-- Used by Layer 3 line constructs (e.g. EV_) to discharge the
-- `SuffixStops isHSpace (showDecRat-dec-chars d ++ rest)` precondition
-- of `parseWS-one-space` after a separator space.
showDecRat-chars-head-dash : ∀ n a b
  .(cx : IsCanonical (suc n) a b) →
  ∃ λ tail →
    showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx) ≡ '-' ∷ tail
showDecRat-chars-head-dash _ _ _ _ = _ , refl

showDecRat-chars-head-digit : ∀ absNum a b
  .(cx : IsCanonical absNum a b) →
  ∃₂ λ (k : ℕ) (tail : List Char) →
    k < 10 ×
    showDecRat-dec-chars (mkDecRat (ℤ+ absNum) a b cx) ≡ digitChar k ∷ tail
-- Case-split on `absNum` is required: `showDecRat-dec-chars` pattern-
-- matches on `+ zero` vs `+ suc _`, so the equation's RHS doesn't
-- reduce on abstract `absNum`.
showDecRat-chars-head-digit zero a b _
  with showNat-chars-head (mag-quot 0 a b)
... | k , subtail , k<10 , eq =
      k , subtail ++ₗ '.' ∷ mag-fracChars 0 a b , k<10 ,
      cong (λ s → s ++ₗ '.' ∷ mag-fracChars 0 a b) eq
showDecRat-chars-head-digit (suc n) a b _
  with showNat-chars-head (mag-quot (suc n) a b)
... | k , subtail , k<10 , eq =
      k , subtail ++ₗ '.' ∷ mag-fracChars (suc n) a b , k<10 ,
      cong (λ s → s ++ₗ '.' ∷ mag-fracChars (suc n) a b) eq

-- `build-eq-+suc` / `build-eq-neg` — `buildDecRat` on the emitter-shape
-- inputs reconstructs the original canonical record.  Lifted to module-
-- level (out of `parseDecRatFrac-roundtrip-+suc`'s / `-neg`'s `where` block)
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

