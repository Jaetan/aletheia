{-# OPTIONS --safe --without-K #-}

-- Phase 6 of the `parseDecRat` roundtrip proof — suffix-aware
-- variants + bareInt-form roundtrip + refined-parser wrappers.
-- Carved out of the historical
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` mega-module
-- under the R21 cluster 9 split (closes AGDA-D-15.1 for this file).
--
-- Phase organisation (preserved from the original section headers):
--   * 6: Suffix-aware variant — per-sign branches (+ zero / + suc / neg)
--        and the top-level dispatcher (`parseDecRatFrac-roundtrip-suffix`).
--   * 6.5: Public `parseDecRat`-level roundtrip on the frac wire form.
--   * 6.6: parseDecRatBareInt — local helpers, per-sign fail/succeed
--          lemmas, dispatcher, and the public composer.
--   * 6.7: Refined-parser roundtrips for `parseIntDecRat` /
--          `parseNatDecRat` (DSL boundary entry points used by 3c-B).
--
-- Depends on all earlier phases (1-4) via the re-export base.
module Aletheia.DBC.TextParser.DecRatParse.Properties.Phase6Suffix where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char; toℕ) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit; _≈ᵇ_)
open import Data.Char.Properties using (toℕ-injective)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as EmptyI
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; length; foldl) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-assoc)
  renaming (length-++ to length-++ₗ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _^_; _⊔_;
         _<_; _≤_; z≤n; s≤s; NonZero)
open import Data.Nat.Base using (≢-nonZero⁻¹)
open import Data.Nat.Properties
  using (*-comm; +-comm; +-identityʳ; *-identityʳ; ≤-<-trans; n<1+n; ^-monoʳ-<;
         m≤m+n; m∸n+n≡m; m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl;
         m*n≢0; m^n≢0)
open import Data.Nat.DivMod
  using (m%n<n; m≡m%n+[m/n]*n; m<n*o⇒m/o<n)
open import Data.Nat.Divisibility using (_∣_; _∣?_; _∤_)
open import Data.Product using (Σ; _×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; value; position; remaining;
         advancePosition; advancePositions;
         satisfy; digit; some; many; manyHelper; sameLengthᵇ;
         char; optional; fail;
         _>>=_; pure; _<$>_; _<*>_; _*>_; _<|>_)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars;
         emitMagnitude-chars; showDecRat-dec-chars; showInt-chars)
open import Aletheia.DBC.TextParser.DecRatParse
  using (charToDigit; parseDigitList; parseDecRat; parseDecRatFrac;
         parseDecRatBareInt; applySign; buildDecRat;
         parseIntDecRat; parseNatDecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRat; intDecRatToℤ; mkIntDecRatFromℤ;
   mkIntDecRatFromℤ-intDecRatToℤ;
   isIntegerᵇ; isIntegerᵇ-fromℤ;
   NatDecRat; mkNatDecRat; natDecRatToℕ; mkNatDecRatFromℕ;
   mkNatDecRatFromℕ-natDecRatToℕ;
   isNonNegIntegerᵇ; isNonNegIntegerᵇ-fromℕ)
open import Aletheia.Prelude using (ifᵀ_then_else_; ifᵀ-witness)
open import Aletheia.DBC.TextParser.Lexer using (parseNatural)
open import Aletheia.Protocol.JSON.Parse using (digitToNat)
open import Data.Integer using (ℤ; sign; _◃_; ∣_∣)
  renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Aletheia.DBC.DecRat
  using (DecRat; mkDecRat; isCanonicalᵇ; IsCanonical;
         canonicalizeDecRat; canonicalizeNat; 0ᵈ; fromℤ)
open import Aletheia.DBC.DecRat.ScaleLemmas using (canonicalizeNat-scale-pos)

-- Phases 1-4 re-export base — every public lemma above is available.
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits      public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many        public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase3Naturals    public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase4Composition public

-- ============================================================================
-- Phase 6: Suffix-aware variant
-- ============================================================================
--
-- Layer 3 line constructs (B.3.d Layer 3) consume `showDecRat-dec-chars d`
-- between non-empty boundaries (e.g. `EV_ … <initial> <minimum> <maximum> …`,
-- where each value is followed by horizontal whitespace).  The closed-form
-- `parseDecRatFrac-roundtrip` above only handles `suffix = []`; below we mirror
-- the three numerator branches with an extra `suffix` argument and a
-- `SuffixStops isDigit suffix` precondition.
--
-- Two structural differences from the closed form:
--   * Input is `showDecRat-dec-chars d ++ₗ suffix`, which under
--     `_++_`'s left-grouping is `(showNat-chars _ ++ₗ '.' ∷ frac) ++ₗ
--     suffix`.  An explicit `++-assoc` step re-groups it to `showNat-chars
--     _ ++ₗ '.' ∷ (frac ++ₗ suffix)` so the `optional-dash-fail-on-showNat`
--     and `parseNatural-showNat-chars` lemmas can match.
--   * The fractional `some digit` step takes `suffix` directly (via the
--     existing `some-digit-showℕ-padded-chars`) rather than the
--     closed-suffix `-end` variant.
--
-- The position arithmetic is unchanged: `advancePositions pos
-- (showDecRat-dec-chars d)` only depends on the consumed prefix, not the
-- trailing `suffix`.

-- Helper: regroup `emitMagnitude-chars _ ++ suffix` from left-grouped to
-- right-grouped via `++-assoc`.  Used as the first `cong (parseDecRat
-- pos)` step in both `+suc-suffix` and `-neg-suffix`.
emag-suffix-shape : ∀ absNum a b suffix →
  emitMagnitude-chars absNum a b ++ₗ suffix
    ≡ showNat-chars (mag-quot absNum a b)
        ++ₗ '.' ∷ mag-fracChars absNum a b ++ₗ suffix
emag-suffix-shape absNum a b suffix =
  ++-assoc (showNat-chars (mag-quot absNum a b))
           ('.' ∷ mag-fracChars absNum a b)
           suffix

-- ----------------------------------------------------------------------------
-- Phase 6.1: `+ zero` case with suffix
-- ----------------------------------------------------------------------------
--
-- For the canonical (a, b) = (0, 0) sub-case, `showDecRat-dec-chars
-- (mkDecRat (+ 0) 0 0 _) = '0' ∷ '.' ∷ '0' ∷ []`.  Appending `suffix`
-- gives `'0' ∷ '.' ∷ '0' ∷ suffix` (definitional via `_∷_` → `_++_`
-- reduction).  parseDecRat then reduces step-by-step:
--   * `optional (char '-')` on `'0' ∷ ...` falls to `nothing` branch (def).
--   * `parseNatural` on `'0' ∷ '.' ∷ '0' ∷ suffix` reads `'0'` and stops
--     at `'.'` (def — `manyHelper`'s outer `with satisfy isDigit` resolves
--     definitionally on the concrete `'.'` head).
--   * `char '.'` consumes (def).
--   * `some digit` on `'0' ∷ suffix` reads `'0'` then must check `suffix`
--     for further digits — *this* is where the lemma is needed.  We
--     `rewrite` with `some-satisfy-prefix` at the matching shape.
-- After the `rewrite`, the entire chain reduces, yielding `refl`.
parseDecRatFrac-roundtrip-+zero-suffix : ∀ a b pos suffix
  .(cx : IsCanonical 0 a b) →
  SuffixStops isDigit suffix →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx)
                     ++ₗ suffix)
    ≡ just (mkResult (mkDecRat (ℤ+ zero) a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx)))
                     suffix)
parseDecRatFrac-roundtrip-+zero-suffix zero    zero    pos suffix _ ss
  rewrite some-satisfy-prefix isDigit
            (advancePosition (advancePosition pos '0') '.')
            '0' [] suffix refl [] ss
  = refl
parseDecRatFrac-roundtrip-+zero-suffix zero    (suc _) _   _      cx _ = EmptyI.⊥-elim cx
parseDecRatFrac-roundtrip-+zero-suffix (suc _) _       _   _      cx _ = EmptyI.⊥-elim cx

-- ----------------------------------------------------------------------------
-- Phase 6.2: `+ suc n` case with suffix
-- ----------------------------------------------------------------------------
parseDecRatFrac-roundtrip-+suc-suffix : ∀ n a b pos suffix
  .(cx : IsCanonical (suc n) a b) →
  SuffixStops isDigit suffix →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat (ℤ+ suc n) a b cx)
                     ++ₗ suffix)
    ≡ just (mkResult (mkDecRat (ℤ+ suc n) a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat (ℤ+ suc n) a b cx)))
                     suffix)
parseDecRatFrac-roundtrip-+suc-suffix n a b pos suffix cx ss =
  trans (cong (parseDecRatFrac pos) (emag-suffix-shape (suc n) a b suffix))
    (trans step-dash-fail
      (trans step-parseNat
        (trans step-some-digit
          (cong₂ (λ v p → just (mkResult v p suffix))
                 (build-eq-+suc n a b cx)
                 pos-eq))))
  where
    posAfterNat : Position
    posAfterNat = advancePositions pos (showNat-chars (mag-quot (suc n) a b))

    posAfterDot : Position
    posAfterDot = advancePosition posAfterNat '.'

    posAfterFrac : Position
    posAfterFrac = advancePositions posAfterDot (mag-fracChars (suc n) a b)

    input-shape : List Char
    input-shape = showNat-chars (mag-quot (suc n) a b)
                    ++ₗ '.' ∷ mag-fracChars (suc n) a b ++ₗ suffix

    step-dash-fail :
      parseDecRatFrac pos input-shape
      ≡ (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing nₚ fd))
        pos input-shape
    step-dash-fail =
      bind-just-step (optional (char '-'))
                     (λ neg → parseNatural >>= λ nₚ → char '.' >>= λ _ →
                              some digit >>= λ fd →
                              pure (buildDecRat neg nₚ fd))
                     pos input-shape
                     nothing pos input-shape
                     (optional-dash-fail-on-showNat pos
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix))

    step-parseNat :
      (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat nothing nₚ fd))
        pos input-shape
      ≡ (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
    step-parseNat =
      bind-just-step parseNatural
                     (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                              pure (buildDecRat nothing nₚ fd))
                     pos input-shape
                     (mag-quot (suc n) a b) posAfterNat
                     ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
                     (parseNatural-showNat-chars pos
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
                        (∷-stop isDigit-dot-false))

    step-some-digit :
      (char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat nothing (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
      ≡ just (mkResult
                (buildDecRat nothing (mag-quot (suc n) a b)
                              (mag-fracChars (suc n) a b))
                posAfterFrac suffix)
    step-some-digit =
      trans (past-dot-char-dot-eq nothing (mag-quot (suc n) a b)
               posAfterNat (mag-fracChars (suc n) a b ++ₗ suffix))
            (bind-just-step (some digit)
                            (λ fd → pure (buildDecRat nothing
                                                      (mag-quot (suc n) a b) fd))
                            posAfterDot (mag-fracChars (suc n) a b ++ₗ suffix)
                            (mag-fracChars (suc n) a b) posAfterFrac suffix
                            (some-digit-showℕ-padded-chars (mag-m a b)
                               (mag-rem (suc n) a b) posAfterDot suffix
                               (0<[a⊔b]⊔1 a b) ss))

    pos-eq : posAfterFrac ≡ advancePositions pos
                              (emitMagnitude-chars (suc n) a b)
    pos-eq = sym (advancePositions-++ pos
                    (showNat-chars (mag-quot (suc n) a b))
                    ('.' ∷ mag-fracChars (suc n) a b))

-- ----------------------------------------------------------------------------
-- Phase 6.3: `-[1+ n ]` (neg) case with suffix
-- ----------------------------------------------------------------------------
parseDecRatFrac-roundtrip-neg-suffix : ∀ n a b pos suffix
  .(cx : IsCanonical (suc n) a b) →
  SuffixStops isDigit suffix →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx)
                     ++ₗ suffix)
    ≡ just (mkResult (mkDecRat ℤ-[1+ n ] a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx)))
                     suffix)
parseDecRatFrac-roundtrip-neg-suffix n a b pos suffix cx ss =
  trans (cong (λ x → parseDecRatFrac pos ('-' ∷ x))
              (emag-suffix-shape (suc n) a b suffix))
    (trans step-parseNat
      (trans step-some-digit
        (cong₂ (λ v p → just (mkResult v p suffix))
               (build-eq-neg n a b cx)
               pos-eq)))
  where
    posAfterDash : Position
    posAfterDash = advancePosition pos '-'

    posAfterNat : Position
    posAfterNat = advancePositions posAfterDash
                    (showNat-chars (mag-quot (suc n) a b))

    posAfterDot : Position
    posAfterDot = advancePosition posAfterNat '.'

    posAfterFrac : Position
    posAfterFrac = advancePositions posAfterDot (mag-fracChars (suc n) a b)

    step-parseNat :
      parseDecRatFrac pos
        ('-' ∷ showNat-chars (mag-quot (suc n) a b)
                 ++ₗ '.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
      ≡ (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat (just '-') (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
    step-parseNat =
      bind-just-step parseNatural
                     (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                              pure (buildDecRat (just '-') nₚ fd))
                     posAfterDash
                     (showNat-chars (mag-quot (suc n) a b)
                        ++ₗ '.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
                     (mag-quot (suc n) a b) posAfterNat
                     ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
                     (parseNatural-showNat-chars posAfterDash
                        (mag-quot (suc n) a b)
                        ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
                        (∷-stop isDigit-dot-false))

    step-some-digit :
      (char '.' >>= λ _ → some digit >>= λ fd →
         pure (buildDecRat (just '-') (mag-quot (suc n) a b) fd))
        posAfterNat ('.' ∷ mag-fracChars (suc n) a b ++ₗ suffix)
      ≡ just (mkResult
                (buildDecRat (just '-') (mag-quot (suc n) a b)
                              (mag-fracChars (suc n) a b))
                posAfterFrac suffix)
    step-some-digit =
      trans (past-dot-char-dot-eq (just '-') (mag-quot (suc n) a b)
               posAfterNat (mag-fracChars (suc n) a b ++ₗ suffix))
            (bind-just-step (some digit)
                            (λ fd → pure (buildDecRat (just '-')
                                                      (mag-quot (suc n) a b) fd))
                            posAfterDot (mag-fracChars (suc n) a b ++ₗ suffix)
                            (mag-fracChars (suc n) a b) posAfterFrac suffix
                            (some-digit-showℕ-padded-chars (mag-m a b)
                               (mag-rem (suc n) a b) posAfterDot suffix
                               (0<[a⊔b]⊔1 a b) ss))

    pos-eq : posAfterFrac ≡ advancePositions pos
                              ('-' ∷ emitMagnitude-chars (suc n) a b)
    pos-eq = sym (advancePositions-++ posAfterDash
                    (showNat-chars (mag-quot (suc n) a b))
                    ('.' ∷ mag-fracChars (suc n) a b))

-- ----------------------------------------------------------------------------
-- Phase 6.4: Top-level dispatcher with suffix
-- ----------------------------------------------------------------------------
parseDecRatFrac-roundtrip-suffix : ∀ d pos suffix →
  SuffixStops isDigit suffix →
  parseDecRatFrac pos (showDecRat-dec-chars d ++ₗ suffix)
    ≡ just (mkResult d (advancePositions pos (showDecRat-dec-chars d)) suffix)
parseDecRatFrac-roundtrip-suffix (mkDecRat (ℤ+ zero)  a b cx) pos suffix ss =
  parseDecRatFrac-roundtrip-+zero-suffix a b pos suffix cx ss
parseDecRatFrac-roundtrip-suffix (mkDecRat (ℤ+ suc n) a b cx) pos suffix ss =
  parseDecRatFrac-roundtrip-+suc-suffix n a b pos suffix cx ss
parseDecRatFrac-roundtrip-suffix (mkDecRat ℤ-[1+ n ]  a b cx) pos suffix ss =
  parseDecRatFrac-roundtrip-neg-suffix n a b pos suffix cx ss

-- ----------------------------------------------------------------------------
-- Phase 6.5: Public `parseDecRat`-level roundtrip on the frac wire form
-- ----------------------------------------------------------------------------
--
-- Lifts `parseDecRatFrac-roundtrip-suffix` through the outer `<|>`.  The
-- `showDecRat-dec-chars` emitter always produces a `'.'`-bearing form, so
-- `parseDecRatFrac` always succeeds on this input — the bare-int branch
-- of `parseDecRat = parseDecRatFrac <|> parseDecRatBareInt` never fires
-- and `alt-left-just` collapses the wrapper to a one-liner.
--
-- This is the lemma external callers (e.g.,
-- `Aletheia.DBC.TextParser.Properties.EnvVars.EnvVar`) hold against —
-- their goals are `parseDecRat …`, not `parseDecRatFrac …`, since the
-- aggregate parsers compose the public name.
--
-- Owed for Layer 3 (AVInt attribute path):
--
--   parseDecRat-bareInt-roundtrip-suffix : ∀ z pos suffix →
--     SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' →
--     parseDecRat pos (showInt-chars z ++ₗ suffix) ≡
--     just (mkResult (fromℤ z)
--                    (advancePositions pos (showInt-chars z))
--                    suffix)
--
-- The wire form for `AVInt z` is `showInt-chars (intDecRatToℤ z)` (see
-- `Aletheia.DBC.TextFormatter.Attributes.emitAssignValue-chars` /
-- `emitDefaultValue-chars`), which has no `'.'`.  The lemma will
-- discharge the `parseDecRatFrac` failure via `bind-nothing` on the
-- absent `'.'`, then close on the bare-int branch.  Estimated ~100 LOC
-- (no canonicalization mass — denominator stays 1, so the
-- `canonicalizeDecRat (+ n) 0 0` reduction is direct).  Consumed by
-- `Aletheia.DBC.TextParser.Properties.Attributes.Common`'s AVInt
-- `rawOfAttribute` per-case lemma.

private
  -- Same shape as `_<|>_` would expand to — kept lifted so the wrapper
  -- below doesn't open the entire `Primitives` module just for one
  -- helper.  Identical body to `Properties.Primitives.alt-left-just`.
  alt-left-just-here :
    ∀ {A : Set} (p q : Parser A) (pos : Position) (input : List Char) r
    → p pos input ≡ just r
    → (p <|> q) pos input ≡ just r
  alt-left-just-here p q pos input r eq with p pos input | eq
  ... | just .r | refl = refl

parseDecRat-roundtrip-suffix : ∀ d pos suffix →
  SuffixStops isDigit suffix →
  parseDecRat pos (showDecRat-dec-chars d ++ₗ suffix)
    ≡ just (mkResult d (advancePositions pos (showDecRat-dec-chars d)) suffix)
parseDecRat-roundtrip-suffix d pos suffix ss =
  alt-left-just-here parseDecRatFrac parseDecRatBareInt pos
    (showDecRat-dec-chars d ++ₗ suffix) _
    (parseDecRatFrac-roundtrip-suffix d pos suffix ss)

-- ============================================================================
-- Phase 6.6: parseDecRat bareInt-form roundtrip with suffix
-- ============================================================================
--
-- Closes the AVInt path consumer in
-- `Properties/Attributes/Common.agda`: when the formatter emits
-- `showInt-chars (intDecRatToℤ z)` (no `'.'`, no fractional component),
-- the parser must read back via the bare-int branch of
-- `parseDecRat = parseDecRatFrac <|> parseDecRatBareInt` since the frac
-- branch fails at `char '.'` on a non-`'.'` suffix.
--
-- Strategy (mirrors the frac roundtrip, simplified):
--
--   1. `parseDecRatFrac pos (showInt-chars z ++ suffix) ≡ nothing` —
--      via `bind-just-step` through `optional (char '-')` (success or
--      fail depending on sign) and `parseNatural` (always succeeds on
--      `showNat-chars n` under `SuffixStops isDigit suffix`), then
--      `bind-nothing` through `char '.'` (fails on a non-`'.'`
--      suffix).
--   2. `parseDecRatBareInt pos (showInt-chars z ++ suffix)
--        ≡ just (mkResult (fromℤ z) ...)` — via the same two `bind-
--      just-step`s, then `pure` reduction with
--      `canonicalizeDecRat-zero-exp`.
--   3. Compose via `alt-right-nothing` on the outer `<|>`.
--
-- No canonicalization mass — the bare-int branch always fixes
-- `(twoExp, fiveExp) = (0, 0)`, so `canonicalizeDecRat z 0 0` reduces
-- pointwise to `fromℤ z` via the `IsCanonical _ 0 0 = ⊤` collapse
-- (see `canonicalizeDecRat-zero-exp` below).

-- ----------------------------------------------------------------------------
-- Phase 6.6.1: Local helpers — head-of-list + char-fail bridge
-- ----------------------------------------------------------------------------

-- Head of a list, defaulting to `d` on empty.  Used by the public
-- precondition `'.' ≢ headOr suffix '_'` to express "the suffix's
-- first char (if any) is not `'.'`" in a list-shape-agnostic way
-- (`'_'` is an arbitrary non-`'.'` placeholder for the empty case).
-- Public so downstream proofs (`Properties/Attributes/Type.agda`) can
-- discharge the precondition without redefining the helper.
headOr : ∀ {A : Set} → List A → A → A
headOr []      d = d
headOr (x ∷ _) _ = x

private
  -- Nat-level bridge: `m ≢ n ⟹ (m ≡ᵇ n) ≡ false`.  Structural induction
  -- on `m, n` exhausts the four diagonal cases; `(zero, zero)` is the
  -- only one that needs the hypothesis to derive the absurdity.
  ≢→≡ᵇ-false-ℕ : ∀ m n → m ≢ n → (m Data.Nat.≡ᵇ n) ≡ false
  ≢→≡ᵇ-false-ℕ zero    zero    h = ⊥-elim (h refl)
  ≢→≡ᵇ-false-ℕ zero    (suc _) _ = refl
  ≢→≡ᵇ-false-ℕ (suc _) zero    _ = refl
  ≢→≡ᵇ-false-ℕ (suc m) (suc n) h = ≢→≡ᵇ-false-ℕ m n (λ m≡n → h (cong suc m≡n))

  -- Char-level bridge: lift `≢→≡ᵇ-false-ℕ` through `toℕ-injective`.
  -- `c ≈ᵇ d` is `toℕ c ≡ᵇ toℕ d` by definition (`Data.Char.Base`).
  ≢→≈ᵇ-false : ∀ c d → c ≢ d → (c ≈ᵇ d) ≡ false
  ≢→≈ᵇ-false c d c≢d =
    ≢→≡ᵇ-false-ℕ (toℕ c) (toℕ d) (λ teq → c≢d (toℕ-injective c d teq))

  -- `char '.' pos suffix ≡ nothing` when suffix's head is not `'.'`.
  -- Two cases: empty suffix (definitional `nothing` from `satisfy _ _ []`)
  -- and `c ∷ cs` with `c ≢ '.'` (`satisfy`'s false-branch via
  -- `≢→≈ᵇ-false`).
  char-dot-fail-on-non-dot : ∀ pos suffix →
    '.' ≢ headOr suffix '_' →
    char '.' pos suffix ≡ nothing
  char-dot-fail-on-non-dot _ []       _  = refl
  char-dot-fail-on-non-dot _ (c ∷ _)  ne
    rewrite ≢→≈ᵇ-false c '.' (λ c≡dot → ne (sym c≡dot))
    = refl

  -- Local version of `Primitives.bind-nothing` (DecRatParse/Properties is
  -- below Primitives in the import graph, so we can't reach back).
  bind-nothing-here : ∀ {A B : Set} (p : Parser A) (f : A → Parser B)
                   (pos : Position) (input : List Char)
    → p pos input ≡ nothing
    → (p >>= f) pos input ≡ nothing
  bind-nothing-here p f pos input eq with p pos input | eq
  ... | nothing | refl = refl

-- ----------------------------------------------------------------------------
-- Phase 6.6.2: canonicalizeDecRat at twoExp = fiveExp = 0 collapses to fromℤ
-- ----------------------------------------------------------------------------
--
-- With `(a, b) = (0, 0)`, `canonicalizeNat ∣z∣ 0 0` reduces to `(∣z∣, 0, 0)`
-- by the first clause of each `stripShared{2,5}-abs` (no work to do at
-- exponent 0).  `canonicalizeDecRat`'s `with`-abstraction then resolves
-- as `mkDecRat (sign z ◃ ∣z∣) 0 0 _`, with the irrelevant
-- `IsCanonical (sign z ◃ ∣z∣) 0 0 = ⊤` witness.  `fromℤ` produces the
-- same shape with the same irrelevant `tt` witness, so each non-zero
-- sign branch closes by `refl`.

canonicalizeDecRat-zero-exp : ∀ z → canonicalizeDecRat z 0 0 ≡ fromℤ z
canonicalizeDecRat-zero-exp (ℤ+ zero)  = refl
canonicalizeDecRat-zero-exp (ℤ+ suc _) = refl
canonicalizeDecRat-zero-exp ℤ-[1+ _ ]  = refl

-- ----------------------------------------------------------------------------
-- Phase 6.6.3: optional-dash success on the negative wire form
-- ----------------------------------------------------------------------------
--
-- `optional (char '-')` on `'-' ∷ rest` consumes `'-'` and returns
-- `just (just '-')`.  Reuses `optional-dash-succ` from Phase 3.10 (which
-- already proved this for any rest).

-- ----------------------------------------------------------------------------
-- Phase 6.6.4: parseNatural on showNat-chars n then `pure` (bare-int success)
-- ----------------------------------------------------------------------------
--
-- The bare-int branch reads `optional (char '-') >>= parseNatural >>= pure`
-- with `pure (buildDecRat neg n [])` at the tail.  Each non-pure step
-- reuses an existing lemma; `pure` is definitional `just`-injection.

-- ----------------------------------------------------------------------------
-- Phase 6.6.5: parseDecRatFrac fails on the bare-int wire form (positive z)
-- ----------------------------------------------------------------------------

private
  parseDecRatFrac-fails-+ : ∀ n pos suffix →
    SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' →
    parseDecRatFrac pos (showNat-chars n ++ₗ suffix) ≡ nothing
  parseDecRatFrac-fails-+ n pos suffix ss not-dot =
    trans step-dash-fail
      (trans step-parseNat
        step-dot-fails)
    where
      posAfterNat : Position
      posAfterNat = advancePositions pos (showNat-chars n)

      step-dash-fail :
        parseDecRatFrac pos (showNat-chars n ++ₗ suffix)
        ≡ (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
             pure (buildDecRat nothing nₚ fd))
          pos (showNat-chars n ++ₗ suffix)
      step-dash-fail =
        bind-just-step (optional (char '-'))
                       (λ neg → parseNatural >>= λ nₚ → char '.' >>= λ _ →
                                some digit >>= λ fd →
                                pure (buildDecRat neg nₚ fd))
                       pos (showNat-chars n ++ₗ suffix)
                       nothing pos (showNat-chars n ++ₗ suffix)
                       (optional-dash-fail-on-showNat pos n suffix)

      step-parseNat :
        (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing nₚ fd))
          pos (showNat-chars n ++ₗ suffix)
        ≡ (char '.' >>= λ _ → some digit >>= λ fd →
             pure (buildDecRat nothing n fd))
          posAfterNat suffix
      step-parseNat =
        bind-just-step parseNatural
                       (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                                pure (buildDecRat nothing nₚ fd))
                       pos (showNat-chars n ++ₗ suffix)
                       n posAfterNat suffix
                       (parseNatural-showNat-chars pos n suffix ss)

      step-dot-fails :
        (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat nothing n fd))
          posAfterNat suffix
        ≡ nothing
      step-dot-fails =
        bind-nothing-here (char '.')
                     (λ _ → some digit >>= λ fd →
                              pure (buildDecRat nothing n fd))
                     posAfterNat suffix
                     (char-dot-fail-on-non-dot posAfterNat suffix not-dot)

-- ----------------------------------------------------------------------------
-- Phase 6.6.6: parseDecRatFrac fails on the bare-int wire form (negative z)
-- ----------------------------------------------------------------------------

private
  parseDecRatFrac-fails-neg : ∀ n pos suffix →
    SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' →
    parseDecRatFrac pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix) ≡ nothing
  parseDecRatFrac-fails-neg n pos suffix ss not-dot =
    trans step-dash-succ
      (trans step-parseNat
        step-dot-fails)
    where
      posAfterDash : Position
      posAfterDash = advancePosition pos '-'

      posAfterNat : Position
      posAfterNat = advancePositions posAfterDash (showNat-chars (suc n))

      step-dash-succ :
        parseDecRatFrac pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix)
        ≡ (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
             pure (buildDecRat (just '-') nₚ fd))
          posAfterDash (showNat-chars (suc n) ++ₗ suffix)
      step-dash-succ =
        bind-just-step (optional (char '-'))
                       (λ neg → parseNatural >>= λ nₚ → char '.' >>= λ _ →
                                some digit >>= λ fd →
                                pure (buildDecRat neg nₚ fd))
                       pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix)
                       (just '-') posAfterDash
                       (showNat-chars (suc n) ++ₗ suffix)
                       (optional-dash-succ pos
                          (showNat-chars (suc n) ++ₗ suffix))

      step-parseNat :
        (parseNatural >>= λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat (just '-') nₚ fd))
          posAfterDash (showNat-chars (suc n) ++ₗ suffix)
        ≡ (char '.' >>= λ _ → some digit >>= λ fd →
             pure (buildDecRat (just '-') (suc n) fd))
          posAfterNat suffix
      step-parseNat =
        bind-just-step parseNatural
                       (λ nₚ → char '.' >>= λ _ → some digit >>= λ fd →
                                pure (buildDecRat (just '-') nₚ fd))
                       posAfterDash (showNat-chars (suc n) ++ₗ suffix)
                       (suc n) posAfterNat suffix
                       (parseNatural-showNat-chars posAfterDash (suc n) suffix ss)

      step-dot-fails :
        (char '.' >>= λ _ → some digit >>= λ fd →
           pure (buildDecRat (just '-') (suc n) fd))
          posAfterNat suffix
        ≡ nothing
      step-dot-fails =
        bind-nothing-here (char '.')
                     (λ _ → some digit >>= λ fd →
                              pure (buildDecRat (just '-') (suc n) fd))
                     posAfterNat suffix
                     (char-dot-fail-on-non-dot posAfterNat suffix not-dot)

-- ----------------------------------------------------------------------------
-- Phase 6.6.7: parseDecRatFrac dispatcher.  Public — used by 3c-B's
-- `Format/AttrValue.agda` for the inner-altSum disjointness witness when
-- the wire form is `RavwBareInt` (parseDecRatFrac arm of the inner altSum
-- must fail on bare-int input so the fall-through to intDecRat fires).
-- ----------------------------------------------------------------------------

parseDecRatFrac-fails-bareInt : ∀ z pos suffix →
  SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' →
  parseDecRatFrac pos (showInt-chars z ++ₗ suffix) ≡ nothing
parseDecRatFrac-fails-bareInt (ℤ+ n)        pos suffix ss not-dot =
  parseDecRatFrac-fails-+ n pos suffix ss not-dot
parseDecRatFrac-fails-bareInt ℤ-[1+ n ]     pos suffix ss not-dot =
  parseDecRatFrac-fails-neg n pos suffix ss not-dot

-- ----------------------------------------------------------------------------
-- Phase 6.6.8: parseDecRatBareInt success on the positive wire form
-- ----------------------------------------------------------------------------

private
  parseDecRatBareInt-roundtrip-+ : ∀ n pos suffix →
    SuffixStops isDigit suffix →
    parseDecRatBareInt pos (showNat-chars n ++ₗ suffix)
    ≡ just (mkResult (fromℤ (ℤ+ n))
                     (advancePositions pos (showNat-chars n))
                     suffix)
  parseDecRatBareInt-roundtrip-+ n pos suffix ss =
    trans step-dash-fail
      (trans step-parseNat
        step-build)
    where
      posAfterNat : Position
      posAfterNat = advancePositions pos (showNat-chars n)

      step-dash-fail :
        parseDecRatBareInt pos (showNat-chars n ++ₗ suffix)
        ≡ (parseNatural >>= λ nₚ →
             pure (buildDecRat nothing nₚ []))
          pos (showNat-chars n ++ₗ suffix)
      step-dash-fail =
        bind-just-step (optional (char '-'))
                       (λ neg → parseNatural >>= λ nₚ →
                                pure (buildDecRat neg nₚ []))
                       pos (showNat-chars n ++ₗ suffix)
                       nothing pos (showNat-chars n ++ₗ suffix)
                       (optional-dash-fail-on-showNat pos n suffix)

      step-parseNat :
        (parseNatural >>= λ nₚ →
           pure (buildDecRat nothing nₚ []))
          pos (showNat-chars n ++ₗ suffix)
        ≡ pure (buildDecRat nothing n [])
          posAfterNat suffix
      step-parseNat =
        bind-just-step parseNatural
                       (λ nₚ → pure (buildDecRat nothing nₚ []))
                       pos (showNat-chars n ++ₗ suffix)
                       n posAfterNat suffix
                       (parseNatural-showNat-chars pos n suffix ss)

      -- `buildDecRat nothing n []` reduces in two steps:
      -- (1) `applySign nothing _ = + _` (definitional);
      -- (2) `n * 10^0 + 0 ≡ n` via `*-identityʳ` + `+-identityʳ`.
      -- Then `canonicalizeDecRat (+ n) 0 0 ≡ fromℤ (+ n)` by Phase 6.6.2.
      step-build :
        pure (buildDecRat nothing n []) posAfterNat suffix
        ≡ just (mkResult (fromℤ (ℤ+ n)) posAfterNat suffix)
      step-build = cong (λ d → just (mkResult d posAfterNat suffix))
                        (trans build-reduce (canonicalizeDecRat-zero-exp (ℤ+ n)))
        where
          build-reduce : buildDecRat nothing n [] ≡ canonicalizeDecRat (ℤ+ n) 0 0
          build-reduce =
            cong (λ x → canonicalizeDecRat (ℤ+ x) 0 0)
                 (trans (cong (_+ 0) (*-identityʳ n)) (+-identityʳ n))

-- ----------------------------------------------------------------------------
-- Phase 6.6.9: parseDecRatBareInt success on the negative wire form
-- ----------------------------------------------------------------------------

private
  parseDecRatBareInt-roundtrip-neg : ∀ n pos suffix →
    SuffixStops isDigit suffix →
    parseDecRatBareInt pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix)
    ≡ just (mkResult (fromℤ ℤ-[1+ n ])
                     (advancePositions pos
                        ('-' ∷ showNat-chars (suc n)))
                     suffix)
  parseDecRatBareInt-roundtrip-neg n pos suffix ss =
    trans step-dash-succ
      (trans step-parseNat
        (trans step-build pos-eq))
    where
      posAfterDash : Position
      posAfterDash = advancePosition pos '-'

      posAfterNat : Position
      posAfterNat = advancePositions posAfterDash (showNat-chars (suc n))

      step-dash-succ :
        parseDecRatBareInt pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix)
        ≡ (parseNatural >>= λ nₚ →
             pure (buildDecRat (just '-') nₚ []))
          posAfterDash (showNat-chars (suc n) ++ₗ suffix)
      step-dash-succ =
        bind-just-step (optional (char '-'))
                       (λ neg → parseNatural >>= λ nₚ →
                                pure (buildDecRat neg nₚ []))
                       pos ('-' ∷ showNat-chars (suc n) ++ₗ suffix)
                       (just '-') posAfterDash
                       (showNat-chars (suc n) ++ₗ suffix)
                       (optional-dash-succ pos
                          (showNat-chars (suc n) ++ₗ suffix))

      step-parseNat :
        (parseNatural >>= λ nₚ →
           pure (buildDecRat (just '-') nₚ []))
          posAfterDash (showNat-chars (suc n) ++ₗ suffix)
        ≡ pure (buildDecRat (just '-') (suc n) [])
          posAfterNat suffix
      step-parseNat =
        bind-just-step parseNatural
                       (λ nₚ → pure (buildDecRat (just '-') nₚ []))
                       posAfterDash (showNat-chars (suc n) ++ₗ suffix)
                       (suc n) posAfterNat suffix
                       (parseNatural-showNat-chars posAfterDash (suc n) suffix ss)

      -- Same reduction structure as the positive case but routed through
      -- `applySign (just _) (suc m) = -[1+ m ]`.  Definitional steps:
      -- `suc n * 10^0 + 0` → `suc (n * 1 + 0)` (via `*` / `+` clauses)
      -- → `applySign (just '-') (suc _) = -[1+ n * 1 + 0 ]`.  Then the
      -- ℕ-level identity bridges `n * 1 + 0 ≡ n`.
      step-build :
        pure (buildDecRat (just '-') (suc n) []) posAfterNat suffix
        ≡ just (mkResult (fromℤ ℤ-[1+ n ]) posAfterNat suffix)
      step-build = cong (λ d → just (mkResult d posAfterNat suffix))
                        (trans build-reduce (canonicalizeDecRat-zero-exp ℤ-[1+ n ]))
        where
          build-reduce : buildDecRat (just '-') (suc n) [] ≡ canonicalizeDecRat ℤ-[1+ n ] 0 0
          build-reduce =
            cong (λ x → canonicalizeDecRat ℤ-[1+ x ] 0 0)
                 (trans (cong (_+ 0) (*-identityʳ n)) (+-identityʳ n))

      pos-eq :
        just (mkResult (fromℤ ℤ-[1+ n ]) posAfterNat suffix)
        ≡ just (mkResult (fromℤ ℤ-[1+ n ])
                          (advancePositions pos ('-' ∷ showNat-chars (suc n)))
                          suffix)
      pos-eq = refl

-- ----------------------------------------------------------------------------
-- Phase 6.6.10: parseDecRatBareInt dispatcher
-- ----------------------------------------------------------------------------

private
  parseDecRatBareInt-roundtrip : ∀ z pos suffix →
    SuffixStops isDigit suffix →
    parseDecRatBareInt pos (showInt-chars z ++ₗ suffix)
    ≡ just (mkResult (fromℤ z)
                     (advancePositions pos (showInt-chars z))
                     suffix)
  parseDecRatBareInt-roundtrip (ℤ+ n)        pos suffix ss =
    parseDecRatBareInt-roundtrip-+ n pos suffix ss
  parseDecRatBareInt-roundtrip ℤ-[1+ n ]     pos suffix ss =
    parseDecRatBareInt-roundtrip-neg n pos suffix ss

-- ----------------------------------------------------------------------------
-- Phase 6.6.11: Public composer
-- ----------------------------------------------------------------------------

private
  alt-right-nothing-here :
    ∀ {A : Set} (p q : Parser A) (pos : Position) (input : List Char)
    → p pos input ≡ nothing
    → (p <|> q) pos input ≡ q pos input
  alt-right-nothing-here p q pos input eq with p pos input | eq
  ... | nothing | refl = refl

parseDecRat-bareInt-roundtrip-suffix : ∀ z pos suffix →
  SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' →
  parseDecRat pos (showInt-chars z ++ₗ suffix)
    ≡ just (mkResult (fromℤ z)
                     (advancePositions pos (showInt-chars z))
                     suffix)
parseDecRat-bareInt-roundtrip-suffix z pos suffix ss not-dot =
  trans (alt-right-nothing-here parseDecRatFrac parseDecRatBareInt
           pos (showInt-chars z ++ₗ suffix)
           (parseDecRatFrac-fails-bareInt z pos suffix ss not-dot))
        (parseDecRatBareInt-roundtrip z pos suffix ss)

-- ============================================================================
-- Phase 6.7: Refined-parser roundtrips — parseIntDecRat / parseNatDecRat
-- ============================================================================
--
-- `parseIntDecRat = parseDecRat >>= λ d → ifᵀ isIntegerᵇ d then ...
--                                        else fail`.  On the wire form
-- `showInt-chars (intDecRatToℤ v)`, the `parseDecRat` step succeeds via
-- `parseDecRat-bareInt-roundtrip-suffix` (Phase 6.6) producing
-- `fromℤ (intDecRatToℤ v)`.  The `ifᵀ` then routes through `isIntegerᵇ-
-- fromℤ` (always `true`) into the `pure (mkIntDecRat (fromℤ z) wf)`
-- branch.  Witness collapse: `mkIntDecRat (fromℤ z) wf ≡
-- mkIntDecRatFromℤ z`, then `mkIntDecRatFromℤ-intDecRatToℤ` recovers
-- the original `v`.
--
-- `parseNatDecRat` mirrors the structure with `isNonNegIntegerᵇ` and
-- `mkNatDecRatFromℕ-natDecRatToℕ`.

parseIntDecRat-roundtrip-suffix : ∀ v pos suffix
  → SuffixStops isDigit suffix → '.' ≢ headOr suffix '_'
  → parseIntDecRat pos (showInt-chars (intDecRatToℤ v) ++ₗ suffix)
    ≡ just (mkResult v
              (advancePositions pos (showInt-chars (intDecRatToℤ v)))
              suffix)
parseIntDecRat-roundtrip-suffix v pos suffix ss not-dot =
  trans step-bind (trans step-ifT step-recover-v)
  where
    z : ℤ
    z = intDecRatToℤ v

    pos' : Position
    pos' = advancePositions pos (showInt-chars z)

    pf : T (isIntegerᵇ (fromℤ z))
    pf = subst T (sym (isIntegerᵇ-fromℤ z)) tt

    -- bind step: parseDecRat reads `showInt-chars z` via Phase 6.6 and
    -- threads the resulting `fromℤ z` into the `ifᵀ` continuation.
    step-bind :
      parseIntDecRat pos (showInt-chars z ++ₗ suffix)
      ≡ (ifᵀ isIntegerᵇ (fromℤ z)
            then (λ wf → pure (mkIntDecRat (fromℤ z) wf))
            else fail) pos' suffix
    step-bind =
      bind-just-step parseDecRat
        (λ d → ifᵀ isIntegerᵇ d
                 then (λ wf → pure (mkIntDecRat d wf))
                 else fail)
        pos (showInt-chars z ++ₗ suffix)
        (fromℤ z) pos' suffix
        (parseDecRat-bareInt-roundtrip-suffix z pos suffix ss not-dot)

    -- ifᵀ step: pin the `T (isIntegerᵇ (fromℤ z))` witness via `pf`,
    -- collapsing the branch under `cong (_ pos' suffix)`.
    step-ifT :
      (ifᵀ isIntegerᵇ (fromℤ z)
          then (λ wf → pure (mkIntDecRat (fromℤ z) wf))
          else fail) pos' suffix
      ≡ pure (mkIntDecRat (fromℤ z) pf) pos' suffix
    step-ifT =
      cong (λ p → p pos' suffix)
           (ifᵀ-witness (λ wf → pure (mkIntDecRat (fromℤ z) wf)) fail pf)

    -- Recover `v`: `mkIntDecRat (fromℤ z) pf ≡ mkIntDecRatFromℤ z`
    -- (definitional — `mkIntDecRatFromℤ` is exactly that record literal),
    -- then `mkIntDecRatFromℤ-intDecRatToℤ v` closes.
    step-recover-v :
      pure (mkIntDecRat (fromℤ z) pf) pos' suffix
      ≡ just (mkResult v pos' suffix)
    step-recover-v =
      cong (λ x → just (mkResult x pos' suffix))
           (mkIntDecRatFromℤ-intDecRatToℤ v)

-- `showNat-chars n = showInt-chars (+ n)` definitionally; reuse the
-- bareInt roundtrip via `(+ natDecRatToℕ v) : ℤ`.  Witness flips to
-- `isNonNegIntegerᵇ-fromℕ`, recovery via `mkNatDecRatFromℕ-natDecRatToℕ`.
parseNatDecRat-roundtrip-suffix : ∀ v pos suffix
  → SuffixStops isDigit suffix → '.' ≢ headOr suffix '_'
  → parseNatDecRat pos (showNat-chars (natDecRatToℕ v) ++ₗ suffix)
    ≡ just (mkResult v
              (advancePositions pos (showNat-chars (natDecRatToℕ v)))
              suffix)
parseNatDecRat-roundtrip-suffix v pos suffix ss not-dot =
  trans step-bind (trans step-ifT step-recover-v)
  where
    n : ℕ
    n = natDecRatToℕ v

    pos' : Position
    pos' = advancePositions pos (showNat-chars n)

    pf : T (isNonNegIntegerᵇ (fromℤ (ℤ+ n)))
    pf = subst T (sym (isNonNegIntegerᵇ-fromℕ n)) tt

    step-bind :
      parseNatDecRat pos (showNat-chars n ++ₗ suffix)
      ≡ (ifᵀ isNonNegIntegerᵇ (fromℤ (ℤ+ n))
            then (λ wf → pure (mkNatDecRat (fromℤ (ℤ+ n)) wf))
            else fail) pos' suffix
    step-bind =
      bind-just-step parseDecRat
        (λ d → ifᵀ isNonNegIntegerᵇ d
                 then (λ wf → pure (mkNatDecRat d wf))
                 else fail)
        pos (showNat-chars n ++ₗ suffix)
        (fromℤ (ℤ+ n)) pos' suffix
        (parseDecRat-bareInt-roundtrip-suffix (ℤ+ n) pos suffix ss not-dot)

    step-ifT :
      (ifᵀ isNonNegIntegerᵇ (fromℤ (ℤ+ n))
          then (λ wf → pure (mkNatDecRat (fromℤ (ℤ+ n)) wf))
          else fail) pos' suffix
      ≡ pure (mkNatDecRat (fromℤ (ℤ+ n)) pf) pos' suffix
    step-ifT =
      cong (λ p → p pos' suffix)
           (ifᵀ-witness (λ wf → pure (mkNatDecRat (fromℤ (ℤ+ n)) wf)) fail pf)

    step-recover-v :
      pure (mkNatDecRat (fromℤ (ℤ+ n)) pf) pos' suffix
      ≡ just (mkResult v pos' suffix)
    step-recover-v =
      cong (λ x → just (mkResult x pos' suffix))
           (mkNatDecRatFromℕ-natDecRatToℕ v)
