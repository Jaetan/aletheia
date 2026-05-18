{-# OPTIONS --safe --without-K #-}

-- Phase 4 + 5 of the `parseDecRat` roundtrip proof — per-sign
-- branches + the suffix=[] top-level dispatcher
-- (`parseDecRatFrac-roundtrip`).  Carved out of the historical
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` mega-module
-- under the R21 cluster 9 split (closes AGDA-D-15.1 for this file).
--
-- Phase organisation:
--   * 4: Shared bind-chain helpers + per-sign branches (+ suc / neg / + zero).
--   * 5: Top-level dispatcher (`parseDecRatFrac-roundtrip`).
--
-- Suffix-aware variants live in Phase 6 (separate submodule).
--
-- Depends on Phases 1-3 (re-exports via `public open import`).
module Aletheia.DBC.TextParser.DecRatParse.Properties.Phase4Composition where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as EmptyI
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong₂)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult;
         advancePosition; advancePositions;
         digit; some;
         char; optional;
         _>>=_; pure)
open import Aletheia.DBC.TextFormatter.Emitter
  using (showNat-chars;
         emitMagnitude-chars; showDecRat-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse
  using (parseDecRatFrac; buildDecRat)
open import Aletheia.DBC.TextParser.Lexer using (parseNatural)
open import Data.Integer using (ℤ)
  renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Aletheia.DBC.DecRat
  using (mkDecRat; IsCanonical)

-- Phases 1-3 re-export base — every public lemma above is available.
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many   public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase3Naturals public

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
parseDecRatFrac-roundtrip-+suc : ∀ n a b pos
  .(cx : IsCanonical (suc n) a b) →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat (ℤ+ suc n) a b cx))
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
parseDecRatFrac-roundtrip-+suc n a b pos cx =
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
      parseDecRatFrac pos (emitMagnitude-chars (suc n) a b)
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
parseDecRatFrac-roundtrip-neg : ∀ n a b pos
  .(cx : IsCanonical (suc n) a b) →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx))
    ≡ just (mkResult (mkDecRat ℤ-[1+ n ] a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat ℤ-[1+ n ] a b cx)))
                     [])
parseDecRatFrac-roundtrip-neg n a b pos cx =
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
      parseDecRatFrac pos ('-' ∷ emitMagnitude-chars (suc n) a b)
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
parseDecRatFrac-roundtrip-+zero : ∀ a b pos
  .(cx : IsCanonical 0 a b) →
  parseDecRatFrac pos (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx))
    ≡ just (mkResult (mkDecRat (ℤ+ zero) a b cx)
                     (advancePositions pos
                        (showDecRat-dec-chars (mkDecRat (ℤ+ zero) a b cx)))
                     [])
parseDecRatFrac-roundtrip-+zero zero    zero    _   _  = refl
parseDecRatFrac-roundtrip-+zero zero    (suc _) _   cx = EmptyI.⊥-elim cx
parseDecRatFrac-roundtrip-+zero (suc _) _       _   cx = EmptyI.⊥-elim cx

-- ============================================================================
-- Phase 5: Top-level dispatcher
-- ============================================================================
--
-- Pattern-match on the numerator constructor (`+ zero` / `+ suc n` /
-- `-[1+ n ]`) and route to the corresponding per-branch theorem.
-- Each branch's theorem carries the same statement shape, so the
-- dispatcher is three one-liners.
parseDecRatFrac-roundtrip : ∀ d pos →
  parseDecRatFrac pos (showDecRat-dec-chars d)
    ≡ just (mkResult d (advancePositions pos (showDecRat-dec-chars d)) [])
parseDecRatFrac-roundtrip (mkDecRat (ℤ+ zero)  a b cx) pos =
  parseDecRatFrac-roundtrip-+zero a b pos cx
parseDecRatFrac-roundtrip (mkDecRat (ℤ+ suc n) a b cx) pos =
  parseDecRatFrac-roundtrip-+suc n a b pos cx
parseDecRatFrac-roundtrip (mkDecRat ℤ-[1+ n ]  a b cx) pos =
  parseDecRatFrac-roundtrip-neg n a b pos cx

