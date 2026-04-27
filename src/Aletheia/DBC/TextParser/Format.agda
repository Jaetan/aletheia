{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 — 3d.5.a — Format DSL framework core (minimum viable kit).
--
-- An inductive `Format A` describes a bidirectional `emit`/`parse` pair.
-- The universal `roundtrip` theorem (proven once, below) replaces the
-- 3a–3d.3 pattern of a hand-written ~500–2000 LOC roundtrip per construct.
-- Gate target for 3d.5.b: re-prove parseValueTable (currently 790 LOC) in
-- this DSL with the proof shrinking to <100 LOC.
--
-- Method (per advisor, examples-first): three constructors — `literal`,
-- `ident`, `pair` — derived from four hand-written concrete proofs (L1–L4).
-- The SuffixStops-isIdentCont hypothesis recurred in L3 and L4, satisfying
-- the ≥2× rule for generalisation, after which the universal `roundtrip`
-- captures every pattern.  L1–L4 remain at the bottom as one-liner
-- regression tests delegating to `roundtrip` — they're load-bearing tests:
-- if `roundtrip`'s shape ever drifts, they'll flag it.
--
-- Constructors deferred to 3d.5.b/c per parseValueTable's gate sketch:
-- `iso` (record assembly), `many` / `sepBy` (variable-length sequences),
-- `nat`, `stringLit`, whitespace combinators.  Add only what the sketch
-- demands; resist speculative growth.
module Aletheia.DBC.TextParser.Format where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePosition; advancePositions;
         parseCharsSeq; pure; _>>=_)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer using (parseIdentifier)
open import Aletheia.DBC.TextParser.Properties.Primitives
  using (parseCharsSeq-success; parseIdentifier-roundtrip)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; []-stop; ∷-stop; advancePositions-++; bind-just-step)

-- ============================================================================
-- FORMAT TYPE
-- ============================================================================

-- `Format A` is a bidirectional grammar fragment carrying values of type `A`.
-- The carrier type `A` is what `emit` consumes and `parse` returns.
--
-- Universe: `Set → Set₁` rather than `Set → Set` because `pair` quantifies
-- over `A B : Set` to compose sub-formats; that ∀-over-Set forces the
-- constructor's type into `Set₁`.  Could be flattened by indexing on a
-- finite `Code` data type with an explicit decoder, but that adds
-- boilerplate without buying expressiveness — the universe bump is free.
data Format : Set → Set₁ where
  -- Fixed-string literal: emits the chars verbatim, parses them by exact
  -- match.  Carrier is `⊤` (no information beyond presence).
  literal : List Char → Format ⊤
  -- Identifier (DBC identifier — `[A-Za-z_][A-Za-z0-9_]*`).  Stops on
  -- the first non-`isIdentCont` char.
  ident   : Format Identifier
  -- Sequence two formats; emit concatenates, parse runs in order.
  pair    : ∀ {A B} → Format A → Format B → Format (A × B)

-- ============================================================================
-- EMIT / PARSE
-- ============================================================================

emit : ∀ {A} → Format A → A → List Char
emit (literal cs) tt      = cs
emit ident        i       = Identifier.name i
emit (pair f g)   (a , b) = emit f a ++ₗ emit g b

parse : ∀ {A} → Format A → Parser A
parse (literal cs) = parseCharsSeq cs >>= λ _ → pure tt
parse ident        = parseIdentifier
parse (pair f g)   = parse f >>= λ a → parse g >>= λ b → pure (a , b)

-- ============================================================================
-- WELL-FORMEDNESS PREDICATE
-- ============================================================================

-- `EmitsOK f a suffix` is the structural well-formedness certificate for
-- the (format, value, suffix) triple — exactly what the user must prove
-- for the universal `roundtrip` to fire.  Computed by recursion on `f`,
-- so each Format constructor names its own side condition:
--
--   * literal: vacuous (literal is exact-match, no max-munch)
--   * ident:   the suffix must be isIdentCont-stopped (max-munch boundary)
--   * pair:    inner f's certificate against the augmented suffix
--              (`emit g b ++ outer-suffix`) AND outer g's certificate.
--
-- The recursive `emit g b ++ suffix` in the `pair` case is the lever that
-- lets the user discharge the inner-format SuffixStops constraint by
-- pointing at the head of `emit g b` — exactly what L4 (below) demands.
-- When future constructors land (`iso`, `many`, `sepBy`), they add new
-- lines here and to `roundtrip` below; the universal statement is stable.
EmitsOK : ∀ {A} → Format A → A → List Char → Set
EmitsOK (literal cs) tt      _      = ⊤
EmitsOK ident        _       suffix = SuffixStops isIdentCont suffix
EmitsOK (pair f g)   (a , b) suffix =
  EmitsOK f a (emit g b ++ₗ suffix) × EmitsOK g b suffix

-- ============================================================================
-- UNIVERSAL ROUNDTRIP THEOREM
-- ============================================================================

-- Every well-formed (format, value, suffix) triple roundtrips.  Proof
-- recurses structurally on `f`; the literal case delegates to
-- `parseCharsSeq-success`, ident to `parseIdentifier-roundtrip`, and the
-- pair case composes the two recursive calls via the same bind-chain
-- shape as L2–L4 below.
roundtrip : ∀ {A} (f : Format A) pos (a : A) (suffix : List Char)
  → EmitsOK f a suffix
  → parse f pos (emit f a ++ₗ suffix)
    ≡ just (mkResult a (advancePositions pos (emit f a)) suffix)
roundtrip (literal cs) pos tt suffix _ =
  bind-just-step (parseCharsSeq cs)
                 (λ _ → pure tt)
                 pos (cs ++ₗ suffix)
                 cs (advancePositions pos cs) suffix
                 (parseCharsSeq-success pos cs suffix)
roundtrip ident        pos i  suffix ss =
  parseIdentifier-roundtrip pos i suffix ss
roundtrip (pair f g)   pos (a , b) suffix (wf-f , wf-g) =
  trans (cong (parse (pair f g) pos)
              (++ₗ-assoc (emit f a) (emit g b) suffix))
    (trans step-f
      (trans step-g
        (cong (λ p → just (mkResult (a , b) p suffix))
              (sym (advancePositions-++ pos (emit f a) (emit g b))))))
  where
    pos-f = advancePositions pos (emit f a)
    pos-g = advancePositions pos-f (emit g b)

    step-f :
      parse (pair f g) pos (emit f a ++ₗ (emit g b ++ₗ suffix))
      ≡ (parse g >>= λ b' → pure (a , b')) pos-f (emit g b ++ₗ suffix)
    step-f =
      bind-just-step (parse f)
                     (λ a' → parse g >>= λ b' → pure (a' , b'))
                     pos (emit f a ++ₗ (emit g b ++ₗ suffix))
                     a pos-f (emit g b ++ₗ suffix)
                     (roundtrip f pos a (emit g b ++ₗ suffix) wf-f)

    step-g :
      (parse g >>= λ b' → pure (a , b')) pos-f (emit g b ++ₗ suffix)
      ≡ just (mkResult (a , b) pos-g suffix)
    step-g =
      bind-just-step (parse g)
                     (λ b' → pure (a , b'))
                     pos-f (emit g b ++ₗ suffix)
                     b pos-g suffix
                     (roundtrip g pos-f b suffix wf-g)

-- ============================================================================
-- REGRESSION TESTS — the four concrete proofs that motivated the abstraction
-- ============================================================================

-- L1–L4 below were hand-written first and used to derive the universal
-- `roundtrip`.  Now reproved as one-liners delegating to `roundtrip`; if
-- the universal's shape drifts (signature, EmitsOK structure, position
-- arithmetic), these will fail to type-check and pinpoint the regression.
-- Per advisor: "the strongest signal that the universal genuinely subsumes
-- the concrete cases."

-- L1: literal-only.  Witness: `tt : ⊤`.
roundtrip-literal : ∀ pos cs suffix
  → parse (literal cs) pos (cs ++ₗ suffix)
    ≡ just (mkResult tt (advancePositions pos cs) suffix)
roundtrip-literal pos cs suffix = roundtrip (literal cs) pos tt suffix tt

-- L2: pair of two literals.  Witness: `(tt , tt) : ⊤ × ⊤`.
roundtrip-pair-literal-literal : ∀ pos cs ds suffix
  → parse (pair (literal cs) (literal ds)) pos
      ((cs ++ₗ ds) ++ₗ suffix)
    ≡ just (mkResult (tt , tt) (advancePositions pos (cs ++ₗ ds)) suffix)
roundtrip-pair-literal-literal pos cs ds suffix =
  roundtrip (pair (literal cs) (literal ds)) pos (tt , tt) suffix (tt , tt)

-- L3: literal-then-ident.  Witness: `(tt , ss) : ⊤ × SuffixStops isIdentCont suffix`.
roundtrip-pair-literal-ident : ∀ pos cs i suffix
  → SuffixStops isIdentCont suffix
  → parse (pair (literal cs) ident) pos
      ((cs ++ₗ Identifier.name i) ++ₗ suffix)
    ≡ just (mkResult (tt , i)
             (advancePositions pos (cs ++ₗ Identifier.name i))
             suffix)
roundtrip-pair-literal-ident pos cs i suffix ss =
  roundtrip (pair (literal cs) ident) pos (tt , i) suffix (tt , ss)

-- L4: ident-then-literal.  Witness: `(ss , tt)` where `ss` carries the
-- compatibility hypothesis on the head of `ds ++ suffix` (this is the
-- shape that, recurring with L3's outer-SuffixStops, drove the
-- generalisation to `EmitsOK`).
roundtrip-pair-ident-literal : ∀ pos i ds suffix
  → SuffixStops isIdentCont (ds ++ₗ suffix)
  → parse (pair ident (literal ds)) pos
      ((Identifier.name i ++ₗ ds) ++ₗ suffix)
    ≡ just (mkResult (i , tt)
             (advancePositions pos (Identifier.name i ++ₗ ds))
             suffix)
roundtrip-pair-ident-literal pos i ds suffix ss =
  roundtrip (pair ident (literal ds)) pos (i , tt) suffix (ss , tt)
