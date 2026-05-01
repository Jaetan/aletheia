{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4b — polymorphic `many P` roundtrip helper.
--
-- Lifts a per-element η-style slim roundtrip (one of the five sections —
-- ValueTable, EnvVar, Comment, SignalGroup, DBCMessage) to its `many P`
-- list-level analogue.  Each section's parser has the η-shape
--
--     parseX = parse fmtX >>= λ x → many parseNewline >>= λ _ → pure x
--
-- and the section emitter is `foldr (λ x acc → emitX-chars x ++ acc) []`.
-- All five share a uniform list-level proof structure modulo the per-
-- element precondition (`Stop : X → Set`); this module factors that
-- shared structure into a single helper and a tiny instantiation API.
--
-- Composition strategy: induct on the *element list* `xs`, with fuel
-- `n` bounded by `length xs ≤ n` (advisor's element-count fuel choice
-- — bytes-bound forces arithmetic at every cons step, element-count
-- gives a clean `length (x ∷ rest) ≤ suc n' ⇒ length rest ≤ n'`
-- handoff to the IH).  Empty case: `manyHelper-P-fails` (any-fuel
-- exhaust on `P pos outer ≡ nothing`).  Cons case: `manyHelper-prog-
-- cons` (Preamble.Newline) + slim `P-on-emit` + `sameLengthᵇ-app-nz`
-- (this module) + IH.  Position bridge via `advancePositions-++`.
module Aletheia.DBC.TextParser.Properties.ManyRoundtrip where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; foldr; length; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (length-++)
  renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using
  (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using
  (m≤n+m; m≤m+n; <⇒≢; ≤-trans; ≤-step; +-mono-≤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult;
   advancePositions; many; manyHelper; sameLengthᵇ)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; advancePositions-++)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-prog-cons)


-- ============================================================================
-- AUXILIARY: `sameLengthᵇ` discharge for non-empty prefix
-- ============================================================================

-- `sameLengthᵇ xs ys = false` whenever `length xs ≢ length ys`.
-- Structural double-induction on `xs` and `ys`.
private
  sameLengthᵇ-len-≢ : ∀ {A : Set} (xs ys : List A) →
    length xs ≢ length ys → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-len-≢ []       []       neq = ⊥-elim (neq refl)
  sameLengthᵇ-len-≢ []       (_ ∷ _)  _   = refl
  sameLengthᵇ-len-≢ (_ ∷ _)  []       _   = refl
  sameLengthᵇ-len-≢ (_ ∷ xs) (_ ∷ ys) neq =
    sameLengthᵇ-len-≢ xs ys (λ eq → neq (cong suc eq))

-- `length ((x ∷ xs) ++ ys) ≢ length ys` — strict-bigger by 1 + length xs.
-- Routes through stdlib's `length-++` + `m≤n+m` + `<⇒≢`.
private
  length-cons-app-≢ : ∀ {A : Set} (x : A) (xs ys : List A) →
    length ((x ∷ xs) ++ₗ ys) ≢ length ys
  length-cons-app-≢ x xs ys eq =
    <⇒≢ (s≤s (m≤n+m (length ys) (length xs)))
        (trans (sym eq) (length-++ (x ∷ xs)))

-- `sameLengthᵇ ((x ∷ xs) ++ ys) ys ≡ false` — workhorse for the cons-case
-- progress check inside `manyHelper-prog-cons`.  Each section's `E x` is
-- non-empty (closed-form prefix `"VAL_TABLE_ "` / `"BO_ "` / `"CM_ "` /
-- `"EV_ "` / `"SIG_GROUP_ "`), so the helper specialises with `E x` in
-- the `(x ∷ xs)` slot.
sameLengthᵇ-app-nz : ∀ {A : Set} (xs ys : List A) →
  0 < length xs →
  sameLengthᵇ (xs ++ₗ ys) ys ≡ false
sameLengthᵇ-app-nz []       _  ()
sameLengthᵇ-app-nz (x ∷ xs) ys _  =
  sameLengthᵇ-len-≢ ((x ∷ xs) ++ₗ ys) ys (length-cons-app-≢ x xs ys)


-- ============================================================================
-- AUXILIARY: empty-case `manyHelper` exhaust
-- ============================================================================

-- `manyHelper P pos input n ≡ just (mkResult [] pos input)` whenever
-- `P pos input ≡ nothing`.  Parametric in fuel — works at zero (vacuous
-- by definition) or `suc n'` (rewrite the parser's `nothing` result).
manyHelper-P-fails : ∀ {A : Set} (P : Parser A)
                       (pos : Position) (input : List Char) (n : ℕ)
  → P pos input ≡ nothing
  → manyHelper P pos input n ≡ just (mkResult [] pos input)
manyHelper-P-fails _ _ _ zero    _  = refl
manyHelper-P-fails _ _ _ (suc _) eq rewrite eq = refl


-- ============================================================================
-- POLYMORPHIC HELPER: `many P` roundtrip from per-element slim
-- ============================================================================

-- Internal core: the proof at a specific fuel level `n`.  Top-level
-- `many-η-roundtrip` calls this with `n = length input` (which is ≥
-- `length xs` since each `E x` consumes ≥ 1 char).
--
-- Parameters:
--   * `P : Parser X`         — the slim parser (`parseValueTable`, …)
--   * `E : X → List Char`    — the slim emitter (`emitValueTable-chars`, …)
--   * `Stop : X → Set`       — per-element precondition
--   * `P-on-emit`            — slim roundtrip lemma
--   * `E-nonzero`            — `0 < length (E x)` (each emit is ≥ 1 char)
--   * `E-head-not-newline`   — head of `E x` is not a newline-start;
--                              discharges the inter-element `SuffixStops`
--                              passed to per-element `P-on-emit`
--   * `pos`                  — starting position
--   * `xs : List X`          — element list
--   * `outer-suffix`         — bytes after the final element
--   * `n`                    — fuel; must be ≥ `length xs`
--   * `xs-stops : All Stop xs`
--   * `outer-stop`           — `SuffixStops isNewlineStart outer-suffix`
--   * `P-fails-outer`        — `P pos' outer-suffix ≡ nothing` ∀ pos'
many-η-roundtrip-helper :
    ∀ {X : Set}
      (P : Parser X) (E : X → List Char) (Stop : X → Set)
    → (P-on-emit :
          ∀ (pos : Position) (x : X) (suffix : List Char)
        → Stop x
        → SuffixStops isNewlineStart suffix
        → P pos (E x ++ₗ suffix)
          ≡ just (mkResult x (advancePositions pos (E x)) suffix))
    → (E-nonzero : ∀ (x : X) → 0 < length (E x))
    → (E-head-not-newline :
          ∀ (x : X) (suffix : List Char)
        → SuffixStops isNewlineStart (E x ++ₗ suffix))
    → ∀ (pos : Position) (xs : List X) (outer-suffix : List Char) (n : ℕ)
    → length xs ≤ n
    → All Stop xs
    → SuffixStops isNewlineStart outer-suffix
    → (∀ (pos' : Position) → P pos' outer-suffix ≡ nothing)
    → manyHelper P pos
                 (foldr (λ x acc → E x ++ₗ acc) [] xs ++ₗ outer-suffix)
                 n
      ≡ just (mkResult xs
               (advancePositions pos
                 (foldr (λ x acc → E x ++ₗ acc) [] xs))
               outer-suffix)
many-η-roundtrip-helper P E Stop rt nz hns
                        pos [] outer n _ [] os pf =
  manyHelper-P-fails P pos outer n (pf pos)
many-η-roundtrip-helper P E Stop rt nz hns
                        pos (x ∷ rest) outer (suc n') (s≤s rest≤n')
                        (sx ∷ srest) os pf =
  -- Spine bridge: associate `(E x ++ rest-input) ++ outer` to
  -- `E x ++ (rest-input ++ outer)` so `manyHelper-prog-cons` can fire.
  trans
    (cong (λ inp → manyHelper P pos inp (suc n'))
          (++ₗ-assoc (E x) rest-input outer))
    (trans
      (manyHelper-prog-cons P pos (E x ++ₗ (rest-input ++ₗ outer)) n'
        x posx (rest-input ++ₗ outer) rest pos-out outer
        peq sleq hpeq)
      (cong (λ p → just (mkResult (x ∷ rest) p outer)) pos-bridge))
  where
    rest-input : List Char
    rest-input = foldr (λ y acc → E y ++ₗ acc) [] rest

    posx : Position
    posx = advancePositions pos (E x)

    pos-out : Position
    pos-out = advancePositions posx rest-input

    -- `P pos (E x ++ rest-input ++ outer)` reduces via `P-on-emit`,
    -- with the inner suffix (`rest-input ++ outer`) discharging
    -- `SuffixStops isNewlineStart` either via `os` (if rest = [], so
    -- inner = outer) or via `E-head-not-newline (head rest) ...` (if
    -- rest = next ∷ rest', so inner = E next ++ ...).
    inner-stop-aux : (ys : List _) →
      SuffixStops isNewlineStart
        (foldr (λ y acc → E y ++ₗ acc) [] ys ++ₗ outer)
    inner-stop-aux []           = os
    inner-stop-aux (next ∷ ys') =
      subst (SuffixStops isNewlineStart)
            (sym (++ₗ-assoc (E next)
                   (foldr (λ y acc → E y ++ₗ acc) [] ys') outer))
            (hns next (foldr (λ y acc → E y ++ₗ acc) [] ys' ++ₗ outer))

    inner-stop : SuffixStops isNewlineStart (rest-input ++ₗ outer)
    inner-stop = inner-stop-aux rest

    peq : P pos (E x ++ₗ (rest-input ++ₗ outer))
          ≡ just (mkResult x posx (rest-input ++ₗ outer))
    peq = rt pos x (rest-input ++ₗ outer) sx inner-stop

    -- `sameLengthᵇ` between `E x ++ rest` and `rest` is false because
    -- `length (E x) ≥ 1`.
    sleq : sameLengthᵇ (E x ++ₗ (rest-input ++ₗ outer))
                       (rest-input ++ₗ outer)
           ≡ false
    sleq = sameLengthᵇ-app-nz (E x) (rest-input ++ₗ outer) (nz x)

    -- IH: `manyHelper P posx (rest-input ++ outer) n' ≡ ...`.
    hpeq : manyHelper P posx (rest-input ++ₗ outer) n'
           ≡ just (mkResult rest pos-out outer)
    hpeq = many-η-roundtrip-helper P E Stop rt nz hns
             posx rest outer n' rest≤n' srest os pf

    -- Position bridge: `pos-out = advancePositions posx rest-input
    -- = advancePositions pos (E x ++ rest-input)` by `advancePositions-++`.
    pos-bridge : pos-out
      ≡ advancePositions pos
          (foldr (λ y acc → E y ++ₗ acc) [] (x ∷ rest))
    pos-bridge = sym (advancePositions-++ pos (E x) rest-input)


-- ============================================================================
-- TOP-LEVEL: `many P` roundtrip — discharges the fuel obligation
-- ============================================================================

-- `length xs ≤ length (foldr ... [] xs)` — each `E xᵢ` ≥ 1 char.
-- Then `length emit ≤ length (emit ++ outer)` by `m≤m+n`.
private
  length-xs-≤-emit :
      ∀ {X : Set} (E : X → List Char)
    → (∀ x → 0 < length (E x))
    → ∀ (xs : List X)
    → length xs ≤ length (foldr (λ x acc → E x ++ₗ acc) [] xs)
  length-xs-≤-emit E nz []          = z≤n
  length-xs-≤-emit E nz (x ∷ rest)  =
    subst (suc (length rest) ≤_)
          (sym (length-++ (E x)))
          (+-mono-≤ (nz x) (length-xs-≤-emit E nz rest))

  length-xs-≤-bytes :
      ∀ {X : Set} (E : X → List Char)
    → (E-nonzero : ∀ x → 0 < length (E x))
    → ∀ (xs : List X) (outer : List Char)
    → length xs
      ≤ length (foldr (λ x acc → E x ++ₗ acc) [] xs ++ₗ outer)
  length-xs-≤-bytes E nz xs outer =
    subst (length xs ≤_)
          (sym (length-++ (foldr (λ x acc → E x ++ₗ acc) [] xs) {ys = outer}))
          (≤-trans (length-xs-≤-emit E nz xs) (m≤m+n _ _))


many-η-roundtrip :
    ∀ {X : Set}
      (P : Parser X) (E : X → List Char) (Stop : X → Set)
    → (P-on-emit :
          ∀ (pos : Position) (x : X) (suffix : List Char)
        → Stop x
        → SuffixStops isNewlineStart suffix
        → P pos (E x ++ₗ suffix)
          ≡ just (mkResult x (advancePositions pos (E x)) suffix))
    → (E-nonzero : ∀ (x : X) → 0 < length (E x))
    → (E-head-not-newline :
          ∀ (x : X) (suffix : List Char)
        → SuffixStops isNewlineStart (E x ++ₗ suffix))
    → ∀ (pos : Position) (xs : List X) (outer-suffix : List Char)
    → All Stop xs
    → SuffixStops isNewlineStart outer-suffix
    → (∀ (pos' : Position) → P pos' outer-suffix ≡ nothing)
    → many P pos
        (foldr (λ x acc → E x ++ₗ acc) [] xs ++ₗ outer-suffix)
      ≡ just (mkResult xs
               (advancePositions pos
                 (foldr (λ x acc → E x ++ₗ acc) [] xs))
               outer-suffix)
many-η-roundtrip P E Stop rt nz hns pos xs outer xs-stops os pf =
  many-η-roundtrip-helper P E Stop rt nz hns
    pos xs outer (length input) (length-xs-≤-bytes E nz xs outer)
    xs-stops os pf
  where
    input : List Char
    input = foldr (λ x acc → E x ++ₗ acc) [] xs ++ₗ outer


-- ============================================================================
-- LIFT-AWARE VARIANT (B.3.d Layer 4c) — `many P` over a foldr-emit where
-- the parser yields `O` and the emitter consumes `I`, with a lift `L : I
-- → O`.  The result list is `map L xs`.  The 4b `many-η-roundtrip` is
-- the special case `I = O`, `L = id`.
--
-- Used by Layer 4c to lift `many parseTopStmt` over the body bytes
-- emitted from a `List TopStmtTyped` (typed shadow), where
-- `liftTopStmt defs : TopStmtTyped → TopStmt` routes attributes through
-- `rawOf defs`.  The 4b helper does not apply directly because parsed-
-- type ≠ input-type for attributes (parser yields RawDBCAttribute,
-- emitter consumes typed DBCAttribute via `emitAttribute-chars defs`).
-- ============================================================================

many-η-roundtrip-with-lift-helper :
    ∀ {I O : Set}
      (P : Parser O) (E : I → List Char) (Stop : I → Set) (L : I → O)
    → (P-on-emit :
          ∀ (pos : Position) (i : I) (suffix : List Char)
        → Stop i
        → SuffixStops isNewlineStart suffix
        → P pos (E i ++ₗ suffix)
          ≡ just (mkResult (L i) (advancePositions pos (E i)) suffix))
    → (E-nonzero : ∀ (i : I) → 0 < length (E i))
    → (E-head-not-newline :
          ∀ (i : I) (suffix : List Char)
        → SuffixStops isNewlineStart (E i ++ₗ suffix))
    → ∀ (pos : Position) (xs : List I) (outer-suffix : List Char) (n : ℕ)
    → length xs ≤ n
    → All Stop xs
    → SuffixStops isNewlineStart outer-suffix
    → (∀ (pos' : Position) → P pos' outer-suffix ≡ nothing)
    → manyHelper P pos
                 (foldr (λ i acc → E i ++ₗ acc) [] xs ++ₗ outer-suffix)
                 n
      ≡ just (mkResult (map L xs)
               (advancePositions pos
                 (foldr (λ i acc → E i ++ₗ acc) [] xs))
               outer-suffix)
many-η-roundtrip-with-lift-helper P E Stop L rt nz hns
                                  pos [] outer n _ [] os pf =
  manyHelper-P-fails P pos outer n (pf pos)
many-η-roundtrip-with-lift-helper P E Stop L rt nz hns
                                  pos (i ∷ rest) outer (suc n') (s≤s rest≤n')
                                  (sx ∷ srest) os pf =
  trans
    (cong (λ inp → manyHelper P pos inp (suc n'))
          (++ₗ-assoc (E i) rest-input outer))
    (trans
      (manyHelper-prog-cons P pos (E i ++ₗ (rest-input ++ₗ outer)) n'
        (L i) posx (rest-input ++ₗ outer) (map L rest) pos-out outer
        peq sleq hpeq)
      (cong (λ p → just (mkResult (L i ∷ map L rest) p outer)) pos-bridge))
  where
    rest-input : List Char
    rest-input = foldr (λ y acc → E y ++ₗ acc) [] rest

    posx : Position
    posx = advancePositions pos (E i)

    pos-out : Position
    pos-out = advancePositions posx rest-input

    inner-stop-aux : (ys : List _) →
      SuffixStops isNewlineStart
        (foldr (λ y acc → E y ++ₗ acc) [] ys ++ₗ outer)
    inner-stop-aux []           = os
    inner-stop-aux (next ∷ ys') =
      subst (SuffixStops isNewlineStart)
            (sym (++ₗ-assoc (E next)
                   (foldr (λ y acc → E y ++ₗ acc) [] ys') outer))
            (hns next (foldr (λ y acc → E y ++ₗ acc) [] ys' ++ₗ outer))

    inner-stop : SuffixStops isNewlineStart (rest-input ++ₗ outer)
    inner-stop = inner-stop-aux rest

    peq : P pos (E i ++ₗ (rest-input ++ₗ outer))
          ≡ just (mkResult (L i) posx (rest-input ++ₗ outer))
    peq = rt pos i (rest-input ++ₗ outer) sx inner-stop

    sleq : sameLengthᵇ (E i ++ₗ (rest-input ++ₗ outer))
                       (rest-input ++ₗ outer)
           ≡ false
    sleq = sameLengthᵇ-app-nz (E i) (rest-input ++ₗ outer) (nz i)

    hpeq : manyHelper P posx (rest-input ++ₗ outer) n'
           ≡ just (mkResult (map L rest) pos-out outer)
    hpeq = many-η-roundtrip-with-lift-helper P E Stop L rt nz hns
             posx rest outer n' rest≤n' srest os pf

    pos-bridge : pos-out
      ≡ advancePositions pos
          (foldr (λ y acc → E y ++ₗ acc) [] (i ∷ rest))
    pos-bridge = sym (advancePositions-++ pos (E i) rest-input)


many-η-roundtrip-with-lift :
    ∀ {I O : Set}
      (P : Parser O) (E : I → List Char) (Stop : I → Set) (L : I → O)
    → (P-on-emit :
          ∀ (pos : Position) (i : I) (suffix : List Char)
        → Stop i
        → SuffixStops isNewlineStart suffix
        → P pos (E i ++ₗ suffix)
          ≡ just (mkResult (L i) (advancePositions pos (E i)) suffix))
    → (E-nonzero : ∀ (i : I) → 0 < length (E i))
    → (E-head-not-newline :
          ∀ (i : I) (suffix : List Char)
        → SuffixStops isNewlineStart (E i ++ₗ suffix))
    → ∀ (pos : Position) (xs : List I) (outer-suffix : List Char)
    → All Stop xs
    → SuffixStops isNewlineStart outer-suffix
    → (∀ (pos' : Position) → P pos' outer-suffix ≡ nothing)
    → many P pos
        (foldr (λ i acc → E i ++ₗ acc) [] xs ++ₗ outer-suffix)
      ≡ just (mkResult (map L xs)
               (advancePositions pos
                 (foldr (λ i acc → E i ++ₗ acc) [] xs))
               outer-suffix)
many-η-roundtrip-with-lift P E Stop L rt nz hns pos xs outer xs-stops os pf =
  many-η-roundtrip-with-lift-helper P E Stop L rt nz hns
    pos xs outer (length input) (length-xs-≤-bytes E nz xs outer)
    xs-stops os pf
  where
    input : List Char
    input = foldr (λ x acc → E x ++ₗ acc) [] xs ++ₗ outer
