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

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Relation.Nullary using (yes; no)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (length-++) renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; n≤1+n; +-mono-≤)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePosition; advancePositions;
         parseCharsSeq; pure; _>>=_;
         manyHelper; sameLengthᵇ)
  renaming (many to many-parser)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer
  using (parseIdentifier; parseStringLit; parseNatural)
open import Aletheia.DBC.TextFormatter.Emitter
  using (showNat-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextParser.Properties.Primitives
  using (parseCharsSeq-success; parseIdentifier-roundtrip;
         parseStringLit-roundtrip)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; []-stop; ∷-stop; advancePositions-++; bind-just-step;
         parseNatural-showNat-chars)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline
  using (manyHelper-prog-cons)

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
  -- Natural number (decimal digits).  Stops on the first non-digit char.
  -- Delegates to `parseNatural` / `showNat-chars`.
  nat     : Format ℕ
  -- Quoted string literal (`"..."` with CSV-style `""` escape).  Stops
  -- on `"`.  Delegates to `parseStringLit` / `quoteStringLit-chars`.
  stringLit : Format (List Char)
  -- Sequence two formats; emit concatenates, parse runs in order.
  pair    : ∀ {A B} → Format A → Format B → Format (A × B)
  -- Zero-or-more repetitions of `f`.  `emit (many f)` is concat-map;
  -- `parse (many f)` delegates to the existing `Combinators.many`
  -- (renamed `many-parser` to avoid the constructor clash).  Each
  -- iteration must consume non-empty input (`0 < length (emit f x)`
  -- carried per-element in `EmitsOK`) so `manyHelper`'s `sameLengthᵇ`
  -- progress check passes; termination is via a user-provided
  -- `ParseFailsAt f suffix` certificate that says the trailing input
  -- doesn't start another `f`-match.
  many    : ∀ {A} → Format A → Format (List A)
  -- Carrier change via a total bijection.  `φ` lifts the inner value to
  -- the outer carrier (used by `parse`); `ψ` projects back (used by
  -- `emit`); the equation `∀ b → φ (ψ b) ≡ b` is the roundtrip law that
  -- makes the universal `roundtrip` discharge.  Used primarily for record
  -- assembly: `ψ` destructs the record into a tuple, the underlying pair
  -- structure carries the tuple, and `φ` reconstructs.  Both directions
  -- are typically `refl` by Agda's record-η rule.
  --
  -- Reserved for total bijections.  Refinement-typed carrier changes
  -- (`IntDecRat`, `NatDecRat`) need `refined : (P : A → Bool) → Format A
  -- → Format (Σ A (T ∘ P))` instead; asymmetric strips (e.g. discard a
  -- B-default) need `strip : (default-B : B) → Format (A × B) → Format
  -- A`.  Adding those when the gate sketch demands them, not before.
  iso     : ∀ {A B} (φ : A → B) (ψ : B → A)
          → (∀ b → φ (ψ b) ≡ b)
          → Format A → Format B
  -- Refinement carrier change.  Takes a Boolean predicate `P : A → Bool`
  -- and produces a Format whose carrier is `Σ A (T ∘ P)` — values paired
  -- with a witness that the predicate holds.  This is the constructor
  -- `iso` cannot express: `iso` requires a *total* inverse `φ : A → B`,
  -- but `A → Σ A (T ∘ P)` is partial — only defined when `P a` holds.
  --
  -- `parse` runs the underlying `f`, then decides `P` on the result; on
  -- `true` it lifts the value with the freshly-derived witness, on `false`
  -- it fails.  `emit` projects the value and discards the witness (the
  -- emitted string has no information about the predicate).
  --
  -- Universal roundtrip closes the witness slot via `T-irrelevant`: any
  -- two `T (P a)` proofs are propositionally equal, so the parse-derived
  -- witness equals the user's original.  Reserved for use through `iso`
  -- when the consumer wants a named record (e.g. `iso mkIntDecRat ψ
  -- (refined isIntegerᵇ <DecRat-format>)`); the Σ carrier is the universal
  -- shape and record-η discharges the iso roundtrip equation.
  refined : ∀ {A} (P : A → Bool) → Format A
          → Format (Σ A (λ a → T (P a)))

-- ============================================================================
-- EMIT / PARSE
-- ============================================================================

emit : ∀ {A} → Format A → A → List Char
emit (literal cs)     tt       = cs
emit ident            i        = Identifier.name i
emit nat              n        = showNat-chars n
emit stringLit        cs       = quoteStringLit-chars cs
emit (pair f g)       (a , b)  = emit f a ++ₗ emit g b
emit (iso _ ψ _ f)    b        = emit f (ψ b)
emit (many f)         xs       = concatMap (emit f) xs
emit (refined _ f)    (a , _)  = emit f a

-- `liftRefined` decides the refinement predicate on the value just parsed
-- by the underlying format, succeeding (with the synthesised witness) when
-- `P a` holds and failing otherwise.  Factored out of `parse (refined …)`
-- so that the universal roundtrip case can use `bind-just-step` on the
-- outer `parse f >>= …` and a separate lemma (`liftRefined-on-witness`,
-- below in `private`) on the predicate decision step.
--
-- Uses `T?` (decidable T) rather than a direct `with P a in eq`: the
-- `yes wit` branch immediately delivers a `wit : T (P a)`, which the
-- `Σ A (λ a → T (P a))` carrier accepts without needing to thread an
-- equation back through `subst T`.  A bare `with P a in eq` doesn't
-- typecheck because the with-elaboration generalises `P a` to a fresh
-- `Bool` variable that no longer matches the `Σ` carrier's type.
liftRefined : ∀ {A} (P : A → Bool) → A → Parser (Σ A (λ a → T (P a)))
liftRefined P a pos input with T? (P a)
... | yes wit = just (mkResult (a , wit) pos input)
... | no  _   = nothing

parse : ∀ {A} → Format A → Parser A
parse (literal cs)    = parseCharsSeq cs >>= λ _ → pure tt
parse ident           = parseIdentifier
parse nat             = parseNatural
parse stringLit       = parseStringLit
parse (pair f g)      = parse f >>= λ a → parse g >>= λ b → pure (a , b)
parse (iso φ _ _ f)   = parse f >>= λ a → pure (φ a)
parse (many f)        = many-parser (parse f)
parse (refined P f)   = parse f >>= liftRefined P

-- ============================================================================
-- PARSE-FAILS-AT — termination certificate for `many`
-- ============================================================================

-- `ParseFailsAt f suffix` certifies that the parser derived from `f`
-- rejects `suffix` at every starting position — i.e., no continuation
-- of a `many f` loop will accept this suffix.  Required for the
-- `EmitsOK (many f) [] suffix` and the trailing-suffix branch of the
-- non-empty case.  User-provided per-construct (cannot be derived from
-- a single `firstChar` predicate — the prototypical depth-2 failure
-- `parseValueEntry pos (' ' ∷ ';' ∷ rest)` wins on `' '` at the head
-- but loses two binds in when `parseNatural` rejects `';'`).
ParseFailsAt : ∀ {A} → Format A → List Char → Set
ParseFailsAt f suffix = ∀ pos → parse f pos suffix ≡ nothing

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
-- Forward declaration: `EmitsOKMany` is defined as an inductive predicate
-- below.  Splitting the list-induction (`xs`) into its own `data`
-- bypasses Agda's termination checker confusing the lex (Format size,
-- list length) recursion when both decrease across `EmitsOK`'s clauses.
data EmitsOKMany {A : Set} (f : Format A) : List A → List Char → Set

EmitsOK : ∀ {A} → Format A → A → List Char → Set
EmitsOK (literal cs)   tt       _      = ⊤
EmitsOK ident          _        suffix = SuffixStops isIdentCont suffix
EmitsOK nat            _        suffix = SuffixStops isDigit suffix
EmitsOK stringLit      _        suffix = SuffixStops (λ c → c ≈ᵇ '"') suffix
EmitsOK (pair f g)     (a , b)  suffix =
  EmitsOK f a (emit g b ++ₗ suffix) × EmitsOK g b suffix
EmitsOK (iso _ ψ _ f)  b        suffix = EmitsOK f (ψ b) suffix
EmitsOK (many f)       xs       suffix = EmitsOKMany f xs suffix
EmitsOK (refined _ f)  (a , _)  suffix = EmitsOK f a suffix

-- The list-induction of `EmitsOK (many f)`.  Recurses on the list `xs`
-- only; each `∷-cons` constructor carries the per-element well-formedness
-- (in `EmitsOK f x (...) × NonEmpty`) plus the recursive certificate.
data EmitsOKMany {A} f where
  []-fails : ∀ {suffix}
    → ParseFailsAt f suffix
    → EmitsOKMany f [] suffix
  ∷-cons   : ∀ {x xs suffix}
    → EmitsOK f x (emit (many f) xs ++ₗ suffix)
    → 0 < length (emit f x)
    → EmitsOKMany f xs suffix
    → EmitsOKMany f (x ∷ xs) suffix

-- ============================================================================
-- PRIVATE HELPERS — `many`'s roundtrip plumbing
-- ============================================================================

private
  -- `manyHelper` on a parser-failing input returns `[]` regardless of fuel.
  -- Drives the `[] / suc m'` branch of `manyHelper-roundtrip-list`.
  manyHelper-fails-stop : ∀ {A} (p : Parser A) (pos : Position)
                            (input : List Char) (n : ℕ)
    → p pos input ≡ nothing
    → manyHelper p pos input n ≡ just (mkResult [] pos input)
  manyHelper-fails-stop p pos input zero    _  = refl
  manyHelper-fails-stop p pos input (suc n) eq rewrite eq = refl

  -- `sameLengthᵇ` on lists of differing length returns `false`.  Mirrors
  -- the local copies in `Properties/Topology/Receivers.agda` and
  -- `Properties/ValueTables/ValueTable.agda`; not factored upstream
  -- because both sites still depend on the layered import order from
  -- the pre-DSL proofs.  3d.5.d migration may consolidate.
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys < length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (_ ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  -- `cs ++ rest` is strictly longer than `rest` whenever `cs` is non-empty.
  -- The progress witness `manyHelper`'s `sameLengthᵇ` check needs to
  -- conclude `false` and continue iteration.
  ++ₗ-strictly-longer : ∀ {A B : Set} (cs : List A) (rest : List B)
    → 0 < length cs
    → length rest < length cs + length rest
  ++ₗ-strictly-longer []       _    ()
  ++ₗ-strictly-longer (_ ∷ _)  rest _ = s≤s (m≤n+m (length rest) _)

  -- Lower bound on emit-many length, derived from per-element non-empty
  -- emit (carried in `EmitsOK (many f)`).  Used to discharge the fuel
  -- precondition of `manyHelper-roundtrip-list` at the outer call site.
  length-emit-many-bound : ∀ {A} (f : Format A) (xs : List A) (suffix : List Char)
    → EmitsOK (many f) xs suffix
    → length xs ≤ length (emit (many f) xs)
  length-emit-many-bound f []       suffix _                       = z≤n
  length-emit-many-bound f (x ∷ xs) suffix (∷-cons _ ne-x wf-xs)
    rewrite length-++ (emit f x) {emit (many f) xs} =
      +-mono-≤ ne-x (length-emit-many-bound f xs suffix wf-xs)

  -- `liftRefined` succeeds with the user's witness when the predicate
  -- decision matches.  Mirrors the `with T? (P a)` inside `liftRefined`'s
  -- definition; the `yes wit'` branch closes via `T-irrelevant` (any two
  -- `T (P a)` proofs are propositionally equal); the `no ¬wit'` branch
  -- is absurd because the user supplied a real `wit : T (P a)` that
  -- contradicts the refutation.
  liftRefined-on-witness : ∀ {A} (P : A → Bool) (a : A) (wit : T (P a))
                             (pos : Position) (input : List Char)
    → liftRefined P a pos input ≡ just (mkResult (a , wit) pos input)
  liftRefined-on-witness P a wit pos input with T? (P a)
  ... | yes wit' = cong (λ w' → just (mkResult (a , w') pos input))
                        (T-irrelevant wit' wit)
  ... | no  ¬wit = ⊥-elim (¬wit wit)

-- ============================================================================
-- UNIVERSAL ROUNDTRIP THEOREM (+ `many`'s manyHelper helper, mutual)
-- ============================================================================

-- `roundtrip` recurses structurally on `f`; `manyHelper-roundtrip-list`
-- (the per-list induction underlying the `many` case) calls `roundtrip f`
-- on the structurally-smaller inner format for each iteration.  The two
-- live in a `mutual` block so the cyclic call graph is accepted; lex
-- termination is `(Format size, list length)`.
mutual
  -- Every well-formed (format, value, suffix) triple roundtrips.  The
  -- literal case delegates to `parseCharsSeq-success`, ident to
  -- `parseIdentifier-roundtrip`, nat to `parseNatural-showNat-chars`,
  -- stringLit to `parseStringLit-roundtrip`, pair composes via the
  -- bind-chain shape from L2–L4, iso transports through `φ ∘ ψ ≡ id`,
  -- and many delegates to `manyHelper-roundtrip-list` below.
  roundtrip : ∀ {A} (f : Format A) pos (a : A) (suffix : List Char)
    → EmitsOK f a suffix
    → parse f pos (emit f a ++ₗ suffix)
      ≡ just (mkResult a (advancePositions pos (emit f a)) suffix)

  -- `manyHelper`-level roundtrip lemma, parametric over a Format.  Body
  -- mirrors `manyHelper-parseValueEntry-body` from
  -- `Properties/ValueTables/ValueTable.agda` but with `roundtrip f` in
  -- place of the per-construct iter-eq lemma.  Inducts on the list `xs`
  -- with fuel `m ≥ length xs`.  One iteration via `manyHelper-prog-cons`
  -- + recursive call on `xs`.
  manyHelper-roundtrip-list : ∀ {A} (f : Format A)
    (pos : Position) (xs : List A) (suffix : List Char) (m : ℕ)
    → length xs ≤ m
    → EmitsOK (many f) xs suffix
    → manyHelper (parse f) pos (emit (many f) xs ++ₗ suffix) m
      ≡ just (mkResult xs (advancePositions pos (emit (many f) xs)) suffix)

  roundtrip (literal cs) pos tt suffix _ =
    bind-just-step (parseCharsSeq cs)
                   (λ _ → pure tt)
                   pos (cs ++ₗ suffix)
                   cs (advancePositions pos cs) suffix
                   (parseCharsSeq-success pos cs suffix)
  roundtrip ident        pos i  suffix ss =
    parseIdentifier-roundtrip pos i suffix ss
  roundtrip nat          pos n  suffix ss =
    parseNatural-showNat-chars pos n suffix ss
  roundtrip stringLit    pos cs suffix ss =
    parseStringLit-roundtrip pos cs suffix ss
  roundtrip (iso φ ψ φψ-id f) pos b suffix wf =
    trans (bind-just-step (parse f)
                          (λ a → pure (φ a))
                          pos (emit f (ψ b) ++ₗ suffix)
                          (ψ b)
                          (advancePositions pos (emit f (ψ b)))
                          suffix
                          (roundtrip f pos (ψ b) suffix wf))
          (cong (λ x → just (mkResult x (advancePositions pos (emit f (ψ b))) suffix))
                (φψ-id b))
  roundtrip (refined P f) pos (a , w) suffix wf =
    trans (bind-just-step (parse f)
                          (liftRefined P)
                          pos (emit f a ++ₗ suffix)
                          a (advancePositions pos (emit f a)) suffix
                          (roundtrip f pos a suffix wf))
          (liftRefined-on-witness P a w
                                  (advancePositions pos (emit f a)) suffix)
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
  roundtrip (many f) pos xs suffix wf =
    manyHelper-roundtrip-list f pos xs suffix
      (length (emit (many f) xs ++ₗ suffix))
      fuel-bound
      wf
    where
      fuel-bound : length xs ≤ length (emit (many f) xs ++ₗ suffix)
      fuel-bound =
        ≤-trans (length-emit-many-bound f xs suffix wf)
                (subst (λ k → length (emit (many f) xs) ≤ k)
                       (sym (length-++ (emit (many f) xs) {suffix}))
                       (m≤m+n (length (emit (many f) xs)) (length suffix)))

  manyHelper-roundtrip-list f pos []       suffix m _ ([]-fails fails) =
    manyHelper-fails-stop (parse f) pos suffix m (fails pos)
  manyHelper-roundtrip-list f pos (x ∷ xs) suffix (suc m') (s≤s len-le)
                            (∷-cons wf-x ne-x wf-xs) =
    trans (cong (λ inp → manyHelper (parse f) pos inp (suc m')) input-eq)
      (trans (manyHelper-prog-cons (parse f) pos
                (emit f x ++ₗ iter-rest) m'
                x pos-x iter-rest
                xs (advancePositions pos-x (emit (many f) xs))
                suffix iter-eq sleq rec-eq)
        (cong (λ p → just (mkResult (x ∷ xs) p suffix)) pos-out-eq))
    where
      pos-x : Position
      pos-x = advancePositions pos (emit f x)

      iter-rest : List Char
      iter-rest = emit (many f) xs ++ₗ suffix

      iter-eq : parse f pos (emit f x ++ₗ iter-rest)
              ≡ just (mkResult x pos-x iter-rest)
      iter-eq = roundtrip f pos x iter-rest wf-x

      input-eq : emit (many f) (x ∷ xs) ++ₗ suffix
               ≡ emit f x ++ₗ iter-rest
      input-eq = ++ₗ-assoc (emit f x) (emit (many f) xs) suffix

      sleq : sameLengthᵇ (emit f x ++ₗ iter-rest) iter-rest ≡ false
      sleq = sameLengthᵇ-lt (emit f x ++ₗ iter-rest) iter-rest
               (subst (λ k → length iter-rest < k)
                      (sym (length-++ (emit f x) {iter-rest}))
                      (++ₗ-strictly-longer (emit f x) iter-rest ne-x))

      rec-eq : manyHelper (parse f) pos-x iter-rest m'
             ≡ just (mkResult xs
                       (advancePositions pos-x (emit (many f) xs)) suffix)
      rec-eq = manyHelper-roundtrip-list f pos-x xs suffix m' len-le wf-xs

      pos-out-eq : advancePositions pos-x (emit (many f) xs)
                 ≡ advancePositions pos (emit (many f) (x ∷ xs))
      pos-out-eq = sym (advancePositions-++ pos (emit f x) (emit (many f) xs))

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

-- L5: refined nat with arbitrary predicate `P : ℕ → Bool`.  Witness:
-- `(ss , wit)` where `ss : SuffixStops isDigit suffix` is the underlying
-- format's well-formedness, and `wit : T (P n)` is the refinement witness
-- supplied by the user.  Exercises the `refined` constructor's roundtrip
-- case end-to-end: parse runs nat, then `liftRefined` (decided via `T?`),
-- and the witness slot closes via `T-irrelevant`.  If `refined`'s
-- signature or `liftRefined-on-witness`'s shape drifts, this fails.
roundtrip-refined-nat : ∀ pos (P : ℕ → Bool) (n : ℕ) (wit : T (P n)) suffix
  → SuffixStops isDigit suffix
  → parse (refined P nat) pos (showNat-chars n ++ₗ suffix)
    ≡ just (mkResult (n , wit)
             (advancePositions pos (showNat-chars n))
             suffix)
roundtrip-refined-nat pos P n wit suffix ss =
  roundtrip (refined P nat) pos (n , wit) suffix ss
