{-# OPTIONS --without-K #-}

-- Per-primitive roundtrip lemmas for the DBC text-format parser
-- (B.3.d Layer 2).
--
-- This commit (2b) lands ONLY the Identifier primitive + required
-- machinery.  Byte-order digit, sign flag, mux marker, string lit, attr
-- scope/type/value, signal-presence — deferred to commit 2c.
--
-- Scope rationale: `parseIdentifier`-roundtrip is the structurally
-- novel one (bridges through the `toList∘fromList` axiom in
-- `Substrate.Unsafe`) and the most widely consumed by Layer 3 (SG_,
-- BO_, CM_, SIG_GROUP_, EV_, BU_, attribute targets — ~7 call sites).
-- Doing it first establishes the proof template; the mechanical
-- primitives cascade from there.
module Aletheia.DBC.TextParser.Properties.Primitives where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   pure; fail; _>>=_; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont;
   validIdentifierᵇ; allᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; buildIdent; fromMaybeIdent)
open import Aletheia.DBC.TextParser.Properties.Substrate.Unsafe using
  (toList∘fromList; fromList∘toList; mkIdentFromCharsUnsafe)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many)
open import Aletheia.Prelude using (ifᵀ-witness; T→true)

-- ============================================================================
-- Probe 1 — decompose-valid
-- ============================================================================
--
-- `T (validIdentifierᵇ cs)` destructures into: `cs = h ∷ t`, the head
-- satisfies `isIdentStart`, and the tail is pointwise `isIdentCont`.
-- Empty list rejected by `validIdentifierᵇ [] = false → T false = ⊥`.

-- Helper: T (a ∧ b) → T a × T b  (stdlib has this but requires specific import)
private
  T-∧-split : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
  T-∧-split {true}  {true}  _ = tt , tt
  T-∧-split {true}  {false} ()
  T-∧-split {false} {_}     ()

-- Helper: T (allᵇ p xs) → All (T ∘ p) xs
private
  T-allᵇ→All : ∀ (p : Char → Bool) (xs : List Char)
             → T (allᵇ p xs) → All (T ∘ p) xs
  T-allᵇ→All p []       _  = []
  T-allᵇ→All p (c ∷ cs) ab =
    let (pc , pcs) = T-∧-split {p c} {allᵇ p cs} ab
    in pc ∷ T-allᵇ→All p cs pcs

decompose-valid : ∀ (cs : List Char) → T (validIdentifierᵇ cs)
  → ∃[ h ] ∃[ t ]
    (cs ≡ h ∷ t) × T (isIdentStart h) × All (T ∘ isIdentCont) t
decompose-valid []       ()
decompose-valid (h ∷ t) valid =
  let (ph , pt) = T-∧-split {isIdentStart h} {allᵇ isIdentCont t} valid
  in h , t , refl , ph , T-allᵇ→All isIdentCont t pt

-- ============================================================================
-- Probe 2 — mkIdentFromCharsUnsafe on a valid Identifier's char list
-- ============================================================================
--
-- Given `i : Identifier`, running the text parser's constructor on
-- `toList (Identifier.name i)` returns `just i` propositionally.  Passes
-- through the `fromList∘toList` axiom (to rewrite
-- `fromList (toList name) ≡ name`) and T-irrelevant (to equate the
-- constructed witness with the original `Identifier.valid`).

-- Helper: two Identifiers with propositionally equal `name` fields are
-- propositionally equal; `T-irrelevant` closes the field-mismatch on the
-- `valid` witness (T b is proof-irrelevant at any b).
private
  mkIdent-≡-by-name : ∀ {s₁ s₂ : String}
                      (v₁ : T (validIdentifierᵇ (toList s₁)))
                      (v₂ : T (validIdentifierᵇ (toList s₂)))
                    → s₁ ≡ s₂
                    → mkIdent s₁ v₁ ≡ mkIdent s₂ v₂
  mkIdent-≡-by-name {s₁ = s} v₁ v₂ refl = cong (mkIdent s) (T-irrelevant v₁ v₂)

-- mkIdentFromCharsUnsafe unfolded: on chars whose validIdentifierᵇ is
-- known to be true (via `Identifier.valid`), returns
-- `just (mkIdent (fromList chars) witness)`.  Closes via
-- `ifᵀ-witness` (fires the `true` branch given `valid : T …`) plus
-- `fromList∘toList` (for the name field) and `T-irrelevant` (for the
-- witness field, inside `mkIdent-≡-by-name`).
--
-- Uses `ifᵀ` instead of `with validIdentifierᵇ cs in eq` so that the
-- scrutinee never gets abstracted inside `valid`'s dependent type
-- (which would trigger an ill-typed with-abstraction —
-- `validIdentifierᵇ (toList name) != w` — because
-- `mkIdent name valid` demands `T (validIdentifierᵇ (toList name))` on
-- the RHS).  See `feedback_ifT_witness_pattern.md`.
mkIdentFromCharsUnsafe-on-valid : ∀ (i : Identifier)
  → mkIdentFromCharsUnsafe (toList (Identifier.name i)) ≡ just i
mkIdentFromCharsUnsafe-on-valid (mkIdent name valid) =
  trans (ifᵀ-witness _ nothing valid)
        (cong just (mkIdent-≡-by-name _ valid (fromList∘toList name)))

-- ============================================================================
-- Probe 3 — position alignment (decomposition consistency)
-- ============================================================================
--
-- `toList (Identifier.name i)` IS `h ∷ t` where (h, t) come from
-- `decompose-valid` applied to `Identifier.valid i`.  Follows by refl
-- from the decomposition's first output equation.

decompose-valid-matches-name : ∀ (i : Identifier)
  → let cs = toList (Identifier.name i)
        d  = decompose-valid cs (Identifier.valid i)
        h  = Data.Product.proj₁ d
        t  = Data.Product.proj₁ (Data.Product.proj₂ d)
    in cs ≡ h ∷ t
decompose-valid-matches-name i
  with decompose-valid (toList (Identifier.name i)) (Identifier.valid i)
... | _ , _ , eq , _ , _ = eq

-- ============================================================================
-- Probe 4 — satisfy-success-T
-- ============================================================================
--
-- `satisfy P` succeeds and consumes one char given a `T (P h)` witness.
-- Mirrors the pattern used by `some-satisfy-prefix` in
-- `DecRatParse.Properties` — `rewrite T→true ph` unblocks the internal
-- `with P h` in `satisfy`'s body, at which point `refl` closes the goal.

satisfy-success-T : ∀ (P : Char → Bool) (pos : Position) (h : Char) (cs : List Char)
  → T (P h)
  → satisfy P pos (h ∷ cs) ≡ just (mkResult h (advancePosition pos h) cs)
satisfy-success-T P pos h cs ph rewrite T→true ph = refl

-- ============================================================================
-- Probe 5 — buildIdent-eq
-- ============================================================================
--
-- `buildIdent h t ≡ pure i` follows by `cong fromMaybeIdent` from the
-- `mkIdentFromCharsUnsafe (h ∷ t) ≡ just i` equation (given by
-- `mkIdentFromCharsUnsafe-on-valid` composed with `sym cs-eq` from
-- `decompose-valid`).  The Lexer refactor (split into
-- `buildIdent h t = fromMaybeIdent (mkIdentFromCharsUnsafe (h ∷ t))`)
-- is the reason this closes as a one-liner — a top-level `with` in
-- `buildIdent` would have hidden the Maybe from external rewriting.

buildIdent-eq : ∀ (h : Char) (t : List Char) (i : Identifier)
  → mkIdentFromCharsUnsafe (h ∷ t) ≡ just i
  → buildIdent h t ≡ pure i
buildIdent-eq _ _ _ eq = cong fromMaybeIdent eq

-- ============================================================================
-- parseIdentifier-roundtrip — composed theorem
-- ============================================================================
--
-- The main layer-2 Identifier lemma: parsing any valid Identifier's char
-- list concatenated with a stopping suffix returns that Identifier plus
-- the untouched suffix.  Structure mirrors
-- `DecRatParse/Properties.parseDecRat-roundtrip-+suc` — two
-- `bind-just-step`s + one final `buildIdent-eq`-applied step, chained
-- via `trans`.  `subst` on `sym cs-eq` lifts the concrete-shape proof
-- (`h ∷ t` form) back to the abstract `toList (Identifier.name i)` form
-- the public theorem advertises.

-- Lift `All (T ∘ P) xs` to `All (λ c → P c ≡ true) xs` — the form
-- `manyHelper-satisfy-exhaust-many` demands.  Trivial pointwise `T→true`.
private
  T-All→≡true : ∀ {P : Char → Bool} {xs : List Char}
             → All (T ∘ P) xs
             → All (λ c → P c ≡ true) xs
  T-All→≡true []         = []
  T-All→≡true (px ∷ pxs) = T→true px ∷ T-All→≡true pxs

parseIdentifier-roundtrip : ∀ (pos : Position) (i : Identifier)
                              (suffix : List Char)
                            → SuffixStops isIdentCont suffix
                            → parseIdentifier pos
                                (toList (Identifier.name i) ++ₗ suffix)
                              ≡ just (mkResult i
                                       (advancePositions pos
                                          (toList (Identifier.name i)))
                                       suffix)
parseIdentifier-roundtrip pos i suffix ss
  with decompose-valid (toList (Identifier.name i)) (Identifier.valid i)
... | h , t , cs-eq , start , conts =
      subst (λ cs → parseIdentifier pos (cs ++ₗ suffix)
                      ≡ just (mkResult i (advancePositions pos cs) suffix))
            (sym cs-eq)
            concrete-proof
  where
    pos' : Position
    pos' = advancePosition pos h

    pos'' : Position
    pos'' = advancePositions pos' t

    -- satisfy isIdentStart consumes h, advancing to pos' with tail t++suffix.
    step-satisfy :
      parseIdentifier pos ((h ∷ t) ++ₗ suffix)
      ≡ (many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
          pos' (t ++ₗ suffix)
    step-satisfy =
      bind-just-step (satisfy isIdentStart)
                     (λ h' → many (satisfy isIdentCont) >>=
                             λ t' → buildIdent h' t')
                     pos ((h ∷ t) ++ₗ suffix)
                     h pos' (t ++ₗ suffix)
                     (satisfy-success-T isIdentStart pos h (t ++ₗ suffix) start)

    -- many (satisfy isIdentCont) consumes t, advancing to pos'' with suffix.
    step-many :
      (many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
        pos' (t ++ₗ suffix)
      ≡ buildIdent h t pos'' suffix
    step-many =
      bind-just-step (many (satisfy isIdentCont))
                     (λ t' → buildIdent h t')
                     pos' (t ++ₗ suffix)
                     t pos'' suffix
                     (manyHelper-satisfy-exhaust-many isIdentCont pos' t suffix
                        (T-All→≡true conts) ss)

    -- buildIdent h t reduces via fromMaybeIdent (mkIdentFromCharsUnsafe (h ∷ t))
    -- = fromMaybeIdent (just i) = pure i, once we bridge through cs-eq and
    -- mkIdentFromCharsUnsafe-on-valid.
    mki-eq : mkIdentFromCharsUnsafe (h ∷ t) ≡ just i
    mki-eq = trans (cong mkIdentFromCharsUnsafe (sym cs-eq))
                   (mkIdentFromCharsUnsafe-on-valid i)

    step-build :
      buildIdent h t pos'' suffix
      ≡ just (mkResult i pos'' suffix)
    step-build = cong (λ p → p pos'' suffix) (buildIdent-eq h t i mki-eq)

    concrete-proof :
      parseIdentifier pos ((h ∷ t) ++ₗ suffix)
      ≡ just (mkResult i (advancePositions pos (h ∷ t)) suffix)
    concrete-proof = trans step-satisfy (trans step-many step-build)
