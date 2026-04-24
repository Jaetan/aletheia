{-# OPTIONS --safe --without-K #-}

-- DBC Identifier type — validated identifiers per the DBC grammar
-- (`identifier ::= (letter | "_") (letter | digit | "_")*`).
--
-- Shape chosen (Phase B.3.d Layer 2, T3-fixed after user decision 2026-04-24):
-- single `name : String` field plus an irrelevant witness that the name's char
-- list satisfies the grammar.  The witness lives at `toList name` — concrete
-- when the String is concrete, abstract when the String is abstract.  All
-- `List Char`-level machinery stays at the proof / erasure layer.
--
-- Runtime representation: MAlonzo compiles `Identifier` as a Haskell newtype
-- over `String` (the `.valid` field is irrelevant, erased at compile time).
-- Zero perf regression vs. a bare `String` field — confirmed in the prior
-- option-(iii) round via GHC Core (d_name: just a cast; inlined on hot path).
--
-- Axiom budget:
--   * JSON parser path (`mkIdentFromString`): uses no axioms.  Concrete input
--     String s; `validIdentifierᵇ (toList s)` reduces when s is a term with
--     reducible toList; the bool witness is baked in via `subst T (sym eq) tt`.
--   * Roundtrip proofs (JSON metadata): use no axioms.  Two Identifiers with
--     matching `name` fields are `_≡_`-equal by record-η over the irrelevant
--     `.valid` field.
--   * Text parser path: the parser produces `fromList (h ∷ t)` as the String.
--     Building the witness `T (validIdentifierᵇ (toList (fromList (h ∷ t))))`
--     requires the `toList∘fromList` axiom from `Substrate.Unsafe` to bridge
--     from the char-level bool.  This is the SOLE axiom use in the layer-2
--     Identifier story, and it is confined to the Unsafe helper
--     `mkIdentFromCharsUnsafe` (co-located with the axioms).
module Aletheia.DBC.Identifier where

open import Data.Bool using (Bool; true; false; T; _∨_; _∧_)
open import Data.Bool.Properties using (T?)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isAlpha)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String as String using (String; fromList; toList)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (isAlphaNum)
open import Data.Bool.Properties using (T-irrelevant)

-- ============================================================================
-- CHARACTER CLASSES (hosted here so Identifier can reference them without a
-- cyclic dep on TextParser.Lexer; Lexer re-imports these)
-- ============================================================================

isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ ⌊ c ≟ᶜ '_' ⌋

isIdentCont : Char → Bool
isIdentCont c = isAlphaNum c ∨ ⌊ c ≟ᶜ '_' ⌋

-- ============================================================================
-- IDENTIFIER VALIDITY — Bool predicate at List Char level
-- ============================================================================

-- Bool-valued identifier validity check on char lists.  Mirrors the text
-- parser's shape: `satisfy isIdentStart >>= many (satisfy isIdentCont)`.
-- Defined here (not in Lexer) so downstream callers can reason about validity
-- without a cyclic import.
allᵇ : (Char → Bool) → List Char → Bool
allᵇ _ []       = true
allᵇ p (c ∷ cs) = p c ∧ allᵇ p cs

validIdentifierᵇ : List Char → Bool
validIdentifierᵇ []       = false
validIdentifierᵇ (c ∷ cs) = isIdentStart c ∧ allᵇ isIdentCont cs

-- ============================================================================
-- Identifier — String-internal record with char-list-level witness
-- ============================================================================

-- Runtime representation: `data Identifier = MkIdent String AgdaAny` in
-- MAlonzo output — a two-field data constructor, not a newtype.  The T-value
-- field carries an `AgdaAny` at runtime (irreducible abstract bool → T type
-- is stuck on abstract names).  Benchmarks show ~5–10% regression on Signal
-- Extraction vs. bare-String baseline; the T-relevant storage is needed to
-- close `validateIdent-roundtrip` (via `T-irrelevant` + `T?` case-analysis)
-- and `_≟ᴵ_` (via `cong (mkIdent s)` with relevant fields).  Switching to
-- `@0 valid` would restore newtype compile but breaks `_≟ᴵ_` (erased fields
-- can't pass through stdlib's `cong`).  Documented as T3-fixed accepted cost.
record Identifier : Set where
  constructor mkIdent
  field
    name  : String
    valid : T (validIdentifierᵇ (toList name))

-- ============================================================================
-- Construction from a concrete String (JSON parser path — axiom-free)
-- ============================================================================

-- Build an Identifier from a String by checking the bool predicate on its
-- char list.  Axiom-free; uses `T?` so the roundtrip proof can extract the
-- witness via the `yes/no` case-split + `T-irrelevant`.
mkIdentFromString : String → Maybe Identifier
mkIdentFromString s with T? (validIdentifierᵇ (toList s))
... | yes w = just (mkIdent s w)
... | no  _ = nothing

-- ============================================================================
-- Decidable equality
-- ============================================================================

-- Two Identifiers are propositionally equal iff their `name` strings are
-- equal.  The `@0 valid` field is erased at compile time; since valid has
-- type `T b` (either `⊤` with unique inhabitant `tt`, or `⊥` with no
-- inhabitants), T-irrelevant gives us field equality.  Using `cong` on the
-- constructor with the erased field is accepted under `--erasure`.
_≟ᴵ_ : (i j : Identifier) → Dec (i ≡ j)
mkIdent s₁ v₁ ≟ᴵ mkIdent s₂ v₂ with s₁ ≟ₛ s₂
... | yes refl = yes (cong (mkIdent s₁) (T-irrelevant v₁ v₂))
... | no  ¬eq  = no λ { refl → ¬eq refl }
