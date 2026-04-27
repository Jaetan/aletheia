{-# OPTIONS --safe --without-K #-}

-- DBC Identifier type — validated identifiers per the DBC grammar
-- (`identifier ::= (letter | "_") (letter | digit | "_")*`).
--
-- Shape (Phase B.3.d Layer 3 commit 3d.4 — de-tainted from String, 2026-04-26):
-- `name : List Char` field plus an irrelevant witness that the char list
-- satisfies the grammar.  Pre-3d.4 used `name : String` with the witness
-- buried under `toList`; that forced `Lexer.parseIdentifier` to go through
-- `Substrate.Unsafe.mkIdentFromCharsUnsafe` (and thus through the
-- `toList∘fromList` axiom) just to build an Identifier from a `List Char`.
-- After 3d.4 the parser builds `mkIdent (h ∷ t) <validity>` directly and the
-- 47 modules under `DBC/TextParser/` regain `--safe`.
--
-- Axiom budget:
--   * Lexer (`parseIdentifier`): axiom-free.  Builds `mkIdent (h ∷ t) w`
--     directly from the consumed `List Char`.
--   * JSON parser path (`mkIdentFromString`): axiom-free.  Stores `toList s`
--     as the name; the `T (validIdentifierᵇ (toList s))` witness is the
--     `T?` decision result.
--   * The two `String ↔ List Char` axioms in `Substrate.Unsafe` survive only
--     for the OUTER `parseText (formatText d) ≡ inj₂ d` wrap, not for any
--     Identifier construction site.
module Aletheia.DBC.Identifier where

open import Data.Bool using (Bool; true; false; T; _∨_; _∧_; not)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isAlpha; _≈ᵇ_; toℕ)
open import Data.Char.Properties using (≈⇒≡)
open import Data.List using (List; []; _∷_)
import Data.List.Properties as ListProps
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; fromList; toList)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (isAlphaNum)

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
-- Identifier — `List Char`-internal record with char-list-level witness
-- ============================================================================

-- Runtime representation: MAlonzo compiles `Identifier` as a two-field data
-- constructor — `data Identifier = MkIdent (List Char) AgdaAny` — because
-- `valid : T (validIdentifierᵇ name)` stays relevant under `--safe`.
-- Conversion to `String` for JSON serialization / accessor calls happens in
-- `Aletheia.DBC.Types` via `fromList ∘ Identifier.name`; per-call cost is
-- O(name-length) and identifier names are <30 chars, so the overhead is
-- bounded and not on the per-frame signal-extraction hot path.
record Identifier : Set where
  constructor mkIdent
  field
    name  : List Char
    valid : T (validIdentifierᵇ name)

-- ============================================================================
-- Construction from a concrete String (JSON parser path — axiom-free)
-- ============================================================================

-- Build an Identifier from a `List Char` by checking the bool predicate
-- directly.  Used by `Lexer.parseIdentifier` to construct an Identifier from
-- the chars consumed by `satisfy isIdentStart >>= many (satisfy isIdentCont)`.
-- Axiom-free; the witness type matches the Identifier's `valid` field type
-- exactly, no `toList∘fromList` bridge is needed.
mkIdentFromChars : List Char → Maybe Identifier
mkIdentFromChars cs with T? (validIdentifierᵇ cs)
... | yes w = just (mkIdent cs w)
... | no  _ = nothing

-- Build an Identifier from a String.  Used by JSON ingestion (where every
-- field arrives as a String).  The Identifier's name is stored as `toList s`,
-- so the witness type `T (validIdentifierᵇ (toList s))` is exactly what the
-- `T?` decision returns.  Axiom-free.
mkIdentFromString : String → Maybe Identifier
mkIdentFromString = mkIdentFromChars ∘ toList

-- ============================================================================
-- String view (`fromList ∘ Identifier.name`)
-- ============================================================================

-- Convenience accessor: Identifier as a String.  Use this anywhere a String
-- is needed (JSON serialization, validation messages, error formatting); use
-- the raw `Identifier.name` field in places that already work on the
-- underlying `List Char` (formatters, parser-side proofs).  Per-call cost is
-- O(name-length); not on the per-frame signal-extraction hot path.
nameStr : Identifier → String
nameStr = fromList ∘ Identifier.name

-- ============================================================================
-- Decidable equality
-- ============================================================================

-- Two Identifiers are propositionally equal iff their `name` char lists are
-- equal.  Decidable List Char equality lifts decidable Char equality via
-- stdlib `Data.List.Properties.≡-dec`; `T-irrelevant` then closes the witness
-- field.
_≟ᴵ_ : (i j : Identifier) → Dec (i ≡ j)
mkIdent cs₁ v₁ ≟ᴵ mkIdent cs₂ v₂ with ListProps.≡-dec _≟ᶜ_ cs₁ cs₂
... | yes refl = yes (cong (mkIdent cs₁) (T-irrelevant v₁ v₂))
... | no  ¬eq  = no λ { refl → ¬eq refl }

-- ============================================================================
-- Bool-valued List Char equality (Path-A.5 hot-path Dec-allocation escape)
-- ============================================================================
--
-- Used as a Bool fast path in cache lookup
-- (`LTL.SignalPredicate.Cache.{lookupEntries,updateEntries}`) and signal
-- lookup (`CAN.DBCHelpers.findSignalInList`) where the per-call Dec heap cell
-- allocated by `≡-dec _≟ᶜ_` shows up as Signal-Extraction throughput cost
-- after the Path-A retype (see `feedback_hot_path_refactor_benchmark.md`).
--
-- Soundness/completeness chain stays `--safe`:
--   * `_≈ᵇ_` reduces to `toℕ c ≡ᵇ toℕ d` (a Bool primitive on ℕ);
--   * `≡ᵇ⇒≡` / `≡⇒≡ᵇ` from `Data.Nat.Properties` bridge `T (·≡ᵇ·)` ⇔ `≡`;
--   * `≈⇒≡` from `Data.Char.Properties` bridges Char `≈` ⇔ `≡`.
-- No `primStringEquality` axiom or COMPILE pragma needed; allowlist unchanged.

infix 4 _≡csᵇ_
_≡csᵇ_ : List Char → List Char → Bool
[]       ≡csᵇ []       = true
[]       ≡csᵇ (_ ∷ _)  = false
(_ ∷ _)  ≡csᵇ []       = false
(c ∷ cs) ≡csᵇ (d ∷ ds) = (c ≈ᵇ d) ∧ (cs ≡csᵇ ds)

-- Char-level soundness via the `_≈ᵇ_` chain.
private
  ≡cᵇ-sound : ∀ c d → T (c ≈ᵇ d) → c ≡ d
  ≡cᵇ-sound c d cd = ≈⇒≡ (≡ᵇ⇒≡ (toℕ c) (toℕ d) cd)

  -- Split T (x ∧ y) → T x × T y without going through the `Bool.Properties.T-∧`
  -- equivalence record; structural pattern match on the implicit Bools is
  -- cheaper to elaborate.
  T-∧→ : ∀ {x y : Bool} → T (x ∧ y) → T x × T y
  T-∧→ {true}  {true}  _ = tt , tt

  T-∧← : ∀ {x y : Bool} → T x → T y → T (x ∧ y)
  T-∧← {true}  {true}  _ _ = tt

  -- Char-level completeness: c ≡ d ⇒ T (c ≈ᵇ d).  Definitional after rewriting
  -- `c ≡ d` to `refl`: reduces `c ≈ᵇ c` to `T (toℕ c ≡ᵇ toℕ c)`.
  ≡cᵇ-complete : ∀ c → T (c ≈ᵇ c)
  ≡cᵇ-complete c = ≡⇒≡ᵇ (toℕ c) (toℕ c) refl

≡csᵇ-sound : ∀ cs ds → T (cs ≡csᵇ ds) → cs ≡ ds
≡csᵇ-sound []       []       _ = refl
≡csᵇ-sound (c ∷ cs) (d ∷ ds) p
  with T-∧→ {c ≈ᵇ d} {cs ≡csᵇ ds} p
... | (cd , csds) =
  cong₂ _∷_ (≡cᵇ-sound c d cd) (≡csᵇ-sound cs ds csds)

-- Reflexivity: every list is `≡csᵇ` itself.  Useful for proofs that need
-- to discharge the `T (cs ≡csᵇ cs)` obligation in the `cs ≡ cs` case.
≡csᵇ-refl : ∀ cs → T (cs ≡csᵇ cs)
≡csᵇ-refl []       = tt
≡csᵇ-refl (c ∷ cs) = T-∧← {c ≈ᵇ c} {cs ≡csᵇ cs} (≡cᵇ-complete c) (≡csᵇ-refl cs)

-- Completeness: cs ≡ ds ⇒ T (cs ≡csᵇ ds).  Falls out of reflexivity once
-- the equation is rewritten.
≡csᵇ-complete : ∀ cs ds → cs ≡ ds → T (cs ≡csᵇ ds)
≡csᵇ-complete cs .cs refl = ≡csᵇ-refl cs

-- Anti-soundness: when `_≡csᵇ_` says `false`, the propositional equality
-- is impossible.  Used in cache-lookup proofs that case-split on the Bool
-- and need to discharge the `cs ≢ ds` obligation in the negative branch.
≡csᵇ-false→≢ : ∀ cs ds → (cs ≡csᵇ ds) ≡ false → cs ≢ ds
≡csᵇ-false→≢ cs ds eq cs≡ds rewrite cs≡ds with ds ≡csᵇ ds | ≡csᵇ-refl ds
... | true | _ = case eq of λ ()
  where open import Function using (case_of_)

private
  -- Char-level reflexivity equation, used to collapse `c ≈ᵇ c` to `true` in
  -- the `≡csᵇ-refl-eq` recursion.  Uses `T-≡` to convert the `T` form returned
  -- by `≡⇒≡ᵇ` into a propositional `≡ true` equation.
  ≈ᵇ-refl-eq : ∀ c → (c ≈ᵇ c) ≡ true
  ≈ᵇ-refl-eq c = Equivalence.to T-≡ (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)
    where
      open import Data.Bool.Properties using (T-≡)
      open import Function.Bundles using (Equivalence)

-- Reflexive Bool equation: `(cs ≡csᵇ cs) ≡ true`.  Useful for `rewrite`-based
-- collapsing of `if cs ≡csᵇ cs then X else Y` to `X` in proofs.
≡csᵇ-refl-eq : ∀ cs → (cs ≡csᵇ cs) ≡ true
≡csᵇ-refl-eq []       = refl
≡csᵇ-refl-eq (c ∷ cs) rewrite ≈ᵇ-refl-eq c | ≡csᵇ-refl-eq cs = refl
