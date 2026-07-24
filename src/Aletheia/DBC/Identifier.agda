-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC Identifier type — validated identifiers per the DBC grammar
-- (`identifier ::= (letter | "_") (letter | digit | "_")*`).
--
-- Shape: `name : List Char` plus an irrelevant witness that the char list
-- satisfies the grammar.  Storing as `List Char` (not `String`) lets the
-- lexer build `mkIdent (h ∷ t) <validity>` axiom-free from the chars it
-- just consumed.
--
-- Axiom budget:
--   * Lexer (`parseIdentifier`): axiom-free.  Builds directly from the
--     consumed `List Char`.
--   * JSON parser path (`mkIdentFromString`): axiom-free.  Stores `toList s`
--     as the name; the validity witness is the `T?` decision result.
--   * The two `String ↔ List Char` axioms in `Substrate.Unsafe` survive only
--     for the OUTER `parseText (formatText d) ≡ inj₂ d` wrap, not for any
--     Identifier construction site.
module Aletheia.DBC.Identifier where

open import Data.Bool using (Bool; true; false; T; _∨_; _∧_)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isAlpha; _≈ᵇ_; toℕ)
open import Data.Char.Properties using (≈⇒≡)
open import Data.List using (List; []; _∷_; length)
import Data.List.Properties as ListProps
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Aletheia.Data.Dec0 using (Dec₀; fromBridges)
open import Data.String as String using (String; fromList; toList)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Limits using (max-identifier-length)
open import Aletheia.Parser.CharClass using (isAlphaNum)

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

-- Extended with a length bound against
-- `max-identifier-length` (128) so every constructed `Identifier`
-- provably satisfies AGENTS.md "Adversarial-input bounds at parser
-- surfaces".  The bound check is the third conjunct; existing
-- `mkIdentFromChars` / `mkIdentFromString` callers go through
-- `T? (validIdentifierᵇ cs)` so they pick up the bound automatically.
-- Hard-coded `mkIdent (toList "<short>") tt` callsites still typecheck
-- because the conjunct reduces to `true` on every concrete string
-- shorter than 128 chars (closed-term reduction).
validIdentifierᵇ : List Char → Bool
validIdentifierᵇ []       = false
validIdentifierᵇ (c ∷ cs) =
  isIdentStart c ∧ allᵇ isIdentCont cs ∧ (length (c ∷ cs) <ᵇ suc max-identifier-length)

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
-- Construction from a `List Char` — the single identifier-parse interface
-- ============================================================================

-- The reason an identifier char list fails the DBC grammar.  Carried out of
-- the ONE validity decision (`parseIdentifierField`) so a caller that needs a
-- typed rejection (the LTL-property JSON parser) gets the reason
-- from the parse itself, with no second validity walk to keep in sync:
--   * `TooLong  n`  — `n` chars, over `max-identifier-length` (the length
--                     conjunct of `validIdentifierᵇ` failed).  Surfaced as
--                     `InputBoundExceeded IdentifierLength` (preserves D-32.1).
--   * `BadChars cs` — within the length bound but not the
--                     `(letter|_)(letter|digit|_)*` grammar (incl. empty).
--                     Surfaced as `ParseErr (InvalidIdentifier …)`.
data IdentifierError : Set where
  TooLong  : ℕ → IdentifierError
  BadChars : List Char → IdentifierError

-- THE identifier-parse interface: decide `validIdentifierᵇ` once, returning the
-- validated `Identifier` or the typed reason.  Used by `Lexer.parseIdentifier`
-- (via the `mkIdentFromChars` erasure below) and the LTL-property JSON parser
-- (directly, for the typed error).  Axiom-free; the witness type matches the
-- `Identifier.valid` field exactly.  `T? (validIdentifierᵇ cs)` is decided
-- FIRST so the erasure keeps its original reduction shape — the length split
-- only refines the (already-rejected) failure branch into TooLong vs BadChars.
parseIdentifierField : List Char → IdentifierError ⊎ Identifier
parseIdentifierField cs with T? (validIdentifierᵇ cs)
... | yes w = inj₂ (mkIdent cs w)
... | no  _ with length cs <ᵇ suc max-identifier-length
...   | false = inj₁ (TooLong (length cs))
...   | true  = inj₁ (BadChars cs)

-- `Maybe` erasure of the typed parse — the historical interface, now DERIVED
-- from the single `parseIdentifierField` decision (one interface, one path).
-- `Lexer.parseIdentifier` and `mkIdentFromString` consume this.
toMaybeIdent : IdentifierError ⊎ Identifier → Maybe Identifier
toMaybeIdent = [ (λ _ → nothing) , just ]′

mkIdentFromChars : List Char → Maybe Identifier
mkIdentFromChars cs = toMaybeIdent (parseIdentifierField cs)

-- Build an Identifier from a String.  Used by JSON ingestion (where every
-- field arrives as a String).  The Identifier's name is stored as `toList s`,
-- so the witness type `T (validIdentifierᵇ (toList s))` is exactly what the
-- `T?` decision returns.  Axiom-free.
mkIdentFromString : String → Maybe Identifier
mkIdentFromString = mkIdentFromChars ∘ toList

-- Constructing an Identifier from its own `name` round-trips — primitive form
-- on `parseIdentifierField` (the `yes` branch closes via `T-irrelevant` on the
-- witness; `no` is absurd against the stored `valid`), with the `Maybe` form as
-- its image under the `toMaybeIdent` erasure.  Axiom-free.  Single home for
-- this fact (cat 27 dedup): `parseIdentifierField-on-valid` feeds the LTL-JSON
-- predicate roundtrip (`LTL.JSON.Properties`);
-- `mkIdentFromChars-on-valid` the DBC text-parser roundtrip
-- (`TextParser.Properties.Primitives`).
parseIdentifierField-on-valid : ∀ (i : Identifier)
  → parseIdentifierField (Identifier.name i) ≡ inj₂ i
parseIdentifierField-on-valid (mkIdent name valid)
  with T? (validIdentifierᵇ name)
... | yes w  = cong (λ v → inj₂ (mkIdent name v)) (T-irrelevant w valid)
... | no  ¬w = ⊥-elim (¬w valid)

mkIdentFromChars-on-valid : ∀ (i : Identifier)
  → mkIdentFromChars (Identifier.name i) ≡ just i
mkIdentFromChars-on-valid i = cong toMaybeIdent (parseIdentifierField-on-valid i)

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
-- Bool-valued List Char equality (hot-path Dec-allocation escape)
-- ============================================================================
--
-- Used as a Bool fast path in cache lookup
-- (`LTL.SignalPredicate.Cache.{lookupEntries,updateEntries}`) and signal
-- lookup (`CAN.DBCHelpers.findSignalInList`) where the per-call Dec heap cell
-- allocated by `≡-dec _≟ᶜ_` shows up as Signal-Extraction throughput cost.
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

-- Self-certifying twin: packages `_≡csᵇ_` with an ERASED certificate built
-- from the lemma family below, so a Dec₀-shaped consumer gets the Bool and
-- its meaning as one value (MAlonzo erases the certificate — Dec₀ is a
-- newtype over Bool).  The standalone lemmas REMAIN the proof surface: the
-- cache-correctness and adequacy proofs consume them RELEVANTLY, which an
-- erased certificate cannot serve — the two are complementary, not
-- redundant.
_≟cs₀_ : (cs ds : List Char) → Dec₀ (cs ≡ ds)
cs ≟cs₀ ds = fromBridges (cs ≡csᵇ ds) (≡csᵇ-sound cs ds) (≡csᵇ-complete cs ds)

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
