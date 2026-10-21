-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A DBC identifier: a C identifier in ASCII,
-- `[A-Za-z_][A-Za-z0-9_]*`, held as `name : List Char` with the erased
-- witness that the characters satisfy the grammar.  Its length and the DBC
-- keywords are decided where a DBC's bounds are (`Aletheia.DBC.Bounds`),
-- so the lexer and the JSON route build an `Identifier` from the characters
-- they read with no axiom.
module Aletheia.DBC.Identifier where

open import Data.Bool using (Bool; true; false; T; _∨_; _∧_; not)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit; _≈ᵇ_; toℕ)
open import Data.Char.Properties using (≈⇒≡)
open import Data.List using (List; []; _∷_; length)
import Data.List.Properties as ListProps
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (map)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _<ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Data.String as String using (String; fromList; toList)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Limits using (max-identifier-length)

-- ============================================================================
-- CHARACTER CLASSES (the lexer reads them from here)
-- ============================================================================

-- An ASCII letter, by code point: `A` to `Z` or `a` to `z`.
isAsciiLetter : Char → Bool
isAsciiLetter c = ((65 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 90)) ∨ ((97 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 122))

isIdentStart : Char → Bool
isIdentStart c = isAsciiLetter c ∨ ⌊ c ≟ᶜ '_' ⌋

isIdentCont : Char → Bool
isIdentCont c = isAsciiLetter c ∨ isDigit c ∨ ⌊ c ≟ᶜ '_' ⌋

-- ============================================================================
-- IDENTIFIER VALIDITY, a Bool over the characters
-- ============================================================================

allᵇ : (Char → Bool) → List Char → Bool
allᵇ _ []       = true
allᵇ p (c ∷ cs) = p c ∧ allᵇ p cs

-- The first character failing `p`, with its index counted from `i`.
firstFailing : (Char → Bool) → ℕ → List Char → Maybe (ℕ × Char)
firstFailing _ _ []       = nothing
firstFailing p i (c ∷ cs) = if p c then firstFailing p (suc i) cs else just (i , c)

-- An ASCII character, by code point.
asciiᵇ : Char → Bool
asciiᵇ c = toℕ c <ᵇ 128

infix 4 _≡csᵇ_
_≡csᵇ_ : List Char → List Char → Bool
[]       ≡csᵇ []       = true
[]       ≡csᵇ (_ ∷ _)  = false
(_ ∷ _)  ≡csᵇ []       = false
(c ∷ cs) ≡csᵇ (d ∷ ds) = (c ≈ᵇ d) ∧ (cs ≡csᵇ ds)

-- ============================================================================
-- KEYWORDS
-- ============================================================================

-- Every keyword the DBC grammar spells (the Vector specification of 2007,
-- its NS_ symbols included) and the five attribute type words.  A keyword is
-- refused as a name where a DBC's bounds are decided.
dbcKeywords : List (List Char)
dbcKeywords = map toList
  ( "VERSION" ∷ "NS_" ∷ "BS_" ∷ "BU_" ∷ "BO_" ∷ "SG_" ∷ "EV_" ∷ "CM_"
  ∷ "NS_DESC_" ∷ "BA_DEF_" ∷ "BA_" ∷ "VAL_" ∷ "CAT_DEF_" ∷ "CAT_" ∷ "FILTER"
  ∷ "BA_DEF_DEF_" ∷ "EV_DATA_" ∷ "ENVVAR_DATA_" ∷ "SGTYPE_" ∷ "SGTYPE_VAL_"
  ∷ "BA_DEF_SGTYPE_" ∷ "BA_SGTYPE_" ∷ "SIG_TYPE_REF_" ∷ "VAL_TABLE_"
  ∷ "SIG_GROUP_" ∷ "SIG_VALTYPE_" ∷ "SIGTYPE_VALTYPE_" ∷ "BO_TX_BU_"
  ∷ "BA_DEF_REL_" ∷ "BA_REL_" ∷ "BA_SGTYPE_REL_" ∷ "SG_MUL_VAL_"
  ∷ "BU_SG_REL_" ∷ "BU_BO_REL_" ∷ "BU_EV_REL_" ∷ "BA_DEF_DEF_REL_"
  ∷ "INT" ∷ "HEX" ∷ "FLOAT" ∷ "STRING" ∷ "ENUM" ∷ [] )

isKeywordᵇ : List Char → Bool
isKeywordᵇ cs = any (cs ≡csᵇ_) dbcKeywords

-- A word: the grammar alone, in the lexer's shape (`satisfy isIdentStart`
-- then `many (satisfy isIdentCont)`).  The `NS_` block's keyword lines are
-- words; a DBC identifier is more.
isWordᵇ : List Char → Bool
isWordᵇ []       = false
isWordᵇ (c ∷ cs) = isIdentStart c ∧ allᵇ isIdentCont cs

-- A DBC identifier: a word of at most `max-identifier-length` characters
-- that is not a DBC keyword.
validIdentifierᵇ : List Char → Bool
validIdentifierᵇ cs =
  isWordᵇ cs ∧ (length cs <ᵇ suc max-identifier-length) ∧ not (isKeywordᵇ cs)

-- The index of the first character outside the grammar: the head if it is
-- not a start character, else the first tail character that is not a
-- continuation character; `nothing` for a word.
grammarBreak : List Char → Maybe ℕ
grammarBreak []       = just 0
grammarBreak (c ∷ cs) = if isIdentStart c then index (firstFailing isIdentCont 1 cs) else just 0
  where
    index : Maybe (ℕ × Char) → Maybe ℕ
    index (just (i , _)) = just i
    index nothing        = nothing


-- ============================================================================
-- Identifier — `List Char`-internal record with char-list-level witness
-- ============================================================================

-- MAlonzo compiles `Identifier` as a two-field constructor, the witness
-- `valid : T (validIdentifierᵇ name)` staying relevant under `--safe`.  The
-- `String` view is `nameStr`, a walk of the name.
record Identifier : Set where
  constructor mkIdent
  field
    name  : List Char
    valid : T (validIdentifierᵇ name)

-- ============================================================================
-- Construction from a `List Char` — the single identifier-parse interface
-- ============================================================================

-- Why characters are not an identifier, as a reader meets them one by one:
-- a character outside the grammar before the bound (`BadChars`), the 129th
-- identifier character reached (`TooLong`, carrying the length), or a
-- finished word that is a DBC keyword (`Keyword`).
data IdentifierError : Set where
  TooLong  : ℕ → IdentifierError
  Keyword  : List Char → IdentifierError
  BadChars : List Char → IdentifierError

-- The one identifier decision: the validated `Identifier`, or the typed
-- reason.  `Lexer.parseIdentifier` takes it through `mkIdentFromChars`, the
-- LTL property parser directly.
parseIdentifierField : List Char → IdentifierError ⊎ Identifier
parseIdentifierField cs with T? (validIdentifierᵇ cs)
... | yes w = inj₂ (mkIdent cs w)
... | no  _ with grammarBreak cs
...   | just i  = if i <ᵇ max-identifier-length then inj₁ (BadChars cs) else inj₁ (TooLong (length cs))
...   | nothing = if length cs <ᵇ suc max-identifier-length then inj₁ (Keyword cs) else inj₁ (TooLong (length cs))

-- The decision as a `Maybe`, for the lexer.
toMaybeIdent : IdentifierError ⊎ Identifier → Maybe Identifier
toMaybeIdent = [ (λ _ → nothing) , just ]′

mkIdentFromChars : List Char → Maybe Identifier
mkIdentFromChars cs = toMaybeIdent (parseIdentifierField cs)

-- Deciding an Identifier's own `name` gives it back: the `yes` branch closes
-- through `T-irrelevant` on the witness, `no` is absurd against the stored
-- `valid`.  The DBC text-parser round trip (`TextParser.Properties.Primitives`)
-- consumes it, and the LTL-JSON predicate round trip through
-- `JSONParser.validateIdent-on-valid`.
parseIdentifierField-on-valid : ∀ (i : Identifier)
  → parseIdentifierField (Identifier.name i) ≡ inj₂ i
parseIdentifierField-on-valid (mkIdent name valid)
  with T? (validIdentifierᵇ name)
... | yes w  = cong (λ v → inj₂ (mkIdent name v)) (T-irrelevant w valid)
... | no  ¬w = ⊥-elim (¬w valid)

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


