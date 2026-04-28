{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — DSL-side `ValueTable-format` (production
-- migration).
--
-- Replaces the canonical-only 3d.5.b version with a production-permissive
-- form: every formatter slot the production parser treats as `parseWS`
-- (mandatory whitespace, one-or-more) becomes `withWS`; every slot the
-- production parser treats as `parseWSOpt` (zero-or-more) where the
-- formatter emits a single space becomes `withWSCanonOne`; the trailing
-- newline is `newlineFmt` (altSum `"\r\n"` / `"\n"`).
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `withWS`         — between `"VAL_TABLE_"` and the name (parseWS),
--                        and within each value entry (parseWS twice).
--   * `withWSCanonOne` — between the last entry and `;` (parseWSOpt; the
--                        formatter emits exactly one space there).
--   * `newlineFmt`     — line terminator; canonical emit `'\n'`, parser
--                        accepts `'\n'` and `'\r\n'`.
--
-- The trailing `many parseNewline` consumption (zero-or-more blank lines
-- after the line terminator) lives in the `Aletheia.DBC.TextParser
-- .ValueTables.parseValueTable` wrapper, NOT in this Format — same
-- pattern as η's `parseSignalLine` vs `parseMessage` (line consumes one
-- terminator, block-level composer absorbs blanks).
--
-- This file replaces 3d.5.b's canonical-only gate measurement.  Post-3d.5.d
-- the 88-strict-LOC canonical figure no longer applies; the equivalent
-- measurement is the combined `Format/ValueTable.agda` + thin proof in
-- `Properties/ValueTables/ValueTable.agda` strict-LOC vs the existing
-- 613 strict-code-LOC of the pre-DSL Properties proof.
module Aletheia.DBC.TextParser.Format.ValueTable where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition;
         advancePositions; parseCharsSeq; pure; _>>=_)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.Types using (ValueTable)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; bind-just-step; showNat-chars-head)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         altSum; ws; wsCanonOne; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany; ParseFailsAt;
         []-fails; ∷-cons;
         roundtrip)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirrors `Format.SignalLine`)
-- ============================================================================

-- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
private
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Canonical single space, parser zero-or-more.  Canonical emit `' ' ∷ []`.
  withWSCanonOne : ∀ {A} → Format A → Format A
  withWSCanonOne f =
    iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

-- ============================================================================
-- DSL DEFINITIONS
-- ============================================================================

-- One ` <nat> "<desc>"` entry — single space then nat, single space then
-- quoted string-literal description.  Production permissiveness preserved
-- via `withWS`.
ValueEntry-format : Format (ℕ × List Char)
ValueEntry-format = pair (withWS nat) (withWS stringLit)

-- Full `VAL_TABLE_ <name>(<entries>) ;\n` line.  Production-permissive:
-- post-`VAL_TABLE_` and intra-entry whitespaces are `withWS`; pre-`;`
-- whitespace is `withWSCanonOne` (formatter emits one space, parser
-- accepts zero-or-more); line terminator is `newlineFmt`.
ValueTable-format : Format ValueTable
ValueTable-format =
  iso fwd bwd
      (λ _ → refl)
      (withPrefix (toList "VAL_TABLE_") (
        pair (withWS ident) (
          pair (many ValueEntry-format) (
            withWSCanonOne (
              withPrefix (';' ∷ []) newlineFmt)))))
  where
    fwd : Identifier × (List (ℕ × List Char) × ⊤) → ValueTable
    fwd (name , entries , _) = record { name = name ; entries = entries }

    bwd : ValueTable → Identifier × (List (ℕ × List Char) × ⊤)
    bwd vt = ValueTable.name vt , ValueTable.entries vt , tt

-- ============================================================================
-- PER-TABLE PRECONDITION (mirrors η's `NameStop`)
-- ============================================================================

-- Each table's name decomposes as `c ∷ cs` with `isHSpace c ≡ false`,
-- so the `withWS ident` slot's `SuffixStops isHSpace (Identifier.name name
-- ++ rest)` obligation reduces to `∷-stop c-non-hspace`.  Layer 4 will
-- discharge this universally from `validIdentifierᵇ` via the
-- `isIdentStart→¬isHSpace` bridge (see
-- `project_b3d_layer4_owed_lemmas.md`).
ValueTableNameStop : ValueTable → Set
ValueTableNameStop vt =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (ValueTable.name vt) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- TERMINATION CERTIFICATE — `parse ValueEntry-format` rejects ` ;…`
-- ============================================================================

-- After all entries are parsed, the trailing input is `' ' ∷ ';' ∷ '\n' ∷ …`.
-- `parse ValueEntry-format` fires `parseWS` (consuming the leading space),
-- then `parseNatural` rejects `';'` (not a digit), and the bind chain
-- returns `nothing`.  `refl` works here because every step in the chain
-- (`some (satisfy isHSpace)`'s success-then-stop, the `>>=` plumbing,
-- `some (satisfy isDigit)`'s leading-`satisfy` failure on `';'`) reduces
-- definitionally to `nothing`.  Provides `ParseFailsAt ValueEntry-format
-- (' ' ∷ ';' ∷ '\n' ∷ outer)` for the empty-tail step of `EmitsOKMany`.
parseValueEntry-format-fails-on-semi : ∀ pos rest
  → parse ValueEntry-format pos (' ' ∷ ';' ∷ rest) ≡ nothing
parseValueEntry-format-fails-on-semi pos rest = refl

-- ============================================================================
-- PRIVATE HELPERS — char-class reductions on emitted heads
-- ============================================================================

private
  -- The head of `showNat-chars n ++ rest` is `digitChar k` for some
  -- `k < 10`; `isHSpace` reduces to `false` on every closed digit char.
  -- Mirrored from `Properties/ValueTables/ValueTable.agda` (pre-3d.5.d
  -- copy) — duplicated locally to keep this module self-contained; can
  -- be hoisted to a shared module in a future ws-aware migration sweep.
  digitChar-not-isHSpace : ∀ d → isHSpace
    (Aletheia.DBC.TextFormatter.Emitter.digitChar d) ≡ false
  digitChar-not-isHSpace 0 = refl
  digitChar-not-isHSpace 1 = refl
  digitChar-not-isHSpace 2 = refl
  digitChar-not-isHSpace 3 = refl
  digitChar-not-isHSpace 4 = refl
  digitChar-not-isHSpace 5 = refl
  digitChar-not-isHSpace 6 = refl
  digitChar-not-isHSpace 7 = refl
  digitChar-not-isHSpace 8 = refl
  digitChar-not-isHSpace 9 = refl
  digitChar-not-isHSpace
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

  showNat-head-non-hspace : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops isHSpace (showNat-chars n ++ₗ rest)
  showNat-head-non-hspace n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

  -- The head of `showNat-chars n ++ rest` is non-`'"'` (every digit ≠ '"').
  showNat-head-non-quote : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops (λ c → c ≈ᵇ '"') (showNat-chars n ++ₗ rest)
  showNat-head-non-quote n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops (λ c → c ≈ᵇ '"') (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digit-non-quote d))
    where
      digit-non-quote : ∀ d → (Aletheia.DBC.TextFormatter.Emitter.digitChar d
                                ≈ᵇ '"') ≡ false
      digit-non-quote 0 = refl
      digit-non-quote 1 = refl
      digit-non-quote 2 = refl
      digit-non-quote 3 = refl
      digit-non-quote 4 = refl
      digit-non-quote 5 = refl
      digit-non-quote 6 = refl
      digit-non-quote 7 = refl
      digit-non-quote 8 = refl
      digit-non-quote 9 = refl
      digit-non-quote
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

-- ============================================================================
-- WELL-FORMEDNESS — per-entry EmitsOK
-- ============================================================================

-- Build `EmitsOK ValueEntry-format (v , d) outer-rest`.  Reduces
-- structurally through `pair`, `withWS`/`iso`/`pair ws`:
--
--   EmitsOK ValueEntry-format (v , d) outer-rest
--   = EmitsOK (withWS nat) v (emit (withWS stringLit) d ++ outer-rest)
--     × EmitsOK (withWS stringLit) d outer-rest
--   = (SuffixStops isHSpace (showNat-chars v ++ ' ' ∷ quoteStringLit-chars d
--                                              ++ outer-rest)
--      × SuffixStops isDigit (' ' ∷ quoteStringLit-chars d ++ outer-rest))
--     × (SuffixStops isHSpace (quoteStringLit-chars d ++ outer-rest)
--        × SuffixStops (≈ᵇ '"') outer-rest)
--
-- All four boil down to head-of-residual checks; the caller supplies the
-- `outer-rest` head non-`"` witness.
build-EmitsOK-entry : ∀ (v : ℕ) (d : List Char) (outer-rest : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') outer-rest
  → EmitsOK ValueEntry-format (v , d) outer-rest
build-EmitsOK-entry v d outer-rest q-stop =
  ((showNat-head-non-hspace v
      (' ' ∷ quoteStringLit-chars d ++ₗ outer-rest)
   , ∷-stop refl)
  , (∷-stop refl
    , q-stop))

-- ============================================================================
-- WELL-FORMEDNESS — entries list (EmitsOKMany)
-- ============================================================================

-- Build `EmitsOKMany ValueEntry-format entries (' ' ∷ ';' ∷ '\n' ∷ outer)`.
-- Empty: `[]-fails` via `parseValueEntry-format-fails-on-semi`.
-- Cons (last): per-entry EmitsOK against trailing `' ' ∷ ';' ∷ …` (head
--   `' '`, non-`"`); recursive `[]` step.
-- Cons (non-last): per-entry EmitsOK against next entry's leading `' '`
--   (head non-`"`); recursive cons step.
build-EmitsOKMany : ∀ (entries : List (ℕ × List Char)) (outer-suffix : List Char)
  → EmitsOKMany ValueEntry-format entries
      (' ' ∷ ';' ∷ '\n' ∷ outer-suffix)
build-EmitsOKMany [] outer-suffix =
  []-fails (λ pos →
    parseValueEntry-format-fails-on-semi pos ('\n' ∷ outer-suffix))
build-EmitsOKMany ((v , d) ∷ []) outer-suffix =
  ∷-cons
    (build-EmitsOK-entry v d (' ' ∷ ';' ∷ '\n' ∷ outer-suffix)
                         (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany [] outer-suffix)
build-EmitsOKMany ((v , d) ∷ ((v' , d') ∷ rest')) outer-suffix =
  ∷-cons
    (build-EmitsOK-entry v d
       (emit (many ValueEntry-format) ((v' , d') ∷ rest')
        ++ₗ ' ' ∷ ';' ∷ '\n' ∷ outer-suffix)
       (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany ((v' , d') ∷ rest') outer-suffix)

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- Build `EmitsOK ValueTable-format vt outer-suffix` from a single domain
-- precondition: the table's name is `c ∷ cs` with `isHSpace c ≡ false`.
-- Reduces structurally through `iso → withPrefix → pair → withWS → many
-- → withWSCanonOne → withPrefix → newlineFmt`.  Every SuffixStops
-- obligation either chains to the user's `ValueTableNameStop` witness
-- or reduces to `∷-stop refl` on a known fixed head.
build-emits-ok : ∀ (vt : ValueTable) outer-suffix
  → ValueTableNameStop vt
  → EmitsOK ValueTable-format vt outer-suffix
build-emits-ok record { name = name ; entries = [] } outer-suffix
               (c , cs , name-eq , c-non-hs) =
  -- "VAL_TABLE_" literal: vacuous (tt).
  tt ,
  -- (withWS ident name): SuffixStops isHSpace on (name ++ rest), and
  -- SuffixStops isIdentCont on rest.  rest = emit-many [] ++ ' ' ∷ ';' ∷ '\n'
  --                                            ∷ outer = ' ' ∷ ';' ∷ '\n' ∷ outer.
  ((subst (λ xs → SuffixStops isHSpace
                    (xs ++ₗ ' ' ∷ ';' ∷ '\n' ∷ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs))
   , ∷-stop refl) ,
  -- (many ValueEntry-format []): EmitsOKMany on empty entries.
  build-EmitsOKMany [] outer-suffix ,
  -- (withWSCanonOne (withPrefix ";" newlineFmt)) tt outer-suffix:
  -- SuffixStops isHSpace (';' ∷ '\n' ∷ outer) × inner.
  -- Inner: literal ";" vacuous; newlineFmt (inj₂ tt outer): inner literal
  -- "\n" vacuous + parse "\r\n" disjointness on ('\n' ∷ outer).
  (∷-stop refl
   , (tt
     , (tt , (λ pos → refl))))
build-emits-ok record { name = name ; entries = (v , d) ∷ rest } outer-suffix
               (c , cs , name-eq , c-non-hs) =
  tt ,
  ((subst (λ xs → SuffixStops isHSpace
                    (xs ++ₗ
                     emit (pair (many ValueEntry-format)
                                (withWSCanonOne
                                  (withPrefix (';' ∷ []) newlineFmt)))
                          ((v , d) ∷ rest , tt)
                     ++ₗ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs))
   , ∷-stop refl) ,
  build-EmitsOKMany ((v , d) ∷ rest) outer-suffix ,
  (∷-stop refl
   , (tt
     , (tt , (λ pos → refl))))

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- THE GATE: parseValueTable expressed via Format DSL.  Body is one
-- `roundtrip` call + the EmitsOK construction.  Universal in `vt` and
-- `outer-suffix`; the only domain precondition is `ValueTableNameStop vt`
-- (the table's name first char is non-hspace), which Layer 4 discharges
-- universally.
parseValueTable-format-roundtrip : ∀ pos vt outer-suffix
  → ValueTableNameStop vt
  → parse ValueTable-format pos
      (emit ValueTable-format vt ++ₗ outer-suffix)
    ≡ just (mkResult vt
             (advancePositions pos (emit ValueTable-format vt))
             outer-suffix)
parseValueTable-format-roundtrip pos vt outer-suffix nameStop =
  roundtrip ValueTable-format pos vt outer-suffix
    (build-emits-ok vt outer-suffix nameStop)
