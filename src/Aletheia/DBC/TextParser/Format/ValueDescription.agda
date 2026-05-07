{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 / Track E.5β — DSL-side `ValueDescription-format`.
--
-- Production-permissive Format DSL Format for VAL_ lines:
--   "VAL_" ws nat ws identifier (ws nat ws string-lit)* ws? ";" newline
--
-- Mirrors `Format.ValueTable.ValueTable-format` with two differences:
--   * Prefix is "VAL_" (4 chars) instead of "VAL_TABLE_" (10 chars).
--   * After the prefix, we have `withWS nat` (raw CAN ID) BEFORE the
--     `withWS ident` (signal name) slot.  ValueTable has just `withWS
--     ident` (table name) at that position.
--
-- The carrier is `ℕ × Identifier × List (ℕ × List Char)` — the RAW shape
-- before `buildCANId` decoding.  The `RawValueDesc` record (defined in
-- `TextParser.ValueTables`) carries a decoded `CANId`, but the DSL layer
-- speaks `ℕ` because `buildCANId` is partial (out-of-range `nat` rejects
-- the whole file).  The slim `parseValueDescription-roundtrip` in
-- `Properties/ValueTables/ValueDesc.agda` layers `buildCANId-rawCanIdℕ`
-- on top of this DSL universal to recover the `CANId` form.
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `withWS`         — between "VAL_" and rawId, between rawId and
--                        sigId, and within each value entry (×2).
--   * `withWSCanonOne` — between the last entry and `;` (parseWSOpt; the
--                        formatter emits exactly one space there).
--   * `newlineFmt`     — line terminator; canonical emit `'\n'`, parser
--                        accepts `'\n'` and `'\r\n'`.
--
-- Trailing `many parseNewline` (zero-or-more blank lines after the line
-- terminator) lives in the wrapper `parseValueDescription`, NOT in this
-- Format — same pattern as `parseValueTable` vs `ValueTable-format`.
module Aletheia.DBC.TextParser.Format.ValueDescription where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition;
         advancePositions; parseCharsSeq; pure; _>>=_)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showNat-chars; quoteStringLit-chars; digitChar)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; bind-just-step; showNat-chars-head)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         altSum; ws; wsCanonOne; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany; ParseFailsAt;
         []-fails; ∷-cons;
         roundtrip)
open import Aletheia.DBC.TextParser.Format.ValueTable using
  (ValueEntry-format; build-EmitsOKMany)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirror `Format.ValueTable`)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
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
-- DSL DEFINITION
-- ============================================================================

-- Yields the raw triple `(rawId , sigId , entries)`.  CAN-ID decoding
-- (`buildCANId`) happens OUTSIDE the DSL because it's partial; the DSL
-- requires a total bijection at every `iso` slot.  The slim roundtrip
-- in `Properties/ValueTables/ValueDesc.agda` chains the DSL universal
-- with `buildCANId-rawCanIdℕ` to recover the `RawValueDesc` form.
ValueDescription-format : Format (ℕ × Identifier × List (ℕ × List Char))
ValueDescription-format =
  iso (λ x → proj₁ x , proj₁ (proj₂ x) , proj₁ (proj₂ (proj₂ x)))
      (λ x → proj₁ x , proj₁ (proj₂ x) , proj₂ (proj₂ x) , tt)
      (λ _ → refl)
      (withPrefix (toList "VAL_") (
        pair (withWS nat) (
          pair (withWS ident) (
            pair (many ValueEntry-format) (
              withWSCanonOne (
                withPrefix (';' ∷ []) newlineFmt))))))

-- ============================================================================
-- PER-LINE PRECONDITION
-- ============================================================================

-- The signal `Identifier`'s first char must be non-`isHSpace`, so the
-- `withWS ident` slot's `SuffixStops isHSpace (Identifier.name sigId ++
-- rest)` obligation reduces to `∷-stop c-non-hspace`.  Layer 4 will
-- discharge this universally from `validIdentifierᵇ` via the
-- `isIdentStart→¬isHSpace` bridge — same pattern as
-- `ValueTableNameStop`.
RawValueDescNameStop : Identifier → Set
RawValueDescNameStop sigId =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name sigId ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- PRIVATE HELPERS — char-class reductions on emitted heads
-- ============================================================================

private
  -- The head of `showNat-chars n` is `digitChar k` for some `k`; every
  -- closed digit char fails `isHSpace`.  Local mirror of the same
  -- helper in `Format.ValueTable.agda` (kept private there).  TODO:
  -- consolidate into a shared module if either site grows further.
  digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
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

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- Build `EmitsOK ValueDescription-format (rawId , sigId , entries)
-- outer-suffix` from the single domain precondition `RawValueDescName-
-- Stop sigId`.  Reduces structurally through `iso → withPrefix → pair →
-- withWS nat → withWS ident → many → withWSCanonOne → withPrefix →
-- newlineFmt`.  Two cases on entries (empty / non-empty) parallel
-- `Format.ValueTable.build-emits-ok`.
build-emits-ok-vd : ∀ (rawId : ℕ) (sigId : Identifier)
                     (entries : List (ℕ × List Char)) (outer-suffix : List Char)
  → RawValueDescNameStop sigId
  → EmitsOK ValueDescription-format (rawId , sigId , entries) outer-suffix
build-emits-ok-vd rawId sigId [] outer-suffix
                  (c , cs , name-eq , c-non-hs) =
  -- "VAL_" literal: vacuous (tt).
  tt ,
  -- (withWS nat rawId):
  -- SuffixStops isHSpace (showNat-chars rawId ++ rest1) — head is digit.
  -- SuffixStops isDigit rest1                            — head is ' '.
  ((showNat-head-non-hspace rawId
      (emit (pair (withWS ident)
                  (pair (many ValueEntry-format)
                        (withWSCanonOne
                          (withPrefix (';' ∷ []) newlineFmt))))
            (sigId , [] , tt) ++ₗ outer-suffix))
   , ∷-stop refl) ,
  -- (withWS ident sigId):
  -- SuffixStops isHSpace (name ++ rest2) — head c, c-non-hs witness.
  -- SuffixStops isIdentCont rest2        — head ' ', non-ident-cont.
  ((subst (λ xs → SuffixStops isHSpace
                    (xs ++ₗ ' ' ∷ ';' ∷ '\n' ∷ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs))
   , ∷-stop refl) ,
  -- (many ValueEntry-format []): EmitsOKMany on empty entries.
  build-EmitsOKMany [] outer-suffix ,
  -- (withWSCanonOne (withPrefix ";" newlineFmt)) tt outer-suffix.
  (∷-stop refl
   , (tt
     , (tt , (λ pos → refl))))
build-emits-ok-vd rawId sigId ((v , d) ∷ rest) outer-suffix
                  (c , cs , name-eq , c-non-hs) =
  tt ,
  ((showNat-head-non-hspace rawId
      (emit (pair (withWS ident)
                  (pair (many ValueEntry-format)
                        (withWSCanonOne
                          (withPrefix (';' ∷ []) newlineFmt))))
            (sigId , (v , d) ∷ rest , tt) ++ₗ outer-suffix))
   , ∷-stop refl) ,
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

-- THE GATE: parseValueDescription-format expressed via Format DSL.  Body
-- is one `roundtrip` call + the EmitsOK construction.  Universal in
-- `(rawId , sigId , entries)` and `outer-suffix`; the only domain
-- precondition is `RawValueDescNameStop sigId`.  Layer 4 will discharge
-- this universally from `validIdentifierᵇ`.
parseValueDescription-format-roundtrip :
    ∀ (pos : Position) (rawId : ℕ) (sigId : Identifier)
      (entries : List (ℕ × List Char)) (outer-suffix : List Char)
  → RawValueDescNameStop sigId
  → parse ValueDescription-format pos
      (emit ValueDescription-format (rawId , sigId , entries) ++ₗ outer-suffix)
    ≡ just (mkResult (rawId , sigId , entries)
             (advancePositions pos
               (emit ValueDescription-format (rawId , sigId , entries)))
             outer-suffix)
parseValueDescription-format-roundtrip pos rawId sigId entries outer-suffix nameStop =
  roundtrip ValueDescription-format pos (rawId , sigId , entries) outer-suffix
    (build-emits-ok-vd rawId sigId entries outer-suffix nameStop)
