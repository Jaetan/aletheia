{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.b — gate-target: parseValueTable expressed in the
-- Format DSL.  The proof of `parseValueTable-format-roundtrip` measures
-- the framework's payoff: the existing per-construct
-- `parseValueTable-roundtrip` in
-- `Properties/ValueTables/ValueTable.agda` is 790 LOC; the DSL version
-- below targets <50 LOC, gate <100 LOC.
--
-- Note: `parse ValueTable-format` is canonical-only — it accepts
-- exactly one space everywhere `parseWS`/`parseWSOpt` is canonical (the
-- existing parser is more permissive).  3d.5.d migration phase will
-- consolidate, replacing the existing `parseValueTable` with the DSL one;
-- here we just validate the framework.
module Aletheia.DBC.TextParser.Format.ValueTable where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition;
         advancePositions; parseCharsSeq; pure; _>>=_)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.Types using (ValueTable)
open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; bind-just-step)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         emit; parse; EmitsOK; EmitsOKMany; ParseFailsAt;
         []-fails; ∷-cons;
         roundtrip)

-- ============================================================================
-- DSL DEFINITIONS
-- ============================================================================

-- One ` <nat> "<desc>"` entry — single-space-separated nat then quoted
-- string-literal description.  ⊤s in the carrier come from the literal
-- spaces; `iso` projects them out so the user-facing carrier is `(ℕ × List Char)`.
ValueEntry-format : Format (ℕ × List Char)
ValueEntry-format =
  iso fwd bwd
      (λ _ → refl)
      (pair (literal (' ' ∷ []))
        (pair nat
          (pair (literal (' ' ∷ [])) stringLit)))
  where
    fwd : ⊤ × ℕ × ⊤ × List Char → ℕ × List Char
    fwd (_ , v , _ , d) = v , d

    bwd : ℕ × List Char → ⊤ × ℕ × ⊤ × List Char
    bwd (v , d) = tt , v , tt , d

-- Full `VAL_TABLE_ <name>(<entries>) ;\n` line.  Everything is fixed-string
-- between sub-parts; record-η makes the iso's roundtrip equation `refl`.
ValueTable-format : Format ValueTable
ValueTable-format =
  iso fwd bwd
      (λ _ → refl)
      (pair (literal (toList "VAL_TABLE_ "))
        (pair ident
          (pair (many ValueEntry-format)
            (literal (toList " ;\n")))))
  where
    fwd : ⊤ × Identifier × List (ℕ × List Char) × ⊤ → ValueTable
    fwd (_ , name , entries , _) = record { name = name ; entries = entries }

    bwd : ValueTable → ⊤ × Identifier × List (ℕ × List Char) × ⊤
    bwd vt = tt , ValueTable.name vt , ValueTable.entries vt , tt

-- ============================================================================
-- TERMINATION CERTIFICATE — `parse ValueEntry-format` rejects ` ;…`
-- ============================================================================

-- After all entries are parsed, the trailing input is ` ;\n…` (the
-- canonical terminator).  `parse ValueEntry-format` consumes the first
-- ` ` then fails on `;` (not a digit).  Provides `ParseFailsAt
-- ValueEntry-format (' ' ∷ ';' ∷ '\n' ∷ outer)` for `EmitsOKMany`'s
-- `[]-fails` constructor at the empty-entries-tail step.
--
-- `refl` is load-bearing: relies on Agda definitionally reducing the
-- bind chain through `iso` → `pair` → `parseCharsSeq` (head-match on
-- `' '`) → `parseNatural` (digit-match failing on `';'`).  If any layer
-- gets a `with`-abstraction in the future (e.g., a non-trivial
-- computation in `parse (iso _)` or `parseNatural`'s match), this
-- `refl` will fail and pinpoint the regression.
parseValueEntry-format-fails-on-semi : ∀ pos rest
  → parse ValueEntry-format pos (' ' ∷ ';' ∷ rest) ≡ nothing
parseValueEntry-format-fails-on-semi pos rest = refl

-- ============================================================================
-- WELL-FORMEDNESS CONSTRUCTORS — the per-construct compatibility witness
-- ============================================================================

-- Recursive: build `EmitsOKMany ValueEntry-format` from a list of
-- entries and the canonical trailing ` ;\n outer-suffix`.  Each entry
-- emits `' ' ∷ showNat-chars v ++ ' ' ∷ quoteStringLit-chars d`,
-- always non-empty (≥ 4 chars), so the `∷-cons` non-empty witness is
-- `s≤s z≤n`.  Per-entry `EmitsOK` is structural ⊤s + `∷-stop refl` on
-- heads (every residual head is `' '`, definitionally non-isDigit,
-- non-`"`, non-isIdentCont).
--
-- The two non-empty branches differ only in the residual after the
-- current entry: empty `rest` reduces to ` ;\n…`, non-empty `rest` to
-- the next entry's leading ` `.  Splitting on `rest` is mandatory —
-- without the constructor visible, `concatMap (emit f) rest` doesn't
-- reduce and the `∷-stop refl` on the stringLit step won't typecheck.
build-EmitsOKMany : ∀ (entries : List (ℕ × List Char)) (outer-suffix : List Char)
  → EmitsOKMany ValueEntry-format entries
      (' ' ∷ ';' ∷ '\n' ∷ outer-suffix)
build-EmitsOKMany [] outer-suffix =
  []-fails (λ pos → parseValueEntry-format-fails-on-semi pos
                      ('\n' ∷ outer-suffix))
build-EmitsOKMany ((v , d) ∷ []) outer-suffix =
  ∷-cons (tt , ∷-stop refl , tt , ∷-stop refl)
         (s≤s z≤n)
         (build-EmitsOKMany [] outer-suffix)
build-EmitsOKMany ((v , d) ∷ ((v' , d') ∷ rest')) outer-suffix =
  ∷-cons (tt , ∷-stop refl , tt , ∷-stop refl)
         (s≤s z≤n)
         (build-EmitsOKMany ((v' , d') ∷ rest') outer-suffix)

-- ============================================================================
-- TOP-LEVEL EMITSOK + ROUNDTRIP — the gate
-- ============================================================================

-- Build `EmitsOK ValueTable-format vt outer-suffix`.  The ident step's
-- SuffixStops on `(emit-many entries ++ ' ' ∷ ';' ∷ '\n' ∷ outer-suffix)`
-- requires the head of that string to be non-isIdentCont.  Both branches
-- (empty and non-empty entries) yield head=' '; we case-split on entries
-- so the head reduces definitionally.
build-emits-ok : ∀ (vt : ValueTable) outer-suffix
  → EmitsOK ValueTable-format vt outer-suffix
build-emits-ok record { name = name ; entries = [] } outer-suffix =
  tt ,                              -- "VAL_TABLE_ " literal
  ∷-stop refl ,                     -- ident: head ' ' (entries empty → terminator " ;\n")
  build-EmitsOKMany [] outer-suffix , -- many over empty
  tt                                -- " ;\n" literal
build-emits-ok record { name = name ; entries = (v , d) ∷ rest } outer-suffix =
  tt ,
  ∷-stop refl ,                     -- ident: head ' ' (entries non-empty → first entry's literal " ")
  build-EmitsOKMany ((v , d) ∷ rest) outer-suffix ,
  tt

-- THE GATE: parseValueTable expressed via Format DSL.  Body is one
-- `roundtrip` call + the EmitsOK construction; total LOC for the proof
-- (this file's contents minus header) is the gate measurement.
parseValueTable-format-roundtrip : ∀ pos vt outer-suffix
  → parse ValueTable-format pos
      (emit ValueTable-format vt ++ₗ outer-suffix)
    ≡ just (mkResult vt
             (advancePositions pos (emit ValueTable-format vt))
             outer-suffix)
parseValueTable-format-roundtrip pos vt outer-suffix =
  roundtrip ValueTable-format pos vt outer-suffix
    (build-emits-ok vt outer-suffix)
