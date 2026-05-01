{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — slim `parseValueTable-roundtrip` derived from
-- the universal Format DSL roundtrip.
--
-- Pre-3d.5.d (3b): hand-written 790-line bind-chain proof through 9
-- parser primitives; total ~613 strict-code-LOC.
--
-- Post-3d.5.d: `parseValueTable = parse ValueTable-format >>= many
-- parseNewline >>= pure` (in `TextParser.ValueTables`), and the
-- roundtrip reduces to:
--
--   1. A bridge `emit-ValueTable-format-eq-emitValueTable-chars` proving
--      DSL emit on `vt` equals existing `emitValueTable-chars vt`.
--   2. The universal `parseValueTable-format-roundtrip` (from
--      `Format.ValueTable`).
--   3. The trailing `many parseNewline` consuming zero from the user's
--      `suffix` (via `manyHelper-parseNewline-exhaust` + the existing
--      `SuffixStops isNewlineStart suffix` precondition).
--
-- The `ValueTableNameStop` precondition migrates upstream to
-- `Format.ValueTable`; this module re-exports it for source compatibility
-- with the section facade and any Layer-4 composer that imported the
-- pre-3d.5.d location.
module Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr; concatMap; length)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (++-identityʳ) renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Lexer using
  (parseNewline)
open import Aletheia.DBC.TextParser.ValueTables using
  (parseValueTable)
open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueTable-chars; emitValueEntry-chars)
open import Aletheia.DBC.Types using (ValueTable)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; ∷-stop)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
  renaming (many to manyF)
open import Aletheia.DBC.TextParser.Format.ValueTable as FmtVT using
  (ValueTable-format; ValueEntry-format)

-- ============================================================================
-- RE-EXPORT — `ValueTableNameStop` migrated to `Format.ValueTable`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.ValueTable public
  using (ValueTableNameStop)

-- ============================================================================
-- BRIDGE: DSL emit ≡ existing emitValueTable-chars
-- ============================================================================

-- Per-entry: the DSL emit reduces (through `iso → pair → withWS`) to
-- `' ' ∷ showNat-chars v ++ ' ' ∷ quoteStringLit-chars d`, definitionally
-- equal to `emitValueEntry-chars (v , d)` since `showℕ-dec-chars =
-- showNat-chars` (alias in `Emitter.agda`).
emit-ValueEntry-format-eq-emitValueEntry-chars :
  ∀ (e : ℕ × List Char)
  → emit ValueEntry-format e ≡ emitValueEntry-chars e
emit-ValueEntry-format-eq-emitValueEntry-chars (v , d) = refl

-- Entries fold: `concatMap (emit ValueEntry-format) entries ++ terminator
-- ≡ foldr (λ e acc → emitValueEntry-chars e ++ acc) terminator entries`.
-- Closes by structural induction over `entries`; the cons case unfolds
-- `concatMap` then re-associates `++` to push `terminator` inside the
-- recursion.
emit-many-eq-foldr : ∀ (entries : List (ℕ × List Char)) (terminator : List Char)
  → emit (manyF ValueEntry-format) entries ++ₗ terminator
    ≡ foldr (λ e acc → emitValueEntry-chars e ++ₗ acc) terminator entries
emit-many-eq-foldr [] terminator = refl
emit-many-eq-foldr (e ∷ rest) terminator =
  trans (++ₗ-assoc (emit ValueEntry-format e)
                    (emit (manyF ValueEntry-format) rest)
                    terminator)
        (cong (emit ValueEntry-format e ++ₗ_)
              (emit-many-eq-foldr rest terminator))

-- Top-level bridge: full `emit ValueTable-format vt ≡ emitValueTable-chars vt`.
-- LHS reduces (through nested isos) to:
--   "VAL_TABLE_" ++ ' ' ∷ name ++ concatMap (emit ValueEntry-format) entries
--                          ++ ' ' ∷ ';' ∷ '\n' ∷ []
-- RHS reduces to:
--   toList "VAL_TABLE_ " ++ name ++ foldr (...) (toList " ;\n") entries
-- The "VAL_TABLE_" / "VAL_TABLE_ " prefix split + ' ' / Identifier.name
-- composition collapses definitionally (cons-of-list's right-assoc
-- with `++`); the entries-fold step uses `emit-many-eq-foldr`.
emit-ValueTable-format-eq-emitValueTable-chars : ∀ (vt : ValueTable)
  → emit ValueTable-format vt ≡ emitValueTable-chars vt
emit-ValueTable-format-eq-emitValueTable-chars vt =
  cong (λ x → toList "VAL_TABLE_ " ++ₗ Identifier.name (ValueTable.name vt) ++ₗ x)
       (emit-many-eq-foldr (ValueTable.entries vt) (toList " ;\n"))

-- ============================================================================
-- SLIM `parseValueTable-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseValueTable = parse ValueTable-format >>= λ vt →
-- many parseNewline >>= λ _ → pure vt`.  Composition decomposes into:
--
--   1. `parse ValueTable-format pos (emit ValueTable-format vt ++ suffix)`
--      via `parseValueTable-format-roundtrip`.
--   2. `many parseNewline pos' suffix` returning `[]`-no-consume via
--      `manyHelper-parseNewline-exhaust` + `nl-stop` precondition.
--   3. `pure vt` returns the input value at the resulting position.
--
-- `subst` on input/output positions converts between `emit ValueTable-format
-- vt` and `emitValueTable-chars vt` via the bridge.
parseValueTable-roundtrip :
    ∀ (pos : Position) (vt : ValueTable) (suffix : List Char)
  → ValueTableNameStop vt
  → SuffixStops isNewlineStart suffix
  → parseValueTable pos (emitValueTable-chars vt ++ₗ suffix)
    ≡ just (mkResult vt
             (advancePositions pos (emitValueTable-chars vt))
             suffix)
parseValueTable-roundtrip pos vt suffix nameStop nl-stop =
  trans (cong (λ inp → parseValueTable pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-pure))
  where
    bridge : emit ValueTable-format vt ≡ emitValueTable-chars vt
    bridge = emit-ValueTable-format-eq-emitValueTable-chars vt

    pos-line : Position
    pos-line = advancePositions pos (emit ValueTable-format vt)

    cont-line : ValueTable → Parser ValueTable
    cont-line v = many parseNewline >>= λ _ → pure v

    cont-blanks : List Char → Parser ValueTable
    cont-blanks _ = pure vt

    -- Step 1: parse ValueTable-format succeeds via the universal roundtrip.
    step-format :
      parseValueTable pos (emit ValueTable-format vt ++ₗ suffix)
      ≡ cont-line vt pos-line suffix
    step-format =
      bind-just-step (parse ValueTable-format)
                     cont-line
                     pos (emit ValueTable-format vt ++ₗ suffix)
                     vt pos-line suffix
                     (FmtVT.parseValueTable-format-roundtrip
                       pos vt suffix nameStop)

    -- Step 2: many parseNewline consumes zero from `suffix`.
    step-many-newline :
      cont-line vt pos-line suffix
      ≡ cont-blanks [] pos-line suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (Data.List.length suffix) nl-stop)
      where
        open import Data.List using (length)

    -- Step 3: pure vt returns just (mkResult vt pos-line suffix); convert
    -- pos-line back to `advancePositions pos (emitValueTable-chars vt)`
    -- via the bridge.
    step-pure :
      cont-blanks [] pos-line suffix
      ≡ just (mkResult vt
               (advancePositions pos (emitValueTable-chars vt))
               suffix)
    step-pure =
      cong (λ p → just (mkResult vt p suffix))
           (cong (advancePositions pos) bridge)


-- ============================================================================
-- LIST-LEVEL ROUNDTRIP — `many parseValueTable` over a VAL_TABLE_ block
-- ============================================================================

-- `0 < length (emitValueTable-chars vt)` — the literal `"VAL_TABLE_ "`
-- prefix gives an 11-byte head.
emitValueTable-chars-nonzero : ∀ (vt : ValueTable)
  → 0 < length (emitValueTable-chars vt)
emitValueTable-chars-nonzero _ = s≤s z≤n

-- Head of `emitValueTable-chars vt` is `'V'` — not a newline-start.
emitValueTable-chars-head-not-newline :
    ∀ (vt : ValueTable) (suffix : List Char)
  → SuffixStops isNewlineStart (emitValueTable-chars vt ++ₗ suffix)
emitValueTable-chars-head-not-newline _ _ = ∷-stop refl


parseValueTables-roundtrip :
    ∀ (pos : Position) (vts : List ValueTable) (outer-suffix : List Char)
  → All ValueTableNameStop vts
  → SuffixStops isNewlineStart outer-suffix
  → (∀ (pos' : Position) → parseValueTable pos' outer-suffix ≡ nothing)
  → many parseValueTable pos
      (foldr (λ vt acc → emitValueTable-chars vt ++ₗ acc) [] vts ++ₗ outer-suffix)
    ≡ just (mkResult vts
             (advancePositions pos
               (foldr (λ vt acc → emitValueTable-chars vt ++ₗ acc) [] vts))
             outer-suffix)
parseValueTables-roundtrip pos vts outer-suffix vts-stops os pf =
  many-η-roundtrip
    parseValueTable
    emitValueTable-chars
    ValueTableNameStop
    (λ pos₁ vt suffix nameStop nl-stop →
       parseValueTable-roundtrip pos₁ vt suffix nameStop nl-stop)
    emitValueTable-chars-nonzero
    emitValueTable-chars-head-not-newline
    pos vts outer-suffix vts-stops os pf
  where
    open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip using
      (many-η-roundtrip)
