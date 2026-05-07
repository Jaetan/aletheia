{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 / Track E.5β — slim `parseValueDescription-roundtrip`
-- derived from the universal Format DSL roundtrip + `buildCANId-
-- rawCanIdℕ` inverse witness.
--
-- Structure (parallels `Properties.ValueTables.ValueTable`):
--
--   1. A bridge `emit-ValueDescription-format-eq-emitValueDescription-chars`
--      proving DSL emit on the raw triple equals existing
--      `emitValueDescription-chars rvd`.
--   2. The universal `parseValueDescription-format-roundtrip` (from
--      `Format.ValueDescription`).
--   3. The trailing `many parseNewline` consuming zero from the user's
--      `suffix` (via `manyHelper-parseNewline-exhaust` + the existing
--      `SuffixStops isNewlineStart suffix` precondition).
--   4. `buildResultP (buildCANId rawId) sigId vds`: rewrites
--      `buildCANId (rawCanIdℕ rvd.canId)` to `just rvd.canId` via the
--      `buildCANId-rawCanIdℕ` inverse witness, then `buildResultP (just
--      rvd.canId) rvd.signalName rvd.entries = pure rvd` reduces by
--      record-η on `RawValueDesc`.
--
-- The `RawValueDescStop` precondition migrates upstream to
-- `Format.ValueDescription`; this module re-exports it for source
-- compatibility with the section facade and any Layer-4 composer.
module Aletheia.DBC.TextParser.Properties.ValueTables.ValueDesc where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr; length)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.ValueTables using
  (RawValueDesc; mkRawValueDesc; parseValueDescription; buildResultP)
open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueDescription-chars; emitValueEntry-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

-- DSL framework + `ValueDescription-format` Format.
open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
  renaming (many to manyF)
open import Aletheia.DBC.TextParser.Format.ValueDescription as FmtVD using
  (ValueDescription-format; RawValueDescNameStop)

-- Reuse the per-entries `emit-many-eq-foldr` bridge from the VAL_TABLE_
-- side (the entry shape is identical — `emit ValueEntry-format e ≡
-- emitValueEntry-chars e` definitionally).
open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable using
  (emit-many-eq-foldr)

-- buildCANId inverse witness.
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  (buildCANId-rawCanIdℕ)

-- ============================================================================
-- RE-EXPORT — `RawValueDescStop` derived from upstream `RawValueDescNameStop`
-- ============================================================================

-- Per-`RawValueDesc` precondition: the signal `Identifier`'s first char
-- is non-`isHSpace`.  Layer 4 will discharge this universally from
-- `validIdentifierᵇ` (mirrors `ValueTableNameStop`).  Defined as an alias
-- so consumers can use a name keyed on the `RawValueDesc` record rather
-- than a free `Identifier`.
RawValueDescStop : RawValueDesc → Set
RawValueDescStop rvd = RawValueDescNameStop (RawValueDesc.signalName rvd)

-- ============================================================================
-- BRIDGE: DSL emit ≡ existing emitValueDescription-chars
-- ============================================================================

-- Top-level bridge: full `emit ValueDescription-format (rawCanIdℕ canId,
-- sigName, entries) ≡ emitValueDescription-chars rvd`.  LHS reduces
-- (through nested isos) to:
--   "VAL_" ++ ' ' ∷ showNat-chars rawId
--          ++ ' ' ∷ name
--          ++ concatMap (emit ValueEntry-format) entries
--          ++ ' ' ∷ ';' ∷ '\n' ∷ []
-- RHS (from `emitValueDescription-chars`):
--   toList "VAL_ " ++ showℕ-dec-chars rawId
--                  ++ ' ' ∷ name
--                  ++ foldr (...) (toList " ;\n") entries
-- The "VAL_" / "VAL_ " merge collapses definitionally (via the cons-
-- append `'V' ∷ … '_' ∷ [] ++ ' ' ∷ X = "VAL_ " ++ X` rule);
-- `showNat-chars = showℕ-dec-chars` is a definitional alias; the
-- entries-fold step uses `emit-many-eq-foldr` (reused from the VAL_TABLE_
-- side since the entry shape is identical).
emit-ValueDescription-format-eq-emitValueDescription-chars :
    ∀ (rvd : RawValueDesc)
  → emit ValueDescription-format
         ( rawCanIdℕ (RawValueDesc.canId rvd)
         , RawValueDesc.signalName rvd
         , RawValueDesc.entries rvd )
    ≡ emitValueDescription-chars rvd
emit-ValueDescription-format-eq-emitValueDescription-chars rvd =
  cong (λ x → toList "VAL_ "
              ++ₗ rawCanId-chars
              ++ₗ ' ' ∷ Identifier.name (RawValueDesc.signalName rvd)
              ++ₗ x)
       (emit-many-eq-foldr (RawValueDesc.entries rvd) (toList " ;\n"))
  where
    rawCanId-chars : List Char
    rawCanId-chars = emit Aletheia.DBC.TextParser.Format.nat
                          (rawCanIdℕ (RawValueDesc.canId rvd))

-- ============================================================================
-- SLIM `parseValueDescription-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseValueDescription = parse ValueDescription-format
-- >>= λ triple → many parseNewline >>= λ _ → buildResultP …`.
-- Composition decomposes into 4 steps as outlined in the module header.
parseValueDescription-roundtrip :
    ∀ (pos : Position) (rvd : RawValueDesc) (suffix : List Char)
  → RawValueDescStop rvd
  → SuffixStops isNewlineStart suffix
  → parseValueDescription pos (emitValueDescription-chars rvd ++ₗ suffix)
    ≡ just (mkResult rvd
             (advancePositions pos (emitValueDescription-chars rvd))
             suffix)
parseValueDescription-roundtrip pos rvd suffix nameStop nl-stop =
  trans (cong (λ inp → parseValueDescription pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-buildResult))
  where
    triple : ℕ × Identifier × List (ℕ × List Char)
    triple = ( rawCanIdℕ (RawValueDesc.canId rvd)
             , RawValueDesc.signalName rvd
             , RawValueDesc.entries rvd )

    bridge : emit ValueDescription-format triple
             ≡ emitValueDescription-chars rvd
    bridge =
      emit-ValueDescription-format-eq-emitValueDescription-chars rvd

    pos-line : Position
    pos-line = advancePositions pos (emit ValueDescription-format triple)

    cont-line : (ℕ × Identifier × List (ℕ × List Char))
              → Parser RawValueDesc
    cont-line t =
      many parseNewline >>= λ _ →
      buildResultP (buildCANId (proj₁ t))
                   (proj₁ (proj₂ t))
                   (proj₂ (proj₂ t))
      where
        open import Aletheia.DBC.TextParser.Topology.Foundations using
          (buildCANId)

    -- Step 1: parse ValueDescription-format succeeds via the universal
    -- roundtrip.
    step-format :
        parseValueDescription pos
          (emit ValueDescription-format triple ++ₗ suffix)
      ≡ cont-line triple pos-line suffix
    step-format =
      bind-just-step (parse ValueDescription-format)
                     cont-line
                     pos (emit ValueDescription-format triple ++ₗ suffix)
                     triple pos-line suffix
                     (FmtVD.parseValueDescription-format-roundtrip
                       pos
                       (rawCanIdℕ (RawValueDesc.canId rvd))
                       (RawValueDesc.signalName rvd)
                       (RawValueDesc.entries rvd)
                       suffix
                       nameStop)

    -- Step 2: many parseNewline consumes zero from `suffix`.
    cont-blanks : List Char → Parser RawValueDesc
    cont-blanks _ =
      buildResultP (buildCANId (proj₁ triple))
                   (proj₁ (proj₂ triple))
                   (proj₂ (proj₂ triple))
      where
        open import Aletheia.DBC.TextParser.Topology.Foundations using
          (buildCANId)

    step-many-newline :
        cont-line triple pos-line suffix
      ≡ cont-blanks [] pos-line suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: buildResultP resolves via buildCANId-rawCanIdℕ + record-η.
    step-buildResult :
        cont-blanks [] pos-line suffix
      ≡ just (mkResult rvd
               (advancePositions pos (emitValueDescription-chars rvd))
               suffix)
    step-buildResult =
      trans
        (cong (λ m → buildResultP m
                       (RawValueDesc.signalName rvd)
                       (RawValueDesc.entries rvd)
                       pos-line suffix)
              (buildCANId-rawCanIdℕ (RawValueDesc.canId rvd)))
        (cong (λ p → just (mkResult rvd p suffix))
              (cong (advancePositions pos) bridge))
