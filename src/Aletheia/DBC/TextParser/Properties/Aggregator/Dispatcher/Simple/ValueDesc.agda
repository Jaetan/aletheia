{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c / Phase E.5β — TVD dispatcher under head-dispatched
-- parseTopStmt.
--
-- `emitValueDescription-chars rvd ++ outer` starts with 'V' (followed by
-- 'A' ∷ 'L' ∷ '_' ∷ ' ' ∷ …), so parseTopStmt reduces (by head pattern
-- match) to its V-bucket:
--   `(parseValueTable       >>= λ vt  → pure (TSValueTable vt))
--    <|> (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd))`.
--
-- The LEFT arm fails because `parseValueTable`'s underlying DSL
-- `withPrefix (toList "VAL_TABLE_") …` consumes V, A, L, _ then expects
-- 'T' but finds ' '.  `parseCharsSeq` returns `nothing` and the bind
-- chain propagates.  `alt-right-nothing` then reduces the `<|>` to its
-- right arm; `bind-just-step` over the slim `parseValueDescription-
-- roundtrip` closes the dispatcher.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.ValueDesc where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure; _<|>_)

open import Aletheia.DBC.TextParser.ValueTables using
  (RawValueDesc; parseValueTable; parseValueDescription)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSValueTable; TSValueDesc; parseTopStmt)

open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueDescription-chars)

open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueDesc using
  (parseValueDescription-roundtrip; RawValueDescStop)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-right-nothing; bind-nothing)

-- ============================================================================
-- LEFT-ARM FAILURE: parseValueTable rejects VAL_-prefix input
-- ============================================================================

-- `emitValueDescription-chars rvd ++ outer` starts with the concrete
-- prefix `'V' ∷ 'A' ∷ 'L' ∷ '_' ∷ ' ' ∷ …` (from `toList "VAL_ "`).
-- parseValueTable's DSL `withPrefix (toList "VAL_TABLE_") …` consumes
-- through `_`, then `parseCharsSeq` rejects ' ' (expecting 'T').  The
-- bind chain in `parseValueTable = parse ValueTable-format >>= many
-- parseNewline >>= pure` propagates `nothing`.
--
-- All of this reduces definitionally because the leading 5 chars of
-- `emitValueDescription-chars rvd` are `toList "VAL_ "` (a closed string
-- literal that Agda reduces eagerly).  `refl` closes.
parseValueTable-fails-on-VAL_-prefix :
    ∀ (pos : Position) (rvd : RawValueDesc) (outer : List Char)
  → parseValueTable pos (emitValueDescription-chars rvd ++ₗ outer) ≡ nothing
parseValueTable-fails-on-VAL_-prefix _ _ _ = refl

-- ============================================================================
-- TVD DISPATCHER
-- ============================================================================

parseTopStmt-on-emit-TVD-eq :
    ∀ (pos : Position) (rvd : RawValueDesc) (outer : List Char)
  → RawValueDescStop rvd
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitValueDescription-chars rvd ++ₗ outer)
    ≡ just (mkResult (TSValueDesc rvd)
                     (advancePositions pos (emitValueDescription-chars rvd))
                     outer)
parseTopStmt-on-emit-TVD-eq pos rvd outer rvd-stop nl-stop =
  trans alt-right-eq bind-success-eq
  where
    input : List Char
    input = emitValueDescription-chars rvd ++ₗ outer

    pos-vd : Position
    pos-vd = advancePositions pos (emitValueDescription-chars rvd)

    -- LEFT arm fails: parseValueTable returns nothing.
    parseValueTable-nothing :
        parseValueTable pos input ≡ nothing
    parseValueTable-nothing =
      parseValueTable-fails-on-VAL_-prefix pos rvd outer

    -- LEFT arm with bind: also nothing.
    bind-left-nothing :
        (parseValueTable >>= λ vt → pure (TSValueTable vt)) pos input ≡ nothing
    bind-left-nothing =
      bind-nothing parseValueTable (λ vt → pure (TSValueTable vt))
        pos input parseValueTable-nothing

    -- alt-right-nothing reduces the `<|>` to its right arm.  parseTopStmt
    -- on the input reduces to parseTopStmt-V via head dispatch (refl);
    -- alt-right-nothing then collapses the LEFT arm and exposes the
    -- RIGHT arm.
    alt-right-eq :
        parseTopStmt pos input
      ≡ (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd)) pos input
    alt-right-eq =
      alt-right-nothing
        (parseValueTable       >>= λ vt  → pure (TSValueTable vt))
        (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd))
        pos input bind-left-nothing

    -- RIGHT arm succeeds: parseValueDescription pos input → just (mkResult rvd …).
    parseValueDescription-success :
        parseValueDescription pos input
      ≡ just (mkResult rvd pos-vd outer)
    parseValueDescription-success =
      parseValueDescription-roundtrip pos rvd outer rvd-stop nl-stop

    -- bind-just-step chains the RIGHT arm's success through the
    -- `>>= λ rvd → pure (TSValueDesc rvd)` continuation.
    bind-success-eq :
        (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd)) pos input
      ≡ just (mkResult (TSValueDesc rvd) pos-vd outer)
    bind-success-eq =
      bind-just-step parseValueDescription
                     (λ rvd → pure (TSValueDesc rvd))
                     pos input rvd pos-vd outer
                     parseValueDescription-success
