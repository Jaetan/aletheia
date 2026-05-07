{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TVT dispatcher under head-dispatched parseTopStmt.
--
-- `emitValueTable-chars vt ++ outer` starts with 'V', so parseTopStmt
-- reduces (by head pattern match on its first char) to its V-bucket:
-- `(parseValueTable       >>= λ vt  → pure (TSValueTable vt))
--   <|> (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd))`.
-- (Track E.4 lifted the second arm from `*> pure TSValueDesc` to bind
-- the `RawValueDesc` payload — the `alt-left-just` proof is polymorphic
-- in the right arm so this dispatcher closes unchanged.)
--
-- The dispatcher just promotes parseValueTable's success witness into the
-- 2-way `<|>` via `alt-left-just`.  No 10-way chain to walk.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.ValueTable where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure; _<|>_)

open import Aletheia.DBC.Types using (ValueTable)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSValueTable; TSValueDesc; parseTopStmt)
open import Aletheia.DBC.TextParser.ValueTables using
  (parseValueTable; parseValueDescription)

open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueTable-chars)

open import Aletheia.DBC.TextParser.Properties.ValueTables using
  (parseValueTable-roundtrip; ValueTableNameStop)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-left-just)

parseTopStmt-on-emit-TVT-eq :
    ∀ (pos : Position) (vt : ValueTable) (outer : List Char)
  → ValueTableNameStop vt
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitValueTable-chars vt ++ₗ outer)
    ≡ just (mkResult (TSValueTable vt)
                     (advancePositions pos (emitValueTable-chars vt))
                     outer)
parseTopStmt-on-emit-TVT-eq pos vt outer name-stop nl-stop =
  alt-left-just (parseValueTable       >>= λ vt  → pure (TSValueTable vt))
                (parseValueDescription >>= λ rvd → pure (TSValueDesc rvd))
                pos input result
                alt-vt-eq
  where
    input : List Char
    input = emitValueTable-chars vt ++ₗ outer

    pos-vt : Position
    pos-vt = advancePositions pos (emitValueTable-chars vt)

    result : ParseResult TopStmt
    result = mkResult (TSValueTable vt) pos-vt outer

    p-vt-eq : parseValueTable pos input ≡ just (mkResult vt pos-vt outer)
    p-vt-eq = parseValueTable-roundtrip pos vt outer name-stop nl-stop

    alt-vt-eq : (parseValueTable >>= λ vt → pure (TSValueTable vt)) pos input
                ≡ just result
    alt-vt-eq = bind-just-step parseValueTable (λ vt → pure (TSValueTable vt))
                  pos input vt pos-vt outer p-vt-eq
