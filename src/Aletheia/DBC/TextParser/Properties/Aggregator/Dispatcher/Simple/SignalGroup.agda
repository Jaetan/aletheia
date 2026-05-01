{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TSG dispatcher under head-dispatched parseTopStmt.
--
-- `emitSignalGroup-chars sg ++ outer` starts with 'S'∷'I'∷'G'∷'_'∷'G'…,
-- so parseTopStmt reduces to its SI-bucket:
-- `(parseSigValType *> pure TSSigValType)
--   <|> (parseSignalGroup >>= λ g → pure (TSSignalGroup g))`.
--
-- parseSigValType requires `string "SIG_VALTYPE_"` (char 4 = 'V'); on
-- the emitter's `'S'∷'I'∷'G'∷'_'∷'G'∷…` it fails at char 4.  parseSignalGroup
-- succeeds via `parseSignalGroup-roundtrip`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.SignalGroup where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure; _<|>_; _*>_)

open import Aletheia.DBC.Types using (SignalGroup)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSSignalGroup; TSSigValType; parseTopStmt)
open import Aletheia.DBC.TextParser.SignalGroups using
  (parseSignalGroup)
open import Aletheia.DBC.TextParser.ValueTypes using
  (parseSigValType)

open import Aletheia.DBC.TextFormatter.SignalGroups using
  (emitSignalGroup-chars)

open import Aletheia.DBC.TextParser.Properties.SignalGroups.SignalGroup using
  (parseSignalGroup-roundtrip; SignalGroupWF)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-right-nothing)

parseTopStmt-on-emit-TSG-eq :
    ∀ (pos : Position) (sg : SignalGroup) (outer : List Char)
  → SignalGroupWF sg
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitSignalGroup-chars sg ++ₗ outer)
    ≡ just (mkResult (TSSignalGroup sg)
                     (advancePositions pos (emitSignalGroup-chars sg))
                     outer)
parseTopStmt-on-emit-TSG-eq pos sg outer wf nl-stop =
  trans (alt-right-nothing (parseSigValType  *> pure TSSigValType)
                            (parseSignalGroup >>= λ g → pure (TSSignalGroup g))
                            pos input
                            sigvaltype-fail)
        alt-sg-eq
  where
    input : List Char
    input = emitSignalGroup-chars sg ++ₗ outer

    pos-sg : Position
    pos-sg = advancePositions pos (emitSignalGroup-chars sg)

    sigvaltype-fail : (parseSigValType *> pure TSSigValType) pos input ≡ nothing
    sigvaltype-fail = refl

    p-sg-eq : parseSignalGroup pos input ≡ just (mkResult sg pos-sg outer)
    p-sg-eq = parseSignalGroup-roundtrip pos sg outer
                (SignalGroupWF.name-stop wf)
                (SignalGroupWF.sigs-stops wf)
                nl-stop

    alt-sg-eq : (parseSignalGroup >>= λ g → pure (TSSignalGroup g)) pos input
                ≡ just (mkResult (TSSignalGroup sg) pos-sg outer)
    alt-sg-eq = bind-just-step parseSignalGroup (λ g → pure (TSSignalGroup g))
                  pos input sg pos-sg outer p-sg-eq
