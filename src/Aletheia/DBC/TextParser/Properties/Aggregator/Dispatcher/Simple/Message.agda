{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TM dispatcher under head-dispatched parseTopStmt.
--
-- `emitMessage-chars msg ++ outer` starts with 'B'∷'O'∷'_'∷' ', so
-- parseTopStmt reduces to its BO-bucket:
-- `(parseBOTxBu *> pure TSBOTxBu) <|> (parseMessage >>= λ m → pure (TSMessage m))`.
--
-- parseBOTxBu requires `string "BO_TX_BU_"` (char 3 = 'T'); on the
-- emitter's `'B'∷'O'∷'_'∷' '∷…` it fails at char 3.  parseMessage
-- succeeds via `parseMessage-roundtrip-bundled`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.Message where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure; _<|>_; _*>_)

open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSMessage; TSBOTxBu; parseTopStmt; parseBOTxBu)
open import Aletheia.DBC.TextParser.Topology using
  (parseMessage)

open import Aletheia.DBC.TextFormatter.Topology using
  (emitMessage-chars)

open import Aletheia.DBC.TextParser.Properties.Topology.Message using
  (parseMessage-roundtrip-bundled; MessageWF)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-right-nothing)

parseTopStmt-on-emit-TM-eq :
    ∀ (pos : Position) (msg : DBCMessage) (outer : List Char)
  → MessageWF msg
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitMessage-chars msg ++ₗ outer)
    ≡ just (mkResult (TSMessage msg)
                     (advancePositions pos (emitMessage-chars msg))
                     outer)
parseTopStmt-on-emit-TM-eq pos msg outer wf nl-stop =
  trans (alt-right-nothing (parseBOTxBu *> pure TSBOTxBu)
                            (parseMessage >>= λ m → pure (TSMessage m))
                            pos input
                            botxbu-fail)
        alt-msg-eq
  where
    input : List Char
    input = emitMessage-chars msg ++ₗ outer

    pos-msg : Position
    pos-msg = advancePositions pos (emitMessage-chars msg)

    botxbu-fail : (parseBOTxBu *> pure TSBOTxBu) pos input ≡ nothing
    botxbu-fail = refl

    p-msg-eq : parseMessage pos input ≡ just (mkResult msg pos-msg outer)
    p-msg-eq = parseMessage-roundtrip-bundled pos msg outer wf nl-stop

    alt-msg-eq : (parseMessage >>= λ m → pure (TSMessage m)) pos input
                 ≡ just (mkResult (TSMessage msg) pos-msg outer)
    alt-msg-eq = bind-just-step parseMessage (λ m → pure (TSMessage m))
                   pos input msg pos-msg outer p-msg-eq
