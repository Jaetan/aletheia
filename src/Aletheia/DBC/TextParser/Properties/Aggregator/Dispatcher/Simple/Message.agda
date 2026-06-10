-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TM dispatcher under head-dispatched parseTopStmt.
--
-- `emitMessage-chars msg ++ outer` starts with 'B'∷'O'∷'_'∷' ', so
-- parseTopStmt reduces to its BO-bucket:
-- `(parseBOTxBu >>= λ rms → pure (TSBOTxBu rms)) <|> (parseMessage >>= λ m → pure (TSMessage m))`.
--
-- parseBOTxBu (the A.2 Format-DSL parser) opens with the `"BO_TX_BU_"`
-- literal (char 3 = 'T'); on the emitter's `'B'∷'O'∷'_'∷' '∷…` it fails at
-- char 3, so the left arm is `nothing` (`botxbu-fail = refl`).  parseMessage
-- succeeds via `parseMessage-roundtrip-bundled`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.Message where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions;
   _>>=_; pure)

open import Aletheia.DBC.Types using (DBCMessage; clearBothMsg)
open import Aletheia.DBC.TextParser.TopLevel using
  (TSMessage; TSBOTxBu; parseTopStmt; parseBOTxBu)
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

-- E.9a: result is `mkResult (TSMessage (clearBothMsg msg)) …` because
-- `parseMessage-roundtrip-bundled` returns `mkResult (clearBothMsg msg) …`.
-- The Universal threads `attachValueDescs ∘ collectFromMessages ≡ id`
-- post-buildDBC to recover the original messages.
parseTopStmt-on-emit-TM-eq :
    ∀ (pos : Position) (msg : DBCMessage) (outer : List Char)
  → MessageWF msg
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitMessage-chars msg ++ₗ outer)
    ≡ just (mkResult (TSMessage (clearBothMsg msg))
                     (advancePositions pos (emitMessage-chars msg))
                     outer)
parseTopStmt-on-emit-TM-eq pos msg outer wf nl-stop =
  trans (alt-right-nothing (parseBOTxBu >>= λ rms → pure (TSBOTxBu rms))
                            (parseMessage >>= λ m → pure (TSMessage m))
                            pos input
                            botxbu-fail)
        alt-msg-eq
  where
    input : List Char
    input = emitMessage-chars msg ++ₗ outer

    pos-msg : Position
    pos-msg = advancePositions pos (emitMessage-chars msg)

    botxbu-fail : (parseBOTxBu >>= λ rms → pure (TSBOTxBu rms)) pos input ≡ nothing
    botxbu-fail = refl

    p-msg-eq : parseMessage pos input ≡ just (mkResult (clearBothMsg msg) pos-msg outer)
    p-msg-eq = parseMessage-roundtrip-bundled pos msg outer wf nl-stop

    alt-msg-eq : (parseMessage >>= λ m → pure (TSMessage m)) pos input
                 ≡ just (mkResult (TSMessage (clearBothMsg msg)) pos-msg outer)
    alt-msg-eq = bind-just-step parseMessage (λ m → pure (TSMessage m))
                   pos input (clearBothMsg msg) pos-msg outer p-msg-eq
