-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A.2 — formatter-side `BO_TX_BU_` emitters (DSL-free, mirrors
-- `TextFormatter.ValueTables`'s VAL_ section emitters).
--
-- Standalone hand emitters (no `Format` DSL import) so `formatChars`'s
-- runtime / MAlonzo closure stays free of the parser-side DSL machinery.
-- The proof side bridges these to `emit MsgSenders-format` via
-- `emit-MsgSenders-format-eq-emitMsgSenders-line-chars` (the A.2 analogue of
-- `emit-ValueDescription-format-eq-emitValueDescription-chars`); the
-- comma-list tail uses `concatMap` so it matches `emit (many (withPrefix ","
-- ident))` definitionally (eta), keeping that bridge essentially `refl`.
--
-- `emitMsgSenders-line-chars` emits the `"BO_TX_BU_ "` prefix
-- UNCONDITIONALLY (like `emitValueDescription-chars`'s `"VAL_ "` prefix), so
-- it is `'B'`-headed and non-empty for ALL inputs — the uniform typed-shadow
-- lemmas (`emitTopStmt-chars-nonzero` / `-head-not-newline`) then need no
-- case-split.  Empty senders → `BO_TX_BU_ <id> : ;` is never produced by
-- `collectSenders` (it skips empty-sender messages) and never parsed; only
-- the non-empty form round-trips.
module Aletheia.DBC.TextFormatter.MessageSenders where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr; concatMap)
  renaming (_++_ to _++ₗ_)
open import Data.String using (toList)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.TextParser.Senders using (RawMsgSenders; collectSenders)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using (showℕ-dec-chars)

-- ============================================================================
-- COMMA-SEPARATED SENDER LIST
-- ============================================================================

-- `n1,n2,…,nk`.  Head emitted bare, each tail element comma-prefixed via
-- `concatMap` — matching `emit (many (withPrefix "," ident))` definitionally
-- (`emit (withPrefix "," ident) x = ',' ∷ name x`).  Empty list → `[]`.
emitSenderList-chars : List Identifier → List Char
emitSenderList-chars []      = []
emitSenderList-chars (h ∷ t) =
  Identifier.name h ++ₗ concatMap (λ x → ',' ∷ Identifier.name x) t

-- ============================================================================
-- PER-LINE EMITTER
-- ============================================================================

-- `BO_TX_BU_ <id> : n1,n2,…;` + `\n`.  Prefix is unconditional (see header).
emitMsgSenders-line-chars : RawMsgSenders → List Char
emitMsgSenders-line-chars rms =
  toList "BO_TX_BU_ " ++ₗ showℕ-dec-chars (rawCanIdℕ (RawMsgSenders.canId rms))
    ++ₗ toList " : " ++ₗ emitSenderList-chars (RawMsgSenders.senders rms)
    ++ₗ ' ' ∷ ';' ∷ '\n' ∷ []

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================
--
-- `emitMsgSenders-rmss-chars` operates on the `RawMsgSenders` list directly
-- (what the BodyBridge consumes after the per-section reduction);
-- `emitMessageSenders-chars` is the wrapper `formatChars` calls,
-- definitionally `emitMsgSenders-rmss-chars ∘ collectSenders`.

emitMsgSenders-rmss-chars : List RawMsgSenders → List Char
emitMsgSenders-rmss-chars =
  foldr (λ rms acc → emitMsgSenders-line-chars rms ++ₗ acc) []

emitMessageSenders-chars : List DBCMessage → List Char
emitMessageSenders-chars msgs =
  emitMsgSenders-rmss-chars (collectSenders msgs)
