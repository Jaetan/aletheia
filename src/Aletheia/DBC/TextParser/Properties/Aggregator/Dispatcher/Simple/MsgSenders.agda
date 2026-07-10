-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- BO_TX_BU_ dispatcher slim + section well-formedness.
--
-- Mirrors the VAL_ chain (`Properties.ValueTables.ValueDesc` +
-- `Dispatcher.Simple.ValueDesc`), adapted to message senders:
--
--   1. `emit-MsgSenders-format-eq-emitMsgSenders-line-chars` — bridges the
--      DSL emit (over the raw `(ℕ , Identifier , List Identifier)` carrier)
--      to the hand emitter.  Essentially `refl`: the literals collapse
--      right-associatively and the comma-list tail is `concatMap`-shaped on
--      both sides (`emit (many (withPrefix "," ident)) ≡ λ t → concatMap …`
--      by eta).
--   2. `parseBOTxBu-roundtrip` — the buildCANId-layering slim (mirrors
--      `parseValueDescription-roundtrip`): the DSL roundtrip + trailing
--      `many parseNewline` + `buildCANId-rawCanIdℕ` inverse witness.
--   3. `parseTopStmt-on-emit-TBO-eq` — the dispatcher slim: at a 'B'∷'O'
--      head, `parseTopStmt` reduces to its BO bucket and the LEFT arm
--      (parseBOTxBu) SUCCEEDS, so `alt-left-just` closes it.
--   4. `RawMsgSendersStop` / `collectSenders-stops` — the per-line / section
--      precondition (first sender's name head non-isHSpace, list non-empty)
--      derived from sender `Identifier` validity, exactly as
--      `collectFromMessages-stops` does for VAL_.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.MsgSenders where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePositions; _>>=_; pure; many)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)

open import Aletheia.DBC.TextParser.Senders using
  (RawMsgSenders; mkRawMsgSenders; collectSenders; prependSenders)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSBOTxBu; TSMessage; parseTopStmt; parseBOTxBu; buildSendersResult)
open import Aletheia.DBC.TextParser.Topology using (parseMessage)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)
open import Aletheia.DBC.TextFormatter.MessageSenders using (emitMsgSenders-line-chars)

open import Aletheia.DBC.TextParser.Format using (emit; parse)
open import Aletheia.DBC.TextParser.Format.MessageSenders as FmtMS using
  (MsgSenders-format; RawMsgSendersNameStop)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  (buildCANId-rawCanIdℕ)
open import Aletheia.DBC.TextParser.Properties.Primitives using (alt-left-just)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (identifier-name-stop)

-- ============================================================================
-- PER-LINE / SECTION PRECONDITION
-- ============================================================================

-- The senders list is non-empty (`h ∷ t`) and the first sender's name head
-- is non-`isHSpace`.  `collectSenders` only emits non-empty entries, so this
-- holds for every collected line (see `collectSenders-stops`).
RawMsgSendersStop : RawMsgSenders → Set
RawMsgSendersStop rms =
  Σ-syntax Identifier (λ h → Σ-syntax (List Identifier) (λ t →
    (RawMsgSenders.senders rms ≡ h ∷ t) × RawMsgSendersNameStop h))

-- ============================================================================
-- BRIDGE — DSL emit ≡ hand emitMsgSenders-line-chars (non-empty form)
-- ============================================================================

emit-MsgSenders-format-eq-emitMsgSenders-line-chars :
    ∀ (cid : CANId) (h : Identifier) (t : List Identifier)
  → emit MsgSenders-format (rawCanIdℕ cid , h , t)
    ≡ emitMsgSenders-line-chars (mkRawMsgSenders cid (h ∷ t))
emit-MsgSenders-format-eq-emitMsgSenders-line-chars cid h t = refl

-- ============================================================================
-- SLIM `parseBOTxBu-roundtrip` (buildCANId layering)
-- ============================================================================

-- Explicit `(cid , h , t)` form — NO `rewrite`.  `senders (mkRawMsgSenders
-- cid (h ∷ t)) = h ∷ t` definitionally, so the body is the VAL_-shaped proof
-- verbatim.  Crucially, this avoids abstracting the goal over a stuck
-- `parseBOTxBu pos (… symbolic cid …)` term: `rewrite`/`subst` over such a
-- goal weak-head-normalises it (runs the parser on the stuck CAN-id digits →
-- 16 GB blowup).  The generic wrapper bridges `rms` in via `cong` only.
parseBOTxBu-roundtrip-explicit :
    ∀ (pos : Position) (cid : CANId) (h : Identifier) (t : List Identifier)
      (suffix : List Char)
  → RawMsgSendersNameStop h
  → SuffixStops isNewlineStart suffix
  → proj₂ (parseBOTxBu pos (emitMsgSenders-line-chars (mkRawMsgSenders cid (h ∷ t)) ++ₗ suffix))
    ≡ just (mkResult (mkRawMsgSenders cid (h ∷ t))
             (advancePositions pos (emitMsgSenders-line-chars (mkRawMsgSenders cid (h ∷ t))))
             suffix)
parseBOTxBu-roundtrip-explicit pos cid h t suffix nameStop nl-stop =
  trans (cong (λ inp → proj₂ (parseBOTxBu pos (inp ++ₗ suffix))) (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-buildResult))
  where
    triple : ℕ × (Identifier × List Identifier)
    triple = (rawCanIdℕ cid , h , t)

    bridge : emit MsgSenders-format triple
             ≡ emitMsgSenders-line-chars (mkRawMsgSenders cid (h ∷ t))
    bridge = emit-MsgSenders-format-eq-emitMsgSenders-line-chars cid h t

    pos-line : Position
    pos-line = advancePositions pos (emit MsgSenders-format triple)

    cont-line : (ℕ × (Identifier × List Identifier)) → Parser RawMsgSenders
    cont-line tr =
      many parseNewline >>= λ _ →
      buildSendersResult (buildCANId (proj₁ tr))
                         (proj₁ (proj₂ tr) ∷ proj₂ (proj₂ tr))

    step-format :
        proj₂ (parseBOTxBu pos (emit MsgSenders-format triple ++ₗ suffix))
      ≡ proj₂ (cont-line triple pos-line suffix)
    step-format =
      bind-just-step (parse MsgSenders-format)
                     cont-line
                     pos (emit MsgSenders-format triple ++ₗ suffix)
                     triple pos-line suffix
                     (FmtMS.parseMsgSenders-format-roundtrip
                       pos (rawCanIdℕ cid) h t suffix nameStop)

    cont-blanks : List Char → Parser RawMsgSenders
    cont-blanks _ =
      buildSendersResult (buildCANId (proj₁ triple))
                         (proj₁ (proj₂ triple) ∷ proj₂ (proj₂ triple))

    step-many-newline :
        proj₂ (cont-line triple pos-line suffix)
      ≡ proj₂ (cont-blanks [] pos-line suffix)
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (length suffix) nl-stop)

    step-buildResult :
        proj₂ (cont-blanks [] pos-line suffix)
      ≡ just (mkResult (mkRawMsgSenders cid (h ∷ t))
               (advancePositions pos
                 (emitMsgSenders-line-chars (mkRawMsgSenders cid (h ∷ t))))
               suffix)
    step-buildResult =
      trans
        (cong (λ m → proj₂ (buildSendersResult m (h ∷ t) pos-line suffix))
              (buildCANId-rawCanIdℕ cid))
        (cong (λ p → just (mkResult (mkRawMsgSenders cid (h ∷ t)) p suffix))
              (cong (advancePositions pos) bridge))

-- Generic wrapper — bridge `rms ↔ mkRawMsgSenders (canId rms) (h ∷ t)` via
-- `cong` (NOT `rewrite`/`subst`): congruence forms `f rms ≡ f (mkRawMsgSenders
-- …)` syntactically, so Agda never normalises (runs) the `parseBOTxBu`
-- application inside `f`.  `rms-eq` closes by record-η on `RawMsgSenders`.
parseBOTxBu-roundtrip :
    ∀ (pos : Position) (rms : RawMsgSenders) (suffix : List Char)
  → RawMsgSendersStop rms
  → SuffixStops isNewlineStart suffix
  → proj₂ (parseBOTxBu pos (emitMsgSenders-line-chars rms ++ₗ suffix))
    ≡ just (mkResult rms
             (advancePositions pos (emitMsgSenders-line-chars rms))
             suffix)
parseBOTxBu-roundtrip pos rms suffix (h , t , snds-eq , nameStop) nl-stop =
  trans (cong (λ r → proj₂ (parseBOTxBu pos (emitMsgSenders-line-chars r ++ₗ suffix))) rms-eq)
    (trans (parseBOTxBu-roundtrip-explicit pos (RawMsgSenders.canId rms) h t suffix nameStop nl-stop)
           (sym (cong (λ r → just (mkResult r
                       (advancePositions pos (emitMsgSenders-line-chars r)) suffix)) rms-eq)))
  where
    rms-eq : rms ≡ mkRawMsgSenders (RawMsgSenders.canId rms) (h ∷ t)
    rms-eq = cong (mkRawMsgSenders (RawMsgSenders.canId rms)) snds-eq

-- ============================================================================
-- DISPATCHER SLIM — parseTopStmt on a BO_TX_BU_ line
-- ============================================================================

parseTopStmt-on-emit-TBO-eq :
    ∀ (pos : Position) (rms : RawMsgSenders) (outer : List Char)
  → RawMsgSendersStop rms
  → SuffixStops isNewlineStart outer
  → proj₂ (parseTopStmt pos (emitMsgSenders-line-chars rms ++ₗ outer))
    ≡ just (mkResult (TSBOTxBu rms)
                     (advancePositions pos (emitMsgSenders-line-chars rms))
                     outer)
parseTopStmt-on-emit-TBO-eq pos rms outer stop nl-stop =
  alt-left-just (parseBOTxBu  >>= λ r → pure (TSBOTxBu r))
                (parseMessage >>= λ m → pure (TSMessage m))
                pos input
                (mkResult (TSBOTxBu rms) pos-bo outer)
                left-success
  where
    input : List Char
    input = emitMsgSenders-line-chars rms ++ₗ outer

    pos-bo : Position
    pos-bo = advancePositions pos (emitMsgSenders-line-chars rms)

    left-success :
        proj₂ ((parseBOTxBu >>= λ r → pure (TSBOTxBu r)) pos input)
      ≡ just (mkResult (TSBOTxBu rms) pos-bo outer)
    left-success =
      bind-just-step parseBOTxBu (λ r → pure (TSBOTxBu r))
                     pos input rms pos-bo outer
                     (parseBOTxBu-roundtrip pos rms outer stop nl-stop)

-- ============================================================================
-- SECTION WELL-FORMEDNESS — All RawMsgSendersStop (collectSenders msgs)
-- ============================================================================

prependSenders-stops :
    ∀ (cid : CANId) (snds : List Identifier) (rest : List RawMsgSenders)
  → All RawMsgSendersStop rest
  → All RawMsgSendersStop (prependSenders cid snds rest)
prependSenders-stops _   []       _    acc = acc
prependSenders-stops _   (x ∷ xs) _    acc =
  (x , xs , refl , identifier-name-stop x) ∷ acc

collectSenders-stops :
    ∀ (msgs : List DBCMessage)
  → All RawMsgSendersStop (collectSenders msgs)
collectSenders-stops []       = []
collectSenders-stops (m ∷ ms) =
  prependSenders-stops (DBCMessage.id m) (DBCMessage.senders m)
    (collectSenders ms) (collectSenders-stops ms)
