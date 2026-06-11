-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A.2 — DSL-side `MsgSenders-format` for BO_TX_BU_ lines.
--
-- Canonical-form Format DSL for the message-senders line:
--   "BO_TX_BU_" ws nat ws ":" ws identifier ("," identifier)* ws? ";" newline
--
-- Whitespace matches the codebase's other Format-DSL parsers (VAL_ /
-- receivers), NOT the looser `ws?`-everywhere informal grammar: `ws`
-- (mandatory, parser one-or-more) between tokens and around `:`; NO
-- whitespace after `,` (same as `Format.Receivers` — `Engine, Gateway`
-- is rejected); `ws?` (optional, parser zero-or-more) only before `;`
-- (`withWSCanonOne`, mirroring VAL_).  Canonical emit is `BO_TX_BU_ <id> :
-- n1,n2,… ;`.  This is stricter than the former drop-parser (which used
-- `parseWSOpt` in every slot); since that parser DROPPED senders, the
-- stricter capturing parser is the correct successor.
--
-- Mirrors `Format.ValueDescription.ValueDescription-format`: the carrier is
-- the RAW shape `ℕ × (Identifier × List Identifier)` (CAN ID before
-- `buildCANId` decoding, plus the non-empty sender list as a head + tail).
-- The slim `parseBOTxBu-roundtrip` (Properties side) layers
-- `buildCANId-rawCanIdℕ` on top to recover the `RawMsgSenders` (CANId) form,
-- exactly as `parseValueDescription-roundtrip` does for VAL_.
--
-- The sender list reuses the comma-list shape from
-- `Format.Receivers.canonicalReceiversFmt` — `pair ident (many (withPrefix
-- "," ident))` — but WITHOUT the `CanonicalReceivers` iso, because senders
-- round-trip AS-IS (no `Vector__XXX` singleton stripping).  The comma-list
-- EmitsOK helpers are local copies of the (private) ones in
-- `Format.Receivers.Roundtrip`, matching the codebase's accepted pattern of
-- per-site local copies of the `sameLengthᵇ`/comma helpers.
module Aletheia.DBC.TextParser.Format.MessageSenders where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Aletheia.Parser.Combinators
  using (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; []-stop; ∷-stop)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; pair; iso; many;
         altSum; ws; wsCanonOne; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany;
         []-fails; ∷-cons; roundtrip)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common
  using (showNat-chars-head-stop-isHSpace)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators + newline (mirror `Format.ValueDescription`)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Canonical single space, parser zero-or-more.  Canonical emit `' ' ∷ []`.
  -- Used before `;` to accept an optional pre-terminator space (mirrors
  -- `Format.ValueDescription`'s `withWSCanonOne (withPrefix ";" …)`).
  withWSCanonOne : ∀ {A} → Format A → Format A
  withWSCanonOne f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

  -- One-or-more comma-separated identifiers (head + tail).  No
  -- canonicalisation: the list round-trips verbatim.
  senderListFmt : Format (Identifier × List Identifier)
  senderListFmt = pair ident (many (withPrefix (',' ∷ []) ident))

-- ============================================================================
-- COMMA-LIST EmitsOK HELPERS (local copies of `Format.Receivers.Roundtrip`)
-- ============================================================================

private
  -- Combined inner-many stop: identifier-continuation OR the `,` separator.
  isSenderCont : Char → Bool
  isSenderCont c = isIdentCont c ∨ (c ≈ᵇ ',')

  ∨-elim-isIdentCont : ∀ (c : Char)
    → isSenderCont c ≡ false → isIdentCont c ≡ false
  ∨-elim-isIdentCont c eq with isIdentCont c | c ≈ᵇ ','
  ... | false | _ = refl
  ... | true  | _ = case eq of λ ()

  ∨-elim-comma : ∀ (c : Char)
    → isSenderCont c ≡ false → (c ≈ᵇ ',') ≡ false
  ∨-elim-comma c eq with isIdentCont c | c ≈ᵇ ','
  ... | false | false = refl
  ... | false | true  = case eq of λ ()
  ... | true  | _     = case eq of λ ()

  isSenderCont→isIdentCont : ∀ (suffix : List Char)
    → SuffixStops isSenderCont suffix → SuffixStops isIdentCont suffix
  isSenderCont→isIdentCont []      _          = []-stop
  isSenderCont→isIdentCont (c ∷ _) (∷-stop h) =
    ∷-stop (∨-elim-isIdentCont c h)

  parse-withPrefix-comma-fails : ∀ pos suffix
    → SuffixStops isSenderCont suffix
    → parse (withPrefix (',' ∷ []) ident) pos suffix ≡ nothing
  parse-withPrefix-comma-fails pos []      _          = refl
  parse-withPrefix-comma-fails pos (c ∷ _) (∷-stop ss)
    rewrite ∨-elim-comma c ss = refl

  build-tail-EmitsOKMany : ∀ (t : List Identifier) (suffix : List Char)
    → SuffixStops isSenderCont suffix
    → EmitsOKMany (withPrefix (',' ∷ []) ident) t suffix
  build-tail-EmitsOKMany [] suffix ss =
    []-fails (λ pos → parse-withPrefix-comma-fails pos suffix ss)
  build-tail-EmitsOKMany (s ∷ []) suffix ss =
    ∷-cons (tt , isSenderCont→isIdentCont suffix ss)
           (s≤s z≤n)
           (build-tail-EmitsOKMany [] suffix ss)
  build-tail-EmitsOKMany (s ∷ s' ∷ rest) suffix ss =
    ∷-cons (tt , ∷-stop refl)
           (s≤s z≤n)
           (build-tail-EmitsOKMany (s' ∷ rest) suffix ss)

  -- EmitsOK for the raw `senderListFmt` pair.  Head-ident stop case-splits
  -- on the tail (comma next → `∷-stop refl`; empty → borrow the suffix's
  -- SuffixStops), then the tail many is `build-tail-EmitsOKMany`.
  build-senderlist-emits-ok : ∀ (h : Identifier) (t : List Identifier)
                                (suffix : List Char)
    → SuffixStops isSenderCont suffix
    → EmitsOK senderListFmt (h , t) suffix
  build-senderlist-emits-ok h []         suffix ss =
    isSenderCont→isIdentCont suffix ss ,
    build-tail-EmitsOKMany [] suffix ss
  build-senderlist-emits-ok h (s ∷ rest) suffix ss =
    ∷-stop refl ,
    build-tail-EmitsOKMany (s ∷ rest) suffix ss

-- ============================================================================
-- DSL DEFINITION
-- ============================================================================

-- Carrier: raw triple `(rawId , senderHead , senderTail)` flattened to
-- `ℕ × (Identifier × List Identifier)`.  CAN-ID decoding (`buildCANId`)
-- happens OUTSIDE the DSL (it's partial); the slim layers it on top.
MsgSenders-format : Format (ℕ × (Identifier × List Identifier))
MsgSenders-format =
  iso (λ x → proj₁ x , proj₁ (proj₂ x))
      (λ x → proj₁ x , proj₂ x , tt)
      (λ _ → refl)
      (withPrefix (toList "BO_TX_BU_") (
        pair (withWS nat) (
          pair (withWS (withPrefix (':' ∷ []) (withWS senderListFmt)))
               (withWSCanonOne (withPrefix (';' ∷ []) newlineFmt)))))

-- ============================================================================
-- PER-LINE PRECONDITION
-- ============================================================================

-- The first sender `Identifier`'s head must be non-`isHSpace`, so the
-- `withWS senderListFmt` slot's `SuffixStops isHSpace (name ++ rest)`
-- obligation reduces to `∷-stop`.  Mirrors `RawValueDescNameStop`.
RawMsgSendersNameStop : Identifier → Set
RawMsgSendersNameStop h =
  Σ-syntax Char (λ c → Σ-syntax (List Char) (λ cs →
    (Identifier.name h ≡ c ∷ cs) × (isHSpace c ≡ false)))

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- `EmitsOK MsgSenders-format (rawId , h , t) outer` from the single domain
-- precondition `RawMsgSendersNameStop h`.  Reduces structurally through
-- `iso → withPrefix → pair → withWS nat → withWS(":")withWS → senderListFmt
-- → withPrefix ";" newlineFmt`.  Mirrors `Format.ValueDescription.build-
-- emits-ok-vd`.
build-emits-ok-mss : ∀ (rawId : ℕ) (h : Identifier) (t : List Identifier)
                       (outer : List Char)
  → RawMsgSendersNameStop h
  → EmitsOK MsgSenders-format (rawId , h , t) outer
build-emits-ok-mss rawId h t outer (c , cs , name-eq , c-non-hs) =
  -- "BO_TX_BU_" literal: vacuous (tt).
  tt ,
  -- (withWS nat rawId): ws head non-hspace via showNat; nat-digit slot
  -- head is the following ' ' (from the colon segment's leading withWS).
  ( showNat-chars-head-stop-isHSpace rawId _
  , ∷-stop refl ) ,
  -- (withWS (":" (withWS senderListFmt))) , then (";" newline):
  ( ( -- outer withWS: leading ' ' before ':' — head ':' non-hspace.
      ∷-stop refl
    , ( -- ":" literal: vacuous.
        tt
      , ( -- inner withWS: leading ' ' before the first sender — head is the
          -- first sender's name head (c), non-hspace by the precondition.
          subst (λ xs → SuffixStops isHSpace
                          ((xs ++ₗ emit (many (withPrefix (',' ∷ []) ident)) t)
                           ++ₗ emit (withWSCanonOne (withPrefix (';' ∷ []) newlineFmt)) tt ++ₗ outer))
                (sym name-eq)
                (∷-stop c-non-hs)
        , build-senderlist-emits-ok h t _ (∷-stop refl) ) ) )
  , -- (wsCanonOne (";" newlineFmt)): leading ws-slot head is ';' (non-hspace);
    -- literal ";" vacuous; newlineFmt = altSum (inj₂), so EmitsOK is
    -- `(tt , parse "\r\n" fails on "\n"…)`.
    ( ∷-stop refl , ( tt , ( tt , (λ pos → refl) ) ) ) )

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- Body is one `roundtrip` call + the EmitsOK construction.  Universal in
-- `(rawId , h , t)` and `outer`; the only domain precondition is
-- `RawMsgSendersNameStop h`.
parseMsgSenders-format-roundtrip :
    ∀ (pos : Position) (rawId : ℕ) (h : Identifier) (t : List Identifier)
      (outer : List Char)
  → RawMsgSendersNameStop h
  → parse MsgSenders-format pos
      (emit MsgSenders-format (rawId , h , t) ++ₗ outer)
    ≡ just (mkResult (rawId , h , t)
             (advancePositions pos (emit MsgSenders-format (rawId , h , t)))
             outer)
parseMsgSenders-format-roundtrip pos rawId h t outer nameStop =
  roundtrip MsgSenders-format pos (rawId , h , t) outer
    (build-emits-ok-mss rawId h t outer nameStop)
