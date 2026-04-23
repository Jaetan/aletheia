{-# OPTIONS --safe --without-K #-}

-- Topology parsers for the DBC text format (Phase B.3.c.3).
--
-- Grammar slice covered (BNF section B from `Aletheia.DBC.TextParser`):
--   bu-section    ::= "BU_:" (ws identifier)* newline
--   message       ::= "BO_" ws nat ws identifier ws? ":" ws nat ws identifier
--                     newline signal*
--   signal        ::= " SG_" ws identifier mux-ind? ws? ":" ws? nat "|" nat
--                     "@" byte-order-digit sign ws? "(" rational "," rational
--                     ")" ws? "[" rational "|" rational "]" ws? string-lit
--                     ws? identifier ("," identifier)* newline
--   mux-ind       ::= ws "M" | ws "m" nat | ws "m" nat "M"
--
-- Two-stage design:
--   Stage 1 (`parseSignalLine` → `RawSignal`) — capture syntactic fields
--     including the raw mux marker (`M` / `m<N>` / `m<N>M`).  Cannot build a
--     `DBCSignal` yet because the `SignalPresence.When` constructor needs
--     the *name* of the parent master, which only becomes known after all
--     SG_ lines under a BO_ are collected.
--   Stage 2 (`resolveSignalList`) — scans the captured RawSignals for the
--     master via `findMuxName`, then rebuilds each one as `DBCSignal` with
--     the parent master's name wired into `When`.  A `SelBy`/`BothMux`
--     signal with no master found in the same BO_ block is an ill-formed
--     input and aborts the parse.
--
-- CANId encoding (cantools bit-31 flag convention): raw ≥ 2^31 decodes to
-- `Extended (raw − 2^31)`; raw < 2^31 decodes to `Standard raw` (must fit
-- in 11 bits).  Mirrored by `TextFormatter.Topology.rawCanIdℕ`.
--
-- Validation scope (B.3.c.3): range-checks on CAN ID, DLC byte count, and
-- mux reference resolution; the `physicalGate` predicate from
-- `JSONParser.parseSignalFields` is NOT applied at text-parse time — it is
-- a semantic-layer validator concern, and applying it here would couple
-- the parser to `ParseError` (out of scope for B.3.c.3, which stays on
-- `Maybe`-valued parsers throughout).
--
-- Deferred to later sub-commits:
--   * Multi-value mux selectors (`SG_MUL_VAL_`) — the syntactic drop
--     parser lands in B.3.c.8 (see `TextParser.ExtendedMux`); the
--     cross-line coordination that turns those parsed-and-dropped
--     ranges into actual multi-value `When` selectors is deferred to
--     a later mux-integration sub-commit.  Single-value `m<N>`
--     selectors map to a singleton `values = N List⁺.∷ []` today.
--   * BO_TX_BU_ `senders` — future sub-commit; for now `senders = []`.
--   * Integer-valued SG_ signals with `signalDef.startBit` physical-gate
--     rejection — leave to the validator per the scope note above.
module Aletheia.DBC.TextParser.Topology where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _%_; _^_; _<ᵇ_; _≤ᵇ_)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.DecRat using (DecRat)
open import Data.String using (String)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; _*>_;
   satisfy; char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)

open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When; Node; mkNode)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.DLC using (DLC; bytesToValidDLC)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; convertStartBit)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Constants using
  (standard-can-id-max; extended-can-id-max; max-physical-bits)
open import Aletheia.Prelude using (ifᵀ_then_else_)

-- ============================================================================
-- BU_ (NODES)
-- ============================================================================

-- `BU_:` + zero-or-more `ws identifier` + newline + trailing blanks.
-- `parseWS` before each identifier guarantees the single-space separator
-- required by the grammar; `parseWSOpt` at the end tolerates trailing
-- whitespace on the node line.
parseBU : Parser (List Node)
parseBU =
  string "BU_" *> parseWSOpt *> char ':' *>
  many (parseWS *> parseIdentifier) >>= λ names →
  parseWSOpt *> parseNewline *>
  many parseNewline *>
  pure (map mkNode names)

-- ============================================================================
-- CANID (text-level bit-31 flag encoding)
-- ============================================================================

-- `2 ^ 31` as a term to sidestep the stdlib `LiteralTooBig` bound.
extFlagBit : ℕ
extFlagBit = 2 ^ 31

-- Decode a raw BO_ ℕ into a CANId, ranged-checked.  Returns `nothing` when
-- the ID is out of range for its (inferred) category.
buildCANId : ℕ → Maybe CANId
buildCANId raw =
  ifᵀ extFlagBit ≤ᵇ raw
    then (λ _ →
      let n = raw ∸ extFlagBit
      in ifᵀ n <ᵇ extended-can-id-max
           then (λ pf → just (Extended n pf))
           else nothing)
    else (ifᵀ raw <ᵇ standard-can-id-max
            then (λ pf → just (Standard raw pf))
            else nothing)

-- ============================================================================
-- SG_ MUX INDICATOR (pre-resolution)
-- ============================================================================

-- Encodes the syntactic mux role before the master's name is known:
--   NotMux    — no marker; always-present signal, not the master.
--   IsMux     — `M`; this signal is the multiplexor master.
--   SelBy n   — `m<n>`; present when the master's value is n.
--   BothMux n — `m<n>M`; nested — both selected by an outer master AND
--               itself a multiplexor for inner signals.  The `n` is the
--               outer-master selector; the inner role is implicit.
data MuxMarker : Set where
  NotMux   : MuxMarker
  IsMux    : MuxMarker
  SelBy    : ℕ → MuxMarker
  BothMux  : ℕ → MuxMarker

-- Parse an optional mux indicator.  Enters via `parseWS` (one required
-- space after the signal name); if the next character isn't `M` or `m`,
-- the outer `<|>` restores state to the pre-`parseWS` position and the
-- caller's next `parseWSOpt` handles separator whitespace.
parseMuxMarker : Parser MuxMarker
parseMuxMarker =
  (parseWS *>
    ((char 'M' *> pure IsMux) <|>
     (char 'm' *> parseNatural >>= λ n →
       (char 'M' *> pure (BothMux n)) <|>
       pure (SelBy n))))
  <|> pure NotMux

parseByteOrderDigit : Parser ByteOrder
parseByteOrderDigit =
  (char '0' *> pure BigEndian) <|>
  (char '1' *> pure LittleEndian)

-- DBC historical encoding: `+` = unsigned, `-` = signed.  Note: the
-- DBCSignal field is `isSigned : Bool`, so `-` ⇒ true, `+` ⇒ false.
parseSignFlag : Parser Bool
parseSignFlag =
  (char '+' *> pure false) <|>
  (char '-' *> pure true)

-- ============================================================================
-- SG_ RAW FIELDS (pre-mux-resolution)
-- ============================================================================

record RawSignal : Set where
  constructor mkRawSignal
  field
    name      : String
    muxMarker : MuxMarker
    startBit  : ℕ
    bitLength : ℕ
    byteOrder : ByteOrder
    isSigned  : Bool
    factor    : DecRat
    offset    : DecRat
    minimum   : DecRat
    maximum   : DecRat
    unit      : String
    receivers : List String

-- Comma-separated receiver list (grammar requires at least one).
parseReceiverList : Parser (List String)
parseReceiverList = do
  h ← parseIdentifier
  t ← many (char ',' *> parseIdentifier)
  pure (h ∷ t)

-- Strip cantools' `Vector__XXX` no-named-receiver placeholder to `[]`,
-- matching the JSON path's canonical in-memory form.  Only applied when
-- it is the sole entry — a list like `Vector__XXX,NodeA` (which cantools
-- never emits but third-party tooling might) is preserved verbatim.
stripVectorPlaceholder : List String → List String
stripVectorPlaceholder ("Vector__XXX" ∷ []) = []
stripVectorPlaceholder rs                    = rs

-- Parse one SG_ line into a `RawSignal`.  Leading indent is `parseWSOpt`
-- (cantools emits one space; we tolerate any amount).  Mux resolution is
-- deferred to `resolveSignalList` — this parser records only the marker.
parseSignalLine : Parser RawSignal
parseSignalLine = do
  _ ← parseWSOpt
  _ ← string "SG_"
  _ ← parseWS
  name ← parseIdentifier
  mux  ← parseMuxMarker
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWSOpt
  startBit ← parseNatural
  _ ← char '|'
  bitLength ← parseNatural
  _ ← char '@'
  bo ← parseByteOrderDigit
  isSigned ← parseSignFlag
  _ ← parseWSOpt
  _ ← char '('
  factor ← parseDecRat
  _ ← char ','
  offset ← parseDecRat
  _ ← char ')'
  _ ← parseWSOpt
  _ ← char '['
  minimum ← parseDecRat
  _ ← char '|'
  maximum ← parseDecRat
  _ ← char ']'
  _ ← parseWSOpt
  unit ← parseStringLit
  _ ← parseWSOpt
  receivers ← parseReceiverList
  _ ← parseWSOpt
  _ ← parseNewline
  pure (mkRawSignal name mux startBit bitLength bo isSigned
                    factor offset minimum maximum unit
                    (stripVectorPlaceholder receivers))

-- ============================================================================
-- MUX RESOLUTION + DBCSignal BUILDER
-- ============================================================================

-- Find the multiplexor master's name in a list of raw signals, if any.
findMuxName : List RawSignal → Maybe String
findMuxName [] = nothing
findMuxName (s ∷ rest) with RawSignal.muxMarker s
... | IsMux       = just (RawSignal.name s)
... | BothMux _   = just (RawSignal.name s)
... | _           = findMuxName rest

-- Build a `SignalPresence` from a `MuxMarker` given the master's name
-- (may be `nothing` if no master exists in the enclosing BO_ block).
-- Single-value selectors only — `SG_MUL_VAL_` multi-value integration
-- is deferred to a later mux-integration sub-commit (the syntactic
-- drop parser for the line already landed in B.3.c.8; see
-- `TextParser.ExtendedMux`).  `SelBy`/`BothMux` with no master yields
-- `nothing` (the input is ill-formed — a mux-slave without a master in
-- the same message).
resolvePresence : Maybe String → MuxMarker → Maybe SignalPresence
resolvePresence _        NotMux      = just Always
resolvePresence _        IsMux       = just Always
resolvePresence (just m) (SelBy n)   = just (When m (n List⁺.∷ []))
resolvePresence (just m) (BothMux n) = just (When m (n List⁺.∷ []))
resolvePresence nothing  (SelBy _)   = nothing
resolvePresence nothing  (BothMux _) = nothing

-- Assemble a `DBCSignal` from a `RawSignal` + resolved presence.  Applies
-- the same `% max-physical-bits` clamps and `convertStartBit` call as
-- `JSONParser.parseSignalFields` so both paths produce the same internal
-- representation.  The BE physical gate (`bitLength ≥ 1`, signal-in-frame,
-- MSB-above-LSB) is skipped here; the validator catches gate violations.
buildSignal : (frameBytes : ℕ) → Maybe String → RawSignal → Maybe DBCSignal
buildSignal frameBytes master raw
  with resolvePresence master (RawSignal.muxMarker raw)
... | nothing = nothing
... | just presence =
  let bo  = RawSignal.byteOrder raw
      sb  = RawSignal.startBit  raw % max-physical-bits
      bl  = RawSignal.bitLength raw % (1 + max-physical-bits)
      csb = convertStartBit frameBytes bo sb bl
  in just (record
    { name      = RawSignal.name raw
    ; signalDef = record
        { startBit  = csb
        ; bitLength = bl
        ; isSigned  = RawSignal.isSigned raw
        ; factor    = RawSignal.factor raw
        ; offset    = RawSignal.offset raw
        ; minimum   = RawSignal.minimum raw
        ; maximum   = RawSignal.maximum raw
        }
    ; byteOrder = bo
    ; unit      = RawSignal.unit raw
    ; presence  = presence
    ; receivers = RawSignal.receivers raw
    })

-- Resolve all signals in a BO_ block.  Fails (`nothing`) if any signal's
-- mux reference can't be resolved — that is the only failure mode, since
-- CAN ID + DLC are handled in `parseMessage` and the physical gate is
-- deferred.
resolveSignalList : (frameBytes : ℕ) → List RawSignal → Maybe (List DBCSignal)
resolveSignalList frameBytes raws = buildAll (findMuxName raws) raws
  where
    buildAll : Maybe String → List RawSignal → Maybe (List DBCSignal)
    buildAll _ [] = just []
    buildAll m (r ∷ rest) with buildSignal frameBytes m r
    ... | nothing = nothing
    ... | just s  with buildAll m rest
    ...   | nothing  = nothing
    ...   | just ss  = just (s ∷ ss)

-- ============================================================================
-- BO_ BLOCK PARSER
-- ============================================================================

-- Parse a BO_ block: header + SG_ lines + trailing blanks.  Fails if:
--   * the CAN ID is out of range (`buildCANId` returns nothing),
--   * the DLC byte count doesn't map to a valid `DLC` (CAN-FD aware via
--     `bytesToValidDLC`),
--   * any SG_ line's mux reference can't be resolved.
-- On any of these the partial consumption is discarded by the outer
-- `<|>` / `many` — see the module header for the error-semantics note.
parseMessage : Parser DBCMessage
parseMessage = do
  _ ← string "BO_"
  _ ← parseWS
  rawId ← parseNatural
  _ ← parseWS
  msgName ← parseIdentifier
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseWS
  rawDlc ← parseNatural
  _ ← parseWS
  msgSender ← parseIdentifier
  _ ← parseWSOpt
  _ ← parseNewline
  raws ← many parseSignalLine
  _ ← many parseNewline
  buildMessage rawId msgName rawDlc msgSender raws
  where
    buildMessage : ℕ → String → ℕ → String → List RawSignal → Parser DBCMessage
    buildMessage rawId msgName rawDlc msgSender raws with buildCANId rawId
    ... | nothing = fail
    ... | just canId with bytesToValidDLC rawDlc
    ...   | nothing = fail
    ...   | just dlc with resolveSignalList rawDlc raws
    ...     | nothing = fail
    ...     | just sigs = pure (record
              { id      = canId
              ; name    = msgName
              ; dlc     = dlc
              ; sender  = msgSender
              ; senders = []
              ; signals = sigs
              })

-- Zero-or-more BO_ blocks.  Each `parseMessage` absorbs its own trailing
-- blanks; `many` composes without an inter-message combinator.
parseMessages : Parser (List DBCMessage)
parseMessages = many parseMessage
