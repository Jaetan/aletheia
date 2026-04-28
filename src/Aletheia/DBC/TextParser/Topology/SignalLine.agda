{-# OPTIONS --safe --without-K #-}

-- Signal-line subset of `Aletheia.DBC.TextParser.Topology` (B.3.d ε.2).
--
-- Hosts everything Topology needs *except* the cycle-relevant primitives
-- which live in `Topology.Foundations` (CANID encoding + mux-marker
-- primitives).  Specifically:
--   * `parseBU` (BU_ section parser),
--   * `RawSignal` record + `parseSignalLine`,
--   * `parseReceiverList` (DSL-derived; the cantools `Vector__XXX`
--     placeholder strip is absorbed into the DSL iso `fwd =
--     mkCanonicalFromList`),
--   * mux resolution (`findMuxName`, `resolvePresence`, `buildSignal`,
--     `resolveSignalList`),
--   * `parseMessage`/`parseMessages` (BO_ block parser).
--
-- The grammar slice and design rationale that previously lived at the
-- top of `Topology.agda` apply here unchanged.  See
-- `Aletheia.DBC.TextParser.Topology` (the re-export facade) for the
-- header note kept under that name for backwards compatibility.
module Aletheia.DBC.TextParser.Topology.SignalLine where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using
  (CanonicalReceivers; mkCanonicalFromList)

open import Data.Bool using (Bool)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _%_)
open import Aletheia.DBC.DecRat using (DecRat)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; _*>_; _<$>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (MuxMarker; NotMux; IsMux; SelBy; BothMux;
   buildCANId; parseMuxMarker; parseByteOrderDigit; parseSignFlag)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.Receivers using (canonicalReceiversFmt)

open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When; Node; mkNode)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DLC using (DLC; bytesToValidDLC)
open import Aletheia.CAN.Endianness using
  (ByteOrder; convertStartBit)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Constants using
  (max-physical-bits)

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
-- SG_ RAW FIELDS (pre-mux-resolution)
-- ============================================================================

record RawSignal : Set where
  constructor mkRawSignal
  field
    name      : Identifier
    muxMarker : MuxMarker
    startBit  : ℕ
    bitLength : ℕ
    byteOrder : ByteOrder
    isSigned  : Bool
    factor    : DecRat
    offset    : DecRat
    minimum   : DecRat
    maximum   : DecRat
    unit      : List Char
    receivers : List Identifier

-- Comma-separated receiver list (grammar requires at least one).
-- Post-ε.3: derived from the Format DSL `canonicalReceiversFmt` so the
-- universal `roundtrip` theorem in `Format.agda` discharges the
-- parse-after-emit law without per-element induction.  The DSL's iso
-- `fwd = mkCanonicalFromList` absorbs the `Vector__XXX` strip into the
-- parse output; the outer `<$>` projects the canonical list field.
parseReceiverList : Parser (List Identifier)
parseReceiverList = CanonicalReceivers.list <$> parse canonicalReceiversFmt

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
                    receivers)

-- ============================================================================
-- MUX RESOLUTION + DBCSignal BUILDER
-- ============================================================================

-- Find the multiplexor master's name in a list of raw signals, if any.
findMuxName : List RawSignal → Maybe Identifier
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
resolvePresence : Maybe Identifier → MuxMarker → Maybe SignalPresence
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
buildSignal : (frameBytes : ℕ) → Maybe Identifier → RawSignal → Maybe DBCSignal
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
    ; receivers = mkCanonicalFromList (RawSignal.receivers raw)
    })

-- Resolve all signals in a BO_ block.  Fails (`nothing`) if any signal's
-- mux reference can't be resolved — that is the only failure mode, since
-- CAN ID + DLC are handled in `parseMessage` and the physical gate is
-- deferred.
resolveSignalList : (frameBytes : ℕ) → List RawSignal → Maybe (List DBCSignal)
resolveSignalList frameBytes raws = buildAll (findMuxName raws) raws
  where
    buildAll : Maybe Identifier → List RawSignal → Maybe (List DBCSignal)
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
    buildMessage : ℕ → Identifier → ℕ → Identifier → List RawSignal → Parser DBCMessage
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
