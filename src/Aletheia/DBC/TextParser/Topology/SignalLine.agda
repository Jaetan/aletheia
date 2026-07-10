-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal-line subset of `Aletheia.DBC.TextParser.Topology`.
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

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _%_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _*>_;
   many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseNewline)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (MuxMarker; NotMux; IsMux; SelBy; BothMux;
   buildCANId)
open import Aletheia.DBC.TextParser.Topology.Foundations public using
  (RawSignal; mkRawSignal)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.SignalLine using (signalLineFmt)
open import Aletheia.DBC.TextParser.Format.Message using (messageHeaderFmt)
open import Aletheia.DBC.TextParser.Format.Nodes using (nodeListFmt)

open import Aletheia.DBC.Types using
  (DBCMessage; DBCSignal; SignalPresence; Always; When; Node)
open import Aletheia.CAN.DLC using (bytesToValidDLC)
open import Aletheia.CAN.Endianness using
  (convertStartBit)
open import Aletheia.CAN.Constants using
  (max-physical-bits)

-- ============================================================================
-- BU_ (NODES)
-- ============================================================================

-- `BU_:` + zero-or-more ` <name>` entries + line terminator + trailing
-- blanks.  Derived from the Format DSL `nodeListFmt`, so
-- the universal `roundtrip` theorem in `Format.agda` discharges the
-- header-through-line-terminator parse-after-emit pass in one structural
-- sweep (see `Properties.Topology.Nodes`).  Production permissiveness
-- (zero-or-more whitespace at the formatter's `parseWSOpt` slots, both LF
-- and CR-LF newline) is preserved by the DSL's `wsOpt`/`newlineFmt`.
-- The trailing `many parseNewline` consumes the formatter's section-blank
-- `\n` plus any additional blank lines in the input — same pattern as
-- `parseValueTable` and `parseSignalLine`.
parseBU : Parser (List Node)
parseBU = parse nodeListFmt >>= λ ns →
  many parseNewline >>= λ _ →
  pure ns

-- ============================================================================
-- SG_ RAW FIELDS (pre-mux-resolution)
-- ============================================================================
--
-- `RawSignal` + `mkRawSignal` live in `Topology.Foundations` so the
-- Format DSL `signalLineFmt : Format RawSignal` (under
-- `Format.SignalLine`) can produce them without resurrecting the import
-- cycle.  Re-exported above for source-compatibility.

-- Parse one SG_ line into a `RawSignal`.  Derived from
-- the Format DSL `signalLineFmt`, so the universal `roundtrip` theorem
-- in `Format.agda` discharges the parse-after-emit law via a single
-- `EmitsOK` certificate (see `Format.SignalLine.Roundtrip`).  Production
-- permissiveness (zero-or-more whitespace at every formatter slot, both
-- LF and CR-LF newline) is preserved by the DSL's `wsOpt`/`wsCanonOne`
-- and `newlineFmt` (altSum over the two newline literals).  Mux
-- resolution is deferred to `resolveSignalList` — this parser only
-- records the marker.
parseSignalLine : Parser RawSignal
parseSignalLine = parse signalLineFmt

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
-- drop parser for the line already landed in `TextParser.ExtendedMux`).
-- `SelBy`/`BothMux` with no master yields
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
-- representation.
--
-- Bitlength=0 rejection (2026-05-15): both byte
-- orders require `bitLength ≥ 1` at parse time, matching the JSON path's
-- `physicalGate` LE branch.  Without this gate, the LE side of the text
-- parser would still accept zero-length signals and defer to the validator
-- — leaving the parse boundary asymmetric across byte orders.  Other BE
-- physical-gate constraints (signal-in-frame, MSB-above-LSB) remain
-- validator-side for the text path.
buildSignal : (frameBytes : ℕ) → Maybe Identifier → RawSignal → Maybe DBCSignal
buildSignal frameBytes master raw
  with resolvePresence master (RawSignal.muxMarker raw)
... | nothing = nothing
... | just presence =
  let bo  = RawSignal.byteOrder raw
      sb  = RawSignal.startBit  raw % max-physical-bits
      bl  = RawSignal.bitLength raw % (1 + max-physical-bits)
      csb = convertStartBit frameBytes bo sb bl
  in if 1 ≤ᵇ bl
       then just (record
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
         ; valueDescriptions = []  -- VAL_ entries are scattered across the file; the partition+refine pass at the top level fills this from RawValueDesc collection.  Empty default keeps `buildSignal` total when no VAL_ entries reference this signal.
         })
       else nothing

-- Resolve all signals in a BO_ block.  Fails (`nothing`) if any signal's
-- mux reference can't be resolved — that is the only failure mode, since
-- CAN ID + DLC are handled in `parseMessage` and the physical gate is
-- deferred.
--
-- Inner walker `buildAllRaw` exposed at top level so the `resolveSignalList
-- -roundtrip` proof can induct on it directly (`where`-bound names aren't
-- accessible from outside the surrounding definition).
buildAllRaw : (frameBytes : ℕ) → Maybe Identifier
            → List RawSignal → Maybe (List DBCSignal)
buildAllRaw _          _ [] = just []
buildAllRaw frameBytes m (r ∷ rest) with buildSignal frameBytes m r
... | nothing = nothing
... | just s  with buildAllRaw frameBytes m rest
...   | nothing  = nothing
...   | just ss  = just (s ∷ ss)

resolveSignalList : (frameBytes : ℕ) → List RawSignal → Maybe (List DBCSignal)
resolveSignalList frameBytes raws =
  buildAllRaw frameBytes (findMuxName raws) raws

-- ============================================================================
-- BO_ BLOCK PARSER
-- ============================================================================

-- Inner builder (top-level so the `parseMessage-roundtrip` proof can
-- reference it directly; was a `where`-bound helper of `parseMessage`).
buildMessage : ℕ → Identifier → ℕ → Identifier
             → List RawSignal → Parser DBCMessage
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

-- Parse a BO_ block: header + SG_ lines + trailing blanks.  Fails if:
--   * the CAN ID is out of range (`buildCANId` returns nothing),
--   * the DLC byte count doesn't map to a valid `DLC` (CAN-FD aware via
--     `bytesToValidDLC`),
--   * any SG_ line's mux reference can't be resolved.
-- On any of these the partial consumption is discarded by the outer
-- `<|>` / `many` — see the module header for the error-semantics note.
--
-- Header chunk derived from the Format DSL `messageHeaderFmt`,
-- so the universal `roundtrip` theorem in `Format.agda` discharges the
-- header parse-after-emit pass in one structural sweep (see
-- `Properties.Topology.Message`).  Production permissiveness (zero-or-more
-- whitespace at the formatter's `parseWSOpt` slots, both LF and CR-LF
-- newline) is preserved by the DSL's `wsOpt`/`ws`/`newlineFmt`.
parseMessage : Parser DBCMessage
parseMessage = parse messageHeaderFmt >>= λ hdr →
  let rawId     = proj₁ hdr
      msgName   = proj₁ (proj₂ hdr)
      rawDlc    = proj₁ (proj₂ (proj₂ hdr))
      msgSender = proj₂ (proj₂ (proj₂ hdr))
  in many parseSignalLine >>= λ raws →
     many parseNewline *>
     buildMessage rawId msgName rawDlc msgSender raws

-- Zero-or-more BO_ blocks.  Each `parseMessage` absorbs its own trailing
-- blanks; `many` composes without an inter-message combinator.
parseMessages : Parser (List DBCMessage)
parseMessages = many parseMessage
