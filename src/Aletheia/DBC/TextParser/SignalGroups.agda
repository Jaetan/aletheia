{-# OPTIONS --safe --without-K #-}

-- Signal-group parser for the DBC text format (Phase B.3.c.7).
--
-- Grammar slice covered (BNF section F from `Aletheia.DBC.TextParser`):
--   sig-group    ::= "SIG_GROUP_" ws nat ws identifier ws nat ws? ":"
--                    (ws identifier)* ws? ";" newline
--
-- Scope note — CAN ID and repetitions parsed but discarded:
--   The Agda `SignalGroup` record carries only `name` and `signals`; the
--   leading nat (owning message's CAN ID) and trailing nat (repetitions
--   count) are required by the grammar but dropped at the Agda boundary.
--   Matches the existing Python pipeline: cantools'
--   `signal_group_to_json` in `python/aletheia/dbc_converter.py` drops
--   `repetitions` (docstring: "repetitions is dropped — it is a DBC-text-
--   format concern with no verifier-side semantics") and flattens
--   `message.signal_groups` into a top-level list, absorbing the message-
--   ID association.  The nats are still parsed for syntactic correctness
--   so ill-formed `SIG_GROUP_` lines reject the whole file, and a future
--   extension that promotes these fields end-to-end can flip this parser
--   to return them without re-deriving the grammar.  Mirrors the
--   parse-and-drop convention of `VAL_` in `TextParser.ValueTables`.
--
-- Zero-signal handling: `SIG_GROUP_ 0 Empty 1 : ;` is syntactically
-- valid — the `many parseSigNameEntry` combinator accepts zero entries
-- (same shape as `VAL_TABLE_`'s zero-entry case).  Corpus-never-seen but
-- grammar-allowed; `emitSignalGroup` mirrors this on the output side so
-- B.3.d composes.
module Aletheia.DBC.TextParser.SignalGroups where

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; many)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.SignalGroup using (signalGroupFmt)

open import Aletheia.DBC.Types using (SignalGroup)

-- ============================================================================
-- SIG_GROUP_ LINE
-- ============================================================================

-- Post 3d.5.d-4a: derived from the Format DSL `signalGroupFmt`, so the
-- universal `roundtrip` theorem in `Format.agda` discharges the
-- parse-after-emit law via a single `EmitsOK` certificate (see
-- `Properties/SignalGroups/SignalGroup.parseSignalGroup-roundtrip`).
-- The DSL handles `"SIG_GROUP_" ws nat ws identifier ws nat ws? ":"
-- entries ws? ";" newline` (production-permissive whitespace via
-- `withWS`/`withWSCanonOne`/`withWSOpt`, both LF and CR-LF newline via
-- `newlineFmt`).  The trailing `many parseNewline` consumes optional
-- blank lines between groups, mirroring η's `parseSignalLine` vs
-- `parseMessage` split (line consumes one terminator, block-level
-- wrapper absorbs blanks).
parseSignalGroup : Parser SignalGroup
parseSignalGroup = do
  sg ← parse signalGroupFmt
  _ ← many parseNewline
  pure sg
