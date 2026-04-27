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
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.String using (String)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline;
   parseNatural)

open import Aletheia.DBC.Types using (SignalGroup)

-- ============================================================================
-- SIGNAL ENTRY PARSER
-- ============================================================================

-- One `ws identifier` pair.  Called under `many`, which terminates when
-- the next character is the `;` terminator (the mandatory leading
-- `parseWS` fails on `;`, so the repetition stops cleanly without a
-- separator combinator).  Mirrors `parseValueEntry` in
-- `TextParser.ValueTables`.
parseSigNameEntry : Parser Identifier
parseSigNameEntry = do
  _ ← parseWS
  parseIdentifier

-- ============================================================================
-- SIG_GROUP_ LINE
-- ============================================================================

-- `"SIG_GROUP_" ws nat ws identifier ws nat ws? ":" entries ws? ";" newline`
-- + optional trailing blank lines.  Both nats (CAN ID and repetitions)
-- are parsed then discarded — see module header.  `parseWSOpt` on either
-- side of `:` and `;` tolerates cantools' single-space emission as well
-- as tighter hand-written forms.
parseSignalGroup : Parser SignalGroup
parseSignalGroup = do
  _ ← string "SIG_GROUP_"
  _ ← parseWS
  _ ← parseNatural      -- message CAN ID, discarded
  _ ← parseWS
  name ← parseIdentifier
  _ ← parseWS
  _ ← parseNatural      -- repetitions, discarded
  _ ← parseWSOpt
  _ ← char ':'
  sigs ← many parseSigNameEntry
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (record { name = name ; signals = sigs })
