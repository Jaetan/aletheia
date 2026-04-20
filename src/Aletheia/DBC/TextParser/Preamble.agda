{-# OPTIONS --safe --without-K #-}

-- Preamble parsers for the DBC text format (Phase B.3.c.2).
--
-- Grammar slice covered (BNF section A from `Aletheia.DBC.TextParser`):
--   version      ::= "VERSION" ws string-lit newline
--   ns           ::= "NS_" ws? ":" newline (blank-line | indent keyword newline)*
--   bs           ::= "BS_" ws? ":" (ws baud-rate-expr)? newline
--
-- Section-parser composition: each parser below consumes its own trailing
-- blank lines via `many parseNewline`, so `parseVersion *> parseNamespace *>
-- parseBitTiming` composes without a separate inter-section blank-line
-- combinator.  Exposing each parser independently also keeps the B.3.d
-- roundtrip lemmas small — one lemma per section instead of one big
-- preamble lemma that would need to case-split on blank-line placement.
--
-- Discarded content: the `DBC` record (`Aletheia.DBC.Types`) has no NS_ or
-- BS_ fields (cantools discards them structurally too).  Both
-- `parseNamespace` and `parseBitTiming` return `⊤` — the text is consumed
-- for syntactic correctness but no structural payload is retained.  The
-- roundtrip target is at DBC *value* level (see TextFormatter.agda caveat),
-- so `formatText ∘ parseText` is free to canonicalise the NS_ keyword list
-- and baud-rate expression without breaking the equivalence.
--
-- NS_ body is open-ended: the corpus ranges from 2 keywords (env_vars.dbc)
-- to 25 keywords (minimal.dbc, kitchen_sink.dbc), and third-party tools may
-- add vendor extensions.  `parseNSLine` therefore accepts ANY identifier
-- rather than matching a fixed keyword whitelist.  Termination is via the
-- failure-to-consume condition: the loop stops when the next line is
-- neither blank nor indented (i.e. at the start of the BS_ section).
--
-- BS_ tail handling: the baud-rate expression is documented in the grammar
-- as `nat (":" nat "," nat)?`, but the corpus always leaves it empty.
-- Rather than structurally parse it (dead weight until a caller cares),
-- we consume every non-newline character and discard.  If a future phase
-- exposes bit-timing on `DBC`, reinstate a proper parser here.
module Aletheia.DBC.TextParser.Preamble where

open import Data.Bool using (not; _∨_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   satisfy; char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline)

-- ============================================================================
-- VERSION
-- ============================================================================

-- `"VERSION" ws string-lit newline` + any number of trailing blank lines.
parseVersion : Parser String
parseVersion = do
  _ ← string "VERSION"
  _ ← parseWS
  v ← parseStringLit
  _ ← parseNewline
  _ ← many parseNewline
  pure v

-- ============================================================================
-- NS_ (namespace / symbol set)
-- ============================================================================

-- One entry in the NS_ body: either a blank line or an indented keyword
-- line.  Ordering of the two alternatives matters — the blank-line branch
-- is tried first because it is a strict prefix of the indented-keyword
-- branch (both start with zero or more whitespace chars, but the keyword
-- branch *requires* at least one whitespace char via `parseWS`).  Put
-- differently: if we only have `"\n"` left, the keyword branch's
-- `parseWS` fails immediately, so reordering is safe — we simply fall
-- through to the blank-line branch.  Kept this order for readability.
parseNSLine : Parser ⊤
parseNSLine =
  (parseNewline *> pure tt) <|>
  (parseWS *> parseIdentifier *> parseWSOpt *> parseNewline *> pure tt)

-- `"NS_" ws? ":" newline body`.  The body is `(blank-line | indent kw nl)*`;
-- trailing blank lines are absorbed by the body's blank-line branch, so no
-- separate post-body `many parseNewline` is needed here.
parseNamespace : Parser ⊤
parseNamespace = do
  _ ← string "NS_"
  _ ← parseWSOpt
  _ ← char ':'
  _ ← parseNewline
  _ ← many parseNSLine
  pure tt

-- ============================================================================
-- BS_ (bit timing)
-- ============================================================================

-- `"BS_" ws? ":" <opaque tail> newline` + any trailing blank lines.  The
-- opaque tail is any run of non-newline characters; this covers both the
-- corpus-common empty form (`BS_:`) and the grammar's full `ws baud-rate`
-- form without committing to structural parse.
parseBitTiming : Parser ⊤
parseBitTiming = do
  _ ← string "BS_"
  _ ← parseWSOpt
  _ ← char ':'
  _ ← many (satisfy (λ c → not (⌊ c ≟ᶜ '\n' ⌋ ∨ ⌊ c ≟ᶜ '\r' ⌋)))
  _ ← parseNewline
  _ ← many parseNewline
  pure tt
