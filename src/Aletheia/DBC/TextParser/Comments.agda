{-# OPTIONS --safe --without-K #-}

-- Comment parsers for the DBC text format (Phase B.3.c.6).
--
-- Grammar slice covered (BNF section E from `Aletheia.DBC.TextParser`):
--   comment        ::= "CM_" (ws comment-target)? ws string-lit
--                      ws? ";" newline
--   comment-target ::= "BU_" ws identifier
--                    | "BO_" ws nat
--                    | "SG_" ws nat ws identifier
--                    | "EV_" ws identifier
--
-- Trailing-ws convention: each `comment-target` branch consumes its own
-- trailing `parseWS` so the caller sees a uniform "target eats ws" rule,
-- matching `TextParser.Attributes`'s `parseStandardAttrTarget` /
-- `parseRelTarget`.  The target-absent branch contributes no trailing
-- whitespace — the single `parseWS` between `CM_` and the body absorbs
-- the one and only separator in that shape.
--
-- Dispatch ambiguity — target vs network-only:
--   `CM_ "text";`         — no target; string-lit directly after `CM_ ws`.
--   `CM_ BU_ node "t";`   — target present; keyword before string-lit.
--   The two shapes are distinguished by whether the post-`CM_ ws` cursor
--   points at a string-lit (`"`) or a target keyword (`B` / `S` / `E`).
--   The `parseCommentTarget <|> pure CTNetwork` fall-through in
--   `parseComment` encodes exactly this: try each target keyword first,
--   fall back to the no-target shape on total failure.  Backtracking `<|>`
--   restores the cursor to the post-`CM_ ws` position if a partial target
--   match (e.g. matched `BU_ ` but then the identifier slot held `"`)
--   gets rolled back.
--
-- CAN-ID handling: BO_ / SG_ target branches route the raw natural
-- through `buildCANId` (cantools bit-31 flag → Standard/Extended),
-- re-using the helper already in `TextParser.Topology` so CM_ and BA_
-- agree on the same convention.  Out-of-range IDs abort the parse via
-- `fail`.
module Aletheia.DBC.TextParser.Comments where

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_;
   char; string; many; fail)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.Topology using (buildCANId)

open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment; mkComment
  )

-- ============================================================================
-- CAN-ID-AWARE TARGET WRAPPERS
-- ============================================================================

-- Parallel to `TextParser.Attributes.wrapMsgTarget` / `wrapSigTarget`
-- but producing `CommentTarget` instead of `AttrTarget`.  Out-of-range
-- IDs abort the parse via `fail`.
wrapCTMessage : ℕ → Parser CommentTarget
wrapCTMessage r with buildCANId r
... | just cid = pure (CTMessage cid)
... | nothing  = fail

wrapCTSignal : ℕ → String → Parser CommentTarget
wrapCTSignal r sig with buildCANId r
... | just cid = pure (CTSignal cid sig)
... | nothing  = fail

-- ============================================================================
-- COMMENT TARGET LEXERS
-- ============================================================================

-- Each target branch consumes its trailing `parseWS` so the caller sees
-- a uniform "target eats ws" convention.  Matches `TextParser.Attributes`.
parseBUTgt : Parser CommentTarget
parseBUTgt = do
  _ ← string "BU_"
  _ ← parseWS
  n ← parseIdentifier
  _ ← parseWS
  pure (CTNode n)

parseBOTgt : Parser CommentTarget
parseBOTgt = do
  _ ← string "BO_"
  _ ← parseWS
  r ← parseNatural
  _ ← parseWS
  wrapCTMessage r

parseSGTgt : Parser CommentTarget
parseSGTgt = do
  _ ← string "SG_"
  _ ← parseWS
  r ← parseNatural
  _ ← parseWS
  sig ← parseIdentifier
  _ ← parseWS
  wrapCTSignal r sig

parseEVTgt : Parser CommentTarget
parseEVTgt = do
  _ ← string "EV_"
  _ ← parseWS
  n ← parseIdentifier
  _ ← parseWS
  pure (CTEnvVar n)

-- Longest-first dispatch not required here: all four keywords have
-- distinct first characters (B / S / E) that are never prefixes of each
-- other (BU_ vs BO_ diverge at position 1; SG_ and EV_ diverge at
-- position 0).  Ordering is alphabetical for review-diff friendliness.
parseCommentTarget : Parser CommentTarget
parseCommentTarget =
  parseBUTgt <|> parseBOTgt <|> parseSGTgt <|> parseEVTgt

-- ============================================================================
-- CM_ LINE
-- ============================================================================

-- `"CM_" (ws comment-target)? ws string-lit ws? ";" newline` with
-- trailing blank-line tolerance via `many parseNewline`.  Mirrors the
-- VAL_TABLE_ / BA_* trailing-newline stance — the emitter never produces
-- blank lines between CM_ entries, but the parser stays lenient for
-- hand-written corpora.
parseComment : Parser DBCComment
parseComment = do
  _ ← string "CM_"
  _ ← parseWS
  target ← parseCommentTarget <|> pure CTNetwork
  text ← parseStringLit
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkComment target text)
