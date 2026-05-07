{-# OPTIONS --safe --without-K #-}

-- Comment parsers for the DBC text format (Track B.3.c.6, migrated to
-- Format DSL in 3d.5.d).
--
-- Grammar slice (BNF section E from `Aletheia.DBC.TextParser`):
--   comment        ::= "CM_" ws (comment-target)? ws? string-lit
--                      ws? ";" newline
--   comment-target ::= "BU_" ws ident ws            (CTNode)
--                    | "BO_" ws nat   ws            (CTMessage; via buildCANId)
--                    | "SG_" ws nat   ws ident ws   (CTSignal;  via buildCANId)
--                    | "EV_" ws ident ws            (CTEnvVar)
--                    | (empty)                      (CTNetwork)
--
-- Migration shape (mirrors 3d.5.d EnvVar / BU_ / ValueTable):
--
--     parseComment = parse commentFmt >>= λ (rt , text , _) →
--                    many parseNewline >>= λ _ →
--                    buildCommentP rt text
--
-- where `commentFmt : Format (RawCommentTarget × List Char × ⊤)` (in
-- `Format.Comments`) covers the full `CM_` line including the line
-- terminator, and `buildCommentP` lifts the raw `RawCommentTarget`
-- (which carries raw ℕ for CAN-IDs) to the user-facing `CommentTarget`
-- via `buildCANId`, failing on out-of-range IDs.
--
-- Behavioural parity with the pre-3d.5.d hand-written parser: an
-- out-of-range CAN-ID inside a `CM_ BO_ <id> "text";` line caused the
-- old parser to backtrack via `<|>` (`parseBOTgt` failed at
-- `wrapCTMessage`, the `<|> pure CTNetwork` fell through, then
-- `parseStringLit` failed on the leftover `BO_` keyword) — net result:
-- whole `parseComment` fails.  Under the migrated parser, `commentFmt`
-- succeeds with `RawCTMsg <bad-id>`, then `buildCommentP` returns
-- `nothing` — same net result.
module Aletheia.DBC.TextParser.Comments where

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List using (List)
open import Data.Char using (Char)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; many; fail)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment; mkComment
  )

open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.Comments using
  (commentFmt; RawCommentTarget; RawCTNet; RawCTNode;
   RawCTMsg; RawCTSig; RawCTEnv)

-- ============================================================================
-- BUILD-COMMENT — lift raw target to CommentTarget via buildCANId
-- ============================================================================

-- `buildCommentP rt text` builds a `DBCComment` from the format-emitted
-- raw target plus the parsed text body.  For `RawCTMsg` / `RawCTSig`
-- (the CAN-ID-bearing arms), `buildCANId` must succeed on the raw ℕ;
-- if it returns `nothing` (out-of-range ID), the whole comment line
-- fails to parse — matching the pre-3d.5.d backtrack-then-fail behaviour.
buildCommentP : RawCommentTarget → List Char → Parser DBCComment
buildCommentP RawCTNet      text = pure (mkComment CTNetwork text)
buildCommentP (RawCTNode n) text = pure (mkComment (CTNode n) text)
buildCommentP (RawCTMsg r)  text with buildCANId r
... | just cid = pure (mkComment (CTMessage cid) text)
... | nothing  = fail
buildCommentP (RawCTSig r s) text with buildCANId r
... | just cid = pure (mkComment (CTSignal cid s) text)
... | nothing  = fail
buildCommentP (RawCTEnv ev) text = pure (mkComment (CTEnvVar ev) text)

-- ============================================================================
-- PARSE-COMMENT — η-style production migration
-- ============================================================================

-- Wrap shape: format consumes through the line terminator; `many
-- parseNewline` consumes additional blank lines after; buildCommentP
-- assembles the DBCComment with CAN-ID validation.
parseComment : Parser DBCComment
parseComment =
  parse commentFmt >>= λ result →
  many parseNewline >>= λ _ →
  buildCommentP (proj₁ result) (proj₁ (proj₂ result))
