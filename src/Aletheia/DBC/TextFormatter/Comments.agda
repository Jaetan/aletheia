{-# OPTIONS --safe --without-K #-}

-- Comment emitters for the DBC text format (Phase B.3.c.6).
--
-- Grammar slice emitted (mirrors `TextParser.Comments`):
--   comment        ::= "CM_" (ws comment-target)? ws string-lit
--                      ws? ";" newline
--   comment-target ::= "BU_" ws identifier
--                    | "BO_" ws nat
--                    | "SG_" ws nat ws identifier
--                    | "EV_" ws identifier
--
-- Canonical choices (cantools parity):
--   * Single space between every token.  The parser accepts runs of
--     whitespace (`parseWS = some (satisfy isHSpace)`), so the roundtrip
--     `parseText ∘ formatText ≡ id` (B.3.d) composes either way.
--   * Trailing `;\n` (no space before `;`) — matches cantools' CM_
--     convention, differs from the `BA_DEF_*` families which emit
--     ` ;\n` (space before `;`).
--   * `CTNetwork` comment emits neither a keyword nor a pre-string-lit
--     separator: `CM_ "text";\n`.  Every other `CommentTarget` emits
--     its DBC-standard keyword (BU_ / BO_ / SG_ / EV_) followed by a
--     single space and its identifier(s).
--
-- The five per-target cases are spelled out directly in `body` rather
-- than routing through a uniform target-only helper; the `CTNetwork`
-- case would need a "no trailing separator" special-case if we factored
-- target rendering out.  Mirrors the shape of
-- `TextFormatter.Attributes.emitAttrAssign`.
module Aletheia.DBC.TextFormatter.Comments where

open import Data.List using (List; []; _∷_; foldr)
open import Data.String using (String) renaming (_++_ to _++ₛ_)

open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment
  )
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec; quoteStringLit)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

-- ============================================================================
-- LINE EMITTER
-- ============================================================================

emitComment : DBCComment → String
emitComment c = body (DBCComment.target c)
  where
    quoted : String
    quoted = quoteStringLit (DBCComment.text c)
    body : CommentTarget → String
    body CTNetwork =
      "CM_ " ++ₛ quoted ++ₛ ";\n"
    body (CTNode n) =
      "CM_ BU_ " ++ₛ n ++ₛ " " ++ₛ quoted ++ₛ ";\n"
    body (CTMessage cid) =
      "CM_ BO_ " ++ₛ showℕ-dec (rawCanIdℕ cid) ++ₛ " " ++ₛ quoted ++ₛ ";\n"
    body (CTSignal cid s) =
      "CM_ SG_ " ++ₛ showℕ-dec (rawCanIdℕ cid) ++ₛ " " ++ₛ s ++ₛ " " ++ₛ
      quoted ++ₛ ";\n"
    body (CTEnvVar ev) =
      "CM_ EV_ " ++ₛ ev ++ₛ " " ++ₛ quoted ++ₛ ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more CM_ lines concatenated.  Empty list emits `""`, matching
-- cantools' behaviour on comment-free databases.  Blank-line separation
-- between this section and the next is the composer's responsibility,
-- not this emitter's.
emitComments : List DBCComment → String
emitComments = foldr (λ c acc → emitComment c ++ₛ acc) ""
