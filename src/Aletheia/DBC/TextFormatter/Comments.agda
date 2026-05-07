{-# OPTIONS --safe --without-K #-}

-- Comment emitters for the DBC text format (Track B.3.c.6; layer-1 form
-- 2026-04-24).
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
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.Comments where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.String using (String; toList)

open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment
  )
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

-- ============================================================================
-- LINE EMITTER
-- ============================================================================

emitComment-chars : DBCComment → List Char
emitComment-chars c = body (DBCComment.target c)
  where
    quoted : List Char
    quoted = quoteStringLit-chars (DBCComment.text c)
    body : CommentTarget → List Char
    body CTNetwork =
      toList "CM_ " ++ₗ quoted ++ₗ toList ";\n"
    body (CTNode n) =
      toList "CM_ BU_ " ++ₗ Identifier.name n ++ₗ ' ' ∷ quoted ++ₗ toList ";\n"
    body (CTMessage cid) =
      toList "CM_ BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ quoted ++ₗ toList ";\n"
    body (CTSignal cid s) =
      toList "CM_ SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ Identifier.name s ++ₗ ' ' ∷ quoted ++ₗ toList ";\n"
    body (CTEnvVar ev) =
      toList "CM_ EV_ " ++ₗ Identifier.name ev ++ₗ ' ' ∷ quoted ++ₗ toList ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more CM_ lines concatenated.  Empty list emits `[]`, matching
-- cantools' behaviour on comment-free databases.  Blank-line separation
-- between this section and the next is the composer's responsibility.
emitComments-chars : List DBCComment → List Char
emitComments-chars =
  foldr (λ c acc → emitComment-chars c ++ₗ acc) []
