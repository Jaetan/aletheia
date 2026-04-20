{-# OPTIONS --safe --without-K #-}

-- Preamble emitters for the DBC text format (Phase B.3.c.2).
--
-- Grammar slice emitted (mirrors `TextParser.Preamble`):
--   version      ::= "VERSION" ws string-lit newline
--   ns           ::= "NS_" ws? ":" newline (blank-line | indent keyword newline)*
--   bs           ::= "BS_" ws? ":" (ws baud-rate-expr)? newline
--
-- Canonical emission policy: the parser discards NS_/BS_ content, so this
-- module picks one canonical form per section and emits it unconditionally.
-- Choices (all matching cantools' default output so diffs against cantools-
-- generated fixtures stay minimal):
--
--   * VERSION           — quoted via `quoteStringLit`; single trailing blank
--                         line before NS_.
--   * NS_               — 25-keyword block from `minimal.dbc` (the cantools
--                         default symbol set).  Tab-indented.  Emitted
--                         unconditionally; parser's `many parseNSLine` accepts
--                         any subset/superset, so the image of
--                         `emitNamespace` is always accepted.
--   * BS_               — empty body (`BS_:\n\n`); the corpus never carries a
--                         non-trivial baud-rate expression, and the parser's
--                         opaque-tail consumer accepts empty tails.
--
-- Each emitter ends with a trailing `"\n"` for the section newline plus one
-- more `"\n"` for the blank line before the next section.  Matches the
-- parser's per-section `many parseNewline` so composition is symmetric.
module Aletheia.DBC.TextFormatter.Preamble where

open import Data.String using (String) renaming (_++_ to _++ₛ_)

open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit)

-- ============================================================================
-- VERSION
-- ============================================================================

emitVersion : String → String
emitVersion v = "VERSION " ++ₛ quoteStringLit v ++ₛ "\n\n"

-- ============================================================================
-- NS_ (namespace / symbol set)
-- ============================================================================

-- Cantools-canonical 25-keyword NS_ block (matches the corpus `minimal.dbc`
-- lines 5–29 exactly).  Order follows the cantools emission order, which is
-- the de-facto standard third-party tools compare against.
emitNamespace : String
emitNamespace =
  "NS_ :\n" ++ₛ
  "\tNS_DESC_\n" ++ₛ
  "\tCM_\n" ++ₛ
  "\tBA_DEF_\n" ++ₛ
  "\tBA_\n" ++ₛ
  "\tVAL_\n" ++ₛ
  "\tCAT_DEF_\n" ++ₛ
  "\tCAT_\n" ++ₛ
  "\tFILTER\n" ++ₛ
  "\tBA_DEF_DEF_\n" ++ₛ
  "\tEV_DATA_\n" ++ₛ
  "\tENVVAR_DATA_\n" ++ₛ
  "\tSGTYPE_\n" ++ₛ
  "\tSGTYPE_VAL_\n" ++ₛ
  "\tBA_DEF_SGTYPE_\n" ++ₛ
  "\tBA_SGTYPE_\n" ++ₛ
  "\tSIG_TYPE_REF_\n" ++ₛ
  "\tVAL_TABLE_\n" ++ₛ
  "\tSIG_GROUP_\n" ++ₛ
  "\tSIG_VALTYPE_\n" ++ₛ
  "\tSIGTYPE_VALTYPE_\n" ++ₛ
  "\tBO_TX_BU_\n" ++ₛ
  "\tBA_DEF_REL_\n" ++ₛ
  "\tBA_REL_\n" ++ₛ
  "\tBA_SGTYPE_REL_\n" ++ₛ
  "\tSG_MUL_VAL_\n\n"

-- ============================================================================
-- BS_ (bit timing)
-- ============================================================================

-- Empty-body canonical form.  The corpus never carries a non-trivial
-- baud-rate expression; third-party tooling treats a present `BS_:` as the
-- presence marker regardless of tail content.
emitBitTiming : String
emitBitTiming = "BS_:\n\n"
