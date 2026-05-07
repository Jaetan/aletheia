{-# OPTIONS --safe --without-K #-}

-- Preamble emitters for the DBC text format (Track B.3.c.2; layer-1 form
-- 2026-04-24).
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
--   * VERSION           — quoted via `quoteStringLit-chars`; single trailing
--                         blank line before NS_.
--   * NS_               — 25-keyword block from `minimal.dbc` (the cantools
--                         default symbol set).  Tab-indented.  Emitted
--                         unconditionally; parser's `many parseNSLine` accepts
--                         any subset/superset, so the image of
--                         `emitNamespace-chars` is always accepted.
--   * BS_               — empty body (`BS_:\n\n`); the corpus never carries a
--                         non-trivial baud-rate expression, and the parser's
--                         opaque-tail consumer accepts empty tails.
--
-- Each emitter ends with a trailing `'\n'` for the section newline plus one
-- more `'\n'` for the blank line before the next section.  Matches the
-- parser's per-section `many parseNewline` so composition is symmetric.
--
-- All emitters are `List Char`-valued — the substrate the per-primitive
-- roundtrip proofs in B.3.d layer 2 reason about (see
-- `Aletheia.DBC.TextFormatter.Emitter` module header for the
-- layer-1 layout decision).
module Aletheia.DBC.TextFormatter.Preamble where

open import Data.Char using (Char)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.String using (String; toList)

open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit-chars)

-- ============================================================================
-- VERSION
-- ============================================================================

-- Post-3d.4 + JSON-mirror: `quoteStringLit-chars : List Char → List Char`
-- and `DBC.version : List Char`, so the emitter takes raw chars.
emitVersion-chars : List Char → List Char
emitVersion-chars v =
  toList "VERSION " ++ₗ quoteStringLit-chars v ++ₗ toList "\n\n"

-- ============================================================================
-- NS_ (namespace / symbol set)
-- ============================================================================

-- Cantools-canonical 25-keyword NS_ block (matches the corpus `minimal.dbc`
-- lines 5–29 exactly).  Order follows the cantools emission order, which is
-- the de-facto standard third-party tools compare against.
emitNamespace-chars : List Char
emitNamespace-chars =
  toList "NS_ :\n" ++ₗ
  toList "\tNS_DESC_\n" ++ₗ
  toList "\tCM_\n" ++ₗ
  toList "\tBA_DEF_\n" ++ₗ
  toList "\tBA_\n" ++ₗ
  toList "\tVAL_\n" ++ₗ
  toList "\tCAT_DEF_\n" ++ₗ
  toList "\tCAT_\n" ++ₗ
  toList "\tFILTER\n" ++ₗ
  toList "\tBA_DEF_DEF_\n" ++ₗ
  toList "\tEV_DATA_\n" ++ₗ
  toList "\tENVVAR_DATA_\n" ++ₗ
  toList "\tSGTYPE_\n" ++ₗ
  toList "\tSGTYPE_VAL_\n" ++ₗ
  toList "\tBA_DEF_SGTYPE_\n" ++ₗ
  toList "\tBA_SGTYPE_\n" ++ₗ
  toList "\tSIG_TYPE_REF_\n" ++ₗ
  toList "\tVAL_TABLE_\n" ++ₗ
  toList "\tSIG_GROUP_\n" ++ₗ
  toList "\tSIG_VALTYPE_\n" ++ₗ
  toList "\tSIGTYPE_VALTYPE_\n" ++ₗ
  toList "\tBO_TX_BU_\n" ++ₗ
  toList "\tBA_DEF_REL_\n" ++ₗ
  toList "\tBA_REL_\n" ++ₗ
  toList "\tBA_SGTYPE_REL_\n" ++ₗ
  toList "\tSG_MUL_VAL_\n\n"

-- ============================================================================
-- BS_ (bit timing)
-- ============================================================================

-- Empty-body canonical form.  The corpus never carries a non-trivial
-- baud-rate expression; third-party tooling treats a present `BS_:` as the
-- presence marker regardless of tail content.
emitBitTiming-chars : List Char
emitBitTiming-chars = toList "BS_:\n\n"
