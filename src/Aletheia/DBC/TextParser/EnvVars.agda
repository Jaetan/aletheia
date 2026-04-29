{-# OPTIONS --safe --without-K #-}

-- Environment-variable parser for the DBC text format.
--
-- B.3.d Layer 3 3d.5.d migration: the line-level `parseEnvVar` is now
-- expressed via the Format DSL.  `envVarFmt` (in
-- `Aletheia.DBC.TextParser.Format.EnvVar`) is the canonical specification
-- of the EV_ line including the mandatory line-terminating `\n`; the
-- production parser is the η-style wrap that consumes that line + any
-- trailing blank lines.
--
-- Pre-3d.5.d (B.3.d Commit 3b): hand-written 14-step bind chain through
-- ~30 parser primitives.
-- Post-3d.5.d: 3-line wrap, mirroring 3d.5.d's `parseValueTable`.
--
-- Grammar slice (BNF section G):
--   env-var ::= "EV_" ws identifier wsOpt ":" ws ("0"|"1"|"2") ws
--               "[" rational "|" rational "]" ws string-lit ws
--               rational ws nat ws identifier ws identifier wsOpt ";"
--               newline
--
-- See `Format.EnvVar` module header for cantools-source citations and
-- the synthesized drop-field design.
module Aletheia.DBC.TextParser.EnvVars where

open import Data.Unit using (⊤; tt)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; many)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)

open import Aletheia.DBC.Types using (EnvironmentVar)
open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.EnvVar using (envVarFmt)

-- ============================================================================
-- EV_ LINE — DSL-backed wrapper
-- ============================================================================

-- `parse envVarFmt` consumes the full line (every wire token + the
-- mandatory line-terminating `\n`); `many parseNewline` consumes any
-- additional blank-line padding (zero-or-more — production permissive).
-- Same wrap shape as 3d.5.d's `parseValueTable`.
parseEnvVar : Parser EnvironmentVar
parseEnvVar =
  parse envVarFmt >>= λ ev →
  many parseNewline >>= λ _ →
  pure ev
