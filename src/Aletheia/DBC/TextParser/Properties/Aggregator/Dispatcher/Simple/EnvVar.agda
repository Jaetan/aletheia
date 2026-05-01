{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TEV dispatcher under head-dispatched parseTopStmt.
--
-- `emitEnvVar-chars ev ++ outer` starts with 'E'∷'V', so parseTopStmt
-- reduces to its EV-bucket: `parseEnvVar >>= λ e → pure (TSEnvVar e)`.
-- No alt; the dispatcher just promotes `parseEnvVar-roundtrip` via
-- `bind-just-step`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.EnvVar where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure)

open import Aletheia.DBC.Types using (EnvironmentVar)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSEnvVar; parseTopStmt)
open import Aletheia.DBC.TextParser.EnvVars using
  (parseEnvVar)

open import Aletheia.DBC.TextFormatter.EnvVars using
  (emitEnvVar-chars)

open import Aletheia.DBC.TextParser.Properties.EnvVars using
  (parseEnvVar-roundtrip; EnvVarNameStop)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

parseTopStmt-on-emit-TEV-eq :
    ∀ (pos : Position) (ev : EnvironmentVar) (outer : List Char)
  → EnvVarNameStop ev
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitEnvVar-chars ev ++ₗ outer)
    ≡ just (mkResult (TSEnvVar ev)
                     (advancePositions pos (emitEnvVar-chars ev))
                     outer)
parseTopStmt-on-emit-TEV-eq pos ev outer name-stop nl-stop =
  bind-just-step parseEnvVar (λ e → pure (TSEnvVar e))
    pos input ev pos-ev outer p-ev-eq
  where
    input : List Char
    input = emitEnvVar-chars ev ++ₗ outer

    pos-ev : Position
    pos-ev = advancePositions pos (emitEnvVar-chars ev)

    p-ev-eq : parseEnvVar pos input ≡ just (mkResult ev pos-ev outer)
    p-ev-eq = parseEnvVar-roundtrip pos ev outer name-stop nl-stop
