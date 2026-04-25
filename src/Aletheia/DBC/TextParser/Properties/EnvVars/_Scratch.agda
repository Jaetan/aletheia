{-# OPTIONS --without-K #-}

-- Load-bearing reduction canary for the B.3.d Layer 3 `EV_` proof.
--
-- `EnvVar.parseEnvVar-roundtrip` discharges parser-side `Identifier`
-- equalities for the *synthesized* drop-field defaults (the wire grammar
-- demands 14 tokens; the Agda `EnvironmentVar` record carries 5).  In
-- particular, the formatter emits the placeholder identifiers
-- `DUMMY_NODE_VECTOR0` and `Vector__XXX` for `access_type` and
-- `access_node`; the proof needs to construct an `Identifier` with
-- `valid = tt` for each, which only typechecks if `validIdentifierᵇ`
-- reduces to `true` on these literal names.
--
-- If a stdlib `Data.Char.Base` regression breaks the closed-Char
-- classification reduction, this file fails to typecheck *before* the
-- EV_ roundtrip does, making the regression easy to localise.
module Aletheia.DBC.TextParser.Properties.EnvVars._Scratch where

open import Data.Bool using (T)
open import Data.String using (toList)
open import Data.Unit using (tt)

open import Aletheia.DBC.Identifier using (validIdentifierᵇ)

_test-DUMMY-NODE-VECTOR0 : T (validIdentifierᵇ (toList "DUMMY_NODE_VECTOR0"))
_test-DUMMY-NODE-VECTOR0 = tt

_test-Vector-XXX : T (validIdentifierᵇ (toList "Vector__XXX"))
_test-Vector-XXX = tt
