{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4a — `SIG_GROUP_` section facade.
--
-- Mirrors `Properties/Comments`, `Properties/EnvVars`,
-- `Properties/ValueTables`: re-exports the per-construct slim
-- (`Properties/SignalGroups/SignalGroup.agda`) so the top-level
-- `Properties.agda` can pull a single import per section.
module Aletheia.DBC.TextParser.Properties.SignalGroups where

open import Aletheia.DBC.TextParser.Properties.SignalGroups.SignalGroup public
  using (parseSignalGroup-roundtrip; SignalGroupNameStop; SigNameStop)
