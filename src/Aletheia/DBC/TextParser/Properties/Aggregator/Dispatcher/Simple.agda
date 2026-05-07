{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Façade re-exporting the 5 simple-section dispatchers
-- (+ Track E.5β TVD).  Per-section modules live under `Dispatcher/Simple/`
-- to keep each module's elaboration working set within `-M16G`.  The
-- dispatcher consumers (Aggregator.Properties / Aggregator.Universal)
-- import these names from this façade.
--
-- The TAT case (heaviest) lives in `Aggregator/Dispatcher/Attribute.agda`
-- — separate to isolate its ~600-1500 LOC dispatch tree.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple where

open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.ValueTable public using
  (parseTopStmt-on-emit-TVT-eq)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.Message public using
  (parseTopStmt-on-emit-TM-eq)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.SignalGroup public using
  (parseTopStmt-on-emit-TSG-eq)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.EnvVar public using
  (parseTopStmt-on-emit-TEV-eq)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.Comment public using
  (parseTopStmt-on-emit-TCM-eq)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.ValueDesc public using
  (parseTopStmt-on-emit-TVD-eq)
