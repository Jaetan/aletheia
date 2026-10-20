-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every value batch extraction keeps fits the binary wire's rational slots.
--
-- Purpose: The proof-tree face of `Aletheia.CAN.Batch.WireFits`, whose
--   erased lemmas the extraction handler carries at run time; this module
--   re-exports them so the batch proof facade reaches them under the
--   Properties walk.
-- Key results: categorizeWith-values-fit, extractAllSignals-values-fit.
module Aletheia.CAN.Batch.Properties.WireFits where

open import Aletheia.CAN.Batch.WireFits public using
  ( Fits
  ; wireFits-components
  ; categorizeWith-values-fit
  ; combinePartitioned-All
  ; extractAllSignalsFromMessage-values-fit
  ; extractAllSignals-values-fit
  )
