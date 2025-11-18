{-# OPTIONS --safe --without-K #-}

module Aletheia.Trace.Parser where

open import Aletheia.Trace.CANTrace
open import Aletheia.Parser.Combinators
open import Data.List using (List)

-- ============================================================================
-- YAML TRACE PARSER (Phase 2B - Streaming)
-- ============================================================================

-- DEFERRED TO PHASE 2B: Streaming trace parser
--
-- For Phase 2A, we focus on the LTL core (syntax, semantics, checker).
-- The trace parser will be implemented in Phase 2B along with:
-- - Incremental parsing (memory-bounded)
-- - Streaming LTL checking
-- - Support for 1GB+ trace files
--
-- Phase 2A testing will use programmatically constructed traces
-- or simple hardcoded examples for validation.

-- TODO (Phase 2B): Implement YAML trace parser
-- Format:
-- - timestamp: 1000
--   id: 0x123
--   data: [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]

parseCANTrace : Parser (List TimedFrame)
parseCANTrace = fail  -- Placeholder for Phase 2B
