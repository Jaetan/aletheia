{-# OPTIONS --safe --no-main #-}

module Aletheia.Main where

open import Aletheia.Protocol.Command
open import Aletheia.Protocol.Response
open import Aletheia.Protocol.Handlers
open import Data.String using (String)

-- Main command dispatcher - delegates to handlers
{-# NOINLINE handleCommand #-}
handleCommand : Command → Response
handleCommand (Echo msg) = successResponse "Echo received" (EchoData msg)
handleCommand (ParseDBC yaml) = handleParseDBC yaml
handleCommand (ExtractSignal dbcYAML msgName sigName frameBytes) =
  handleExtractSignal dbcYAML msgName sigName frameBytes
handleCommand (InjectSignal dbcYAML msgName sigName value frameBytes) =
  handleInjectSignal dbcYAML msgName sigName value frameBytes

-- Legacy string-based interface for backward compatibility
{-# NOINLINE processCommand #-}
processCommand : String → String
processCommand input = formatResponse (handleCommand (Echo input))
