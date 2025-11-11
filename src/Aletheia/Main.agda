{-# OPTIONS --safe --no-main #-}

module Aletheia.Main where

open import Aletheia.Protocol.Command
open import Aletheia.Protocol.Response
open import Aletheia.Protocol.Handlers
open import Aletheia.Protocol.Parser
open import Aletheia.Parser.Combinators using (runParser)
open import Data.String using (String; toList)
open import Data.Maybe using (Maybe; just; nothing)

-- Main command dispatcher - delegates to handlers
{-# NOINLINE handleCommand #-}
handleCommand : Command → Response
handleCommand (Echo msg) = successResponse "Echo received" (EchoData msg)
handleCommand (ParseDBC yaml) = handleParseDBC yaml
handleCommand (ExtractSignal dbcYAML msgName sigName frameBytes) =
  handleExtractSignal dbcYAML msgName sigName frameBytes
handleCommand (InjectSignal dbcYAML msgName sigName value frameBytes) =
  handleInjectSignal dbcYAML msgName sigName value frameBytes

-- String-based interface with protocol parser
{-# NOINLINE processCommand #-}
processCommand : String → String
processCommand input = parseHelper (runParser parseCommand (toList input))
  where
    parseHelper : Maybe Command → String
    parseHelper nothing = formatResponse (errorResponse "Failed to parse command")
    parseHelper (just cmd) = formatResponse (handleCommand cmd)
