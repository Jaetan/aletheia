{-# OPTIONS --safe --no-main --guardedness #-}

module Aletheia.Main where

open import Aletheia.Protocol.Command
open import Aletheia.Protocol.Response
open import Aletheia.Protocol.Handlers
open import Aletheia.Protocol.Parser
open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.DebugDBC using (debugBoth)
open import Data.String using (String; toList)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (proj₁)

-- Main command dispatcher - delegates to handlers
{-# NOINLINE handleCommand #-}
handleCommand : Command → Response
handleCommand (Echo msg) = successResponse "Echo received" (EchoData msg)
handleCommand (ParseDBC yaml) = handleParseDBC yaml
handleCommand (ExtractSignal dbcYAML msgName sigName frameBytes) =
  handleExtractSignal dbcYAML msgName sigName frameBytes
handleCommand (InjectSignal dbcYAML msgName sigName value frameBytes) =
  handleInjectSignal dbcYAML msgName sigName value frameBytes
handleCommand (CheckLTL dbcYAML traceYAML propertyYAML) =
  handleCheckLTL dbcYAML traceYAML propertyYAML

-- String-based interface with protocol parser
{-# NOINLINE processCommand #-}
processCommand : String → String
processCommand input = parseHelper (map proj₁ (runParser parseCommand (toList input)))
  where
    parseHelper : Maybe Command → String
    parseHelper nothing = formatResponse (errorResponse "Failed to parse command")
    parseHelper (just cmd) = formatResponse (handleCommand cmd)

-- Debug function for parser tracing
{-# NOINLINE runDebug #-}
runDebug : String
runDebug = debugBoth
