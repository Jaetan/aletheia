{-# OPTIONS --safe --no-main #-}

module Aletheia.Main where

open import Aletheia.Protocol.Command
open import Data.String using (String; _++_)
open import Data.List using (List)
open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing)

-- Simple string processing for now
processCommand : String → String
processCommand input = "Echo: " ++ input

-- TODO: Add proper command parsing in Phase 2
