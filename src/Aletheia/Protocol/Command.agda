{-# OPTIONS --safe #-}

module Aletheia.Protocol.Command where

open import Data.String using (String)

data Command : Set where
  Echo : String → Command
