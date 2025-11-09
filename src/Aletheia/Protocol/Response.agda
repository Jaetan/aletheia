{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Response where

open import Data.String using (String)
open import Data.Bool using (Bool)

record Response : Set where
  field
    success : Bool
    message : String

formatResponse : Response → String
formatResponse = {!!}
