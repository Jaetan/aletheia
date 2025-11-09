{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Parser where

open import Aletheia.Protocol.Command
open import Aletheia.Parser.Combinators

parseCommand : Parser Command
parseCommand = {!!}
