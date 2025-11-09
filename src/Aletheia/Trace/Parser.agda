{-# OPTIONS --safe --without-K #-}

module Aletheia.Trace.Parser where

open import Aletheia.Trace.CANTrace
open import Aletheia.Parser.Combinators

parseCANTrace : Parser CANTrace
parseCANTrace = {!!}
