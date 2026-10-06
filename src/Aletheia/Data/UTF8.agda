-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- How many bytes UTF-8 encodes text in (RFC 3629): a character below
-- U+0080 takes one byte, below U+0800 two, below U+10000 three, the rest
-- four.  An input's length bound counts these bytes, the size of the buffer
-- that crossed the boundary, whatever its characters.
module Aletheia.Data.UTF8 where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; foldr)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)

utf8Width : Char → ℕ
utf8Width c =
  if code <ᵇ 128 then 1 else if code <ᵇ 2048 then 2 else if code <ᵇ 65536 then 3 else 4
  where
    code = toℕ c

utf8Length : List Char → ℕ
utf8Length = foldr (λ c n → utf8Width c + n) 0
