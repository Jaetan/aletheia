-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OriginI where
data TagI2 : Set where mkI2 : TagI2
record Box : Set where
  field unbox : TagI2
open Box public
module GenI (X : Set) where
  instance
    boxI : Box
    boxI = record { unbox = mkI2 }
