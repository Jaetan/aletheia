-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OriginAX where
data Tax : Set where mkax : Tax
record BoxA : Set where
  field unboxA : Tax
open BoxA public
module GenA (X : Set) where
  instance
    boxA : BoxA
    boxA = record { unboxA = mkax }
