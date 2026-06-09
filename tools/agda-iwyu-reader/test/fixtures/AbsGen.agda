-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module AbsGen where
data TagAb : Set where mkAb : TagAb
module GenAb (X : Set) where
  abstract
    absF : TagAb → TagAb
    absF t = t
