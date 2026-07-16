-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- `outer` is defined in terms of `inner`, so forcing `outer` to reduce drags
-- `inner`'s QName into the reducing module's elaborated terms even when that
-- module never names `inner`.
module LeakLib where

data TagL : Set where
  mkL : TagL

inner : TagL → TagL
inner mkL = mkL

outer : TagL → TagL
outer x = inner x
