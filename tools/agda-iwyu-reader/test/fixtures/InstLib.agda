-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module InstLib where
data TagI : Set where mkI : TagI
record HasDef : Set where
  field def : TagI
open HasDef public
instance
  defI : HasDef
  defI = record { def = mkI }
getDef : {{HasDef}} → TagI
getDef {{r}} = HasDef.def r
