-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerWildNarrow where
open import WMod
useAB : Tw
useAB = wa (wb mkw)
