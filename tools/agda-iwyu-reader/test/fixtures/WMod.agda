-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module WMod where
data Tw : Set where mkw : Tw
wa : Tw → Tw
wa t = t
wb : Tw → Tw
wb t = t
wc : Tw → Tw
wc t = t
