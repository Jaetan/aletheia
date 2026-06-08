-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerIUsed where
open import OriginI using (TagI2; mkI2; Box; unbox)
open import MidI using (module InstI)
open InstI
needBox : {{Box}} → TagI2
needBox {{b}} = unbox b
r : TagI2
r = needBox    -- boxI resolved by instance search: no body token for boxI
