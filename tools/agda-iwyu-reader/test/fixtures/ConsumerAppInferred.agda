-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerAppInferred where
open import MidAX
needA : {{BoxA}} → Tax
needA {{b}} = unboxA b
r : Tax
r = needA    -- boxA (the applied copy) resolved by instance search: no body token
