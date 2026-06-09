-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OriginRX where
data Trx : Set where mkrx : Trx
rxUsed : Trx → Trx
rxUsed t = t
rxUnused : Trx → Trx
rxUnused t = t
