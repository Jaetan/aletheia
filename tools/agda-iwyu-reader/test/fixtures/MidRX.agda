-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module MidRX where
open import OriginRX public   -- re-exports Trx, mkrx, rxUsed, rxUnused
reOwn : Trx → Trx
reOwn t = t
