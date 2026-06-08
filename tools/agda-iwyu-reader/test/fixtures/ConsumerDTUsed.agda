-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerDTUsed where
open import OriginDT using (Seed)
open import MidDT using (module InstD)
open InstD
useD : D
useD = dcon
