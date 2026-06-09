-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OriginDT where
data Seed : Set where s0 : Seed
module GenD (X : Set) where
  data D : Set where dcon : D
