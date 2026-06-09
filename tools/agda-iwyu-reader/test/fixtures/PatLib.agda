-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module PatLib where
data NatLike : Set where
  zeroL : NatLike
  sucL  : NatLike → NatLike
pattern two = sucL (sucL zeroL)
