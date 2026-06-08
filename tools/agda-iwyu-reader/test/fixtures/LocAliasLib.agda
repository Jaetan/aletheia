-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module LocAliasLib where

data U : Set where
  u : U

module Helper where
  idh : U → U
  idh x = x
