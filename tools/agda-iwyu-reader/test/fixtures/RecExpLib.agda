-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module RecExpLib where

data U : Set where
  u : U

module Inner where
  record Box : Set where
    field unbox : U
  theBox : Box
  theBox = record { unbox = u }

open Inner public
