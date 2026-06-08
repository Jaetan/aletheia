-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module MidI where
open import OriginI
module InstI where
  open GenI TagI2 public   -- copies the instance boxI into InstI
