-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module OriginC where
data TagC : Set where mkC : TagC
module GenC (X : Set) where
  wrapC : TagC → TagC
  wrapC t = t
