-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- Stands in for `Data.List.Base`: re-exports the origin's constructor AND defines
-- a SECOND constructor of the same name (as `InitLast.[]` shadows the list `[]`),
-- so `nilA` reaches an importer with two resolutions from two different modules.
module AmbigMid where

open import AmbigOrigin public

data ViewA : Set where
  nilA : ViewA
