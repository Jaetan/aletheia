-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
-- Stands in for `Agda.Builtin.List`: the module that really defines the
-- constructor an importer ends up naming.
module AmbigOrigin where

data BoxA : Set where
  nilA : BoxA
