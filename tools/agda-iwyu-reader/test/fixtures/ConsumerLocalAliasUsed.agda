-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerLocalAliasUsed where
open import LocAliasLib using (U; module Helper)
open Helper using (idh)
useH : U → U
useH x = idh x
