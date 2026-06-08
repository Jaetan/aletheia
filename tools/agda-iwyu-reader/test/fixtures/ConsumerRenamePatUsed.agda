-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerRenamePatUsed where
open import PatLib using (NatLike) renaming (two to twoR)
useTwo : NatLike
useTwo = twoR
