-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerRenameDeadClean where
open import Origin using () renaming (idO to idR)
data Dummy : Set where d : Dummy
