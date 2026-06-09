-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerInstUsed where
open import InstLib using (TagI; getDef; defI)
r : TagI
r = getDef
