-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerPrivDead where
open import LibP using (TagP; mkP)
private
  open import LibP using (privF)
noP : TagP
noP = mkP
