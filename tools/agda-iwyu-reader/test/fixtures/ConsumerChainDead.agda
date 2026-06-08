-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerChainDead where
open import OriginC using (TagC; mkC)
open import MidC2 using (module InstC2)
open InstC2
noChain : TagC
noChain = mkC
