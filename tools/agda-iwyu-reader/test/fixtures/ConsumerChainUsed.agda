-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerChainUsed where
open import OriginC using (TagC; mkC)
open import MidC2 using (module InstC2)
open InstC2
useChain : TagC
useChain = wrapC mkC
