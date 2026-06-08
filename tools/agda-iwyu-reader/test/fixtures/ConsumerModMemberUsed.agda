-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerModMemberUsed where
open import ModExpLib using (U; module Reasoning)
open Reasoning
useR : U → U
useR x = idr x
