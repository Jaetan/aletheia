-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module ConsumerWildInferred where
open import WInst
r : Ti
r = needI    -- insti resolved by instance search: no body token, only namesIn sees it
