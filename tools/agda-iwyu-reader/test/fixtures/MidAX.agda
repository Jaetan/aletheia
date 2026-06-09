-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module MidAX where
open import OriginAX public
open GenA Tax public   -- module application: copies boxA into MidAX, re-exported
axUnused : Tax → Tax
axUnused t = t
