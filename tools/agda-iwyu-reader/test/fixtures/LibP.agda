-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}
module LibP where
data TagP : Set where mkP : TagP
privF : TagP → TagP
privF t = t
otherF : TagP → TagP
otherF t = t
