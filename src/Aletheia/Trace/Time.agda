{-# OPTIONS --safe --without-K #-}

-- Refined timestamp type with an erased unit phantom for dimensional analysis.
--
-- Purpose: Give `Timestamp` a type-level unit so that the Agda core cannot
-- silently mix microseconds, milliseconds, nanoseconds, or seconds.
-- Types: TimeUnit (ns / μs / ms / s), Timestamp (@0 u : TimeUnit).
-- Role: Foundation for Trace.CANTrace and all LTL metric operators.
--
-- Design: The unit parameter `u` is marked `@0` (erased modality). Agda
-- checks it during type checking, but MAlonzo strips it entirely at
-- compile time — the runtime representation of `Timestamp μs` is a
-- single-constructor record wrapping `ℕ`, the same shape as the old
-- `Timestamp = ℕ` alias after GHC unboxing. Two timestamps in different
-- units (`Timestamp μs` vs `Timestamp ms`) are distinct Agda types and
-- cannot be mixed without an explicit conversion, giving dimensional
-- analysis at the type level without any runtime cost from the unit.
--
-- The Aletheia stack hardcodes μs across all bindings (C++
-- `std::chrono::microseconds`, Go `Timestamp{Microseconds int64}`, Python
-- docstrings, binary protocol), so in practice every usable `Timestamp u`
-- in this project is `Timestamp μs`. The unit parameter exists for:
-- (1) theorem parameterisation (Coalgebra lemmas can generalise over u),
-- (2) documentation (the unit is visible in every signature, not a comment),
-- (3) future extensibility (higher-frequency buses may adopt ns).
module Aletheia.Trace.Time where

open import Data.Nat using (ℕ; _≤_)

-- ---------------------------------------------------------------------------
-- Time units
-- ---------------------------------------------------------------------------

-- Supported time units. Only `μs` is currently produced by the binding
-- layer, but the data type is fully populated so theorems and future
-- converters can reference the other units by name.
data TimeUnit : Set where
  ns : TimeUnit  -- nanoseconds
  μs : TimeUnit  -- microseconds (bindings' canonical unit)
  ms : TimeUnit  -- milliseconds
  s  : TimeUnit  -- seconds

-- ---------------------------------------------------------------------------
-- Refined Timestamp type
-- ---------------------------------------------------------------------------

-- A point in time, wrapped in a single-constructor record with an erased
-- unit parameter. `tsValue` extracts the raw ℕ for hot-path arithmetic.
record Timestamp (@0 u : TimeUnit) : Set where
  constructor mkTs
  field
    tsValue : ℕ

open Timestamp public

-- ---------------------------------------------------------------------------
-- Unit-preserving comparisons
-- ---------------------------------------------------------------------------

-- Propositional ≤ on same-unit timestamps.
infix 4 _≤ᵗ_
_≤ᵗ_ : ∀ {@0 u} → Timestamp u → Timestamp u → Set
t₁ ≤ᵗ t₂ = tsValue t₁ ≤ tsValue t₂
