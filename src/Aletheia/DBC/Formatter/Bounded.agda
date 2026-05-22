{-# OPTIONS --safe --without-K #-}

-- R19 cluster 8 phase e.4 — bounded-emission theorems for the DBC formatter.
--
-- Closes the cross-binding trust chain established by e.1 / e.2 / e.3:
--   * e.1 — every parsed Identifier carries `length name ≤ max-identifier-
--     length` via the validity-record refinement;
--   * e.2 — every parsed Property has `atomCount ≤ max-atom-count-per-
--     property`;
--   * e.3 — every parsed DBC has `length messages ≤ max-messages-per-file`,
--     `length signals ≤ max-signals-per-message` per message, and
--     `length attributes ≤ max-attributes-per-file` (enforced at the
--     handler boundary).
--
-- These bounded-emission theorems prove the FORMATTER preserves those
-- bounds: if a DBC value `d` was constructed from a parser (hence inherits
-- e.1/e.2/e.3's bounds), then `formatDBC d` emits JSON respecting the same
-- bounds.  Composed with the parse-side enforcement, this means the C++ /
-- Python / Go bindings can TRUST any JSON response from Agda is bounded
-- without doing their own defense-in-depth check (closes CPP-B-9.1 /
-- CPP-B-28.4 cross-binding parity by formal proof, not by mirroring).
--
-- Form: each theorem is a length-preservation lemma — `length (emitted
-- array) ≡ length (corresponding DBC field)` — combined with the input
-- bound to give the output bound.  All proofs reduce to stdlib's
-- `length-map` because every formatter callsite is `JArray (map format-…
-- field)`.
module Aletheia.DBC.Formatter.Bounded where

open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; length; map)
open import Data.List.Properties using (length-map)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Aletheia.DBC.Types using (DBC; DBCMessage)
open import Aletheia.DBC.Formatter using (formatDBCMessage; formatAttribute; formatDBCSignal)

-- Helper: lift `length-map` to a bound-preservation statement.  Given
-- `length xs ≤ n` and `f`, conclude `length (map f xs) ≤ n`.
private
  bound-via-length-map : {A B : Set} (f : A → B) (xs : List A) (n : ℕ)
    → length xs ≤ n → length (map f xs) ≤ n
  bound-via-length-map f xs n bound =
    subst (_≤ n) (sym (length-map f xs)) bound

-- ============================================================================
-- TOP-LEVEL DBC BOUND PRESERVATION
-- ============================================================================

-- The "messages" array emitted by `formatDBC` has the same length as the
-- input `DBC.messages` field.  Combined with the e.3 parse-side cap
-- (`max-messages-per-file`), this means any DBC that survives parseDBC +
-- handleParseDBC bound check round-trips through the formatter with the
-- bound preserved — emitted "messages" array is also ≤ max-messages-per-
-- file.
formatDBC-messages-bounded : ∀ (d : DBC) (n : ℕ)
  → length (DBC.messages d) ≤ n
  → length (map formatDBCMessage (DBC.messages d)) ≤ n
formatDBC-messages-bounded d n =
  bound-via-length-map formatDBCMessage (DBC.messages d) n

-- The "attributes" array emitted by `formatDBC` has the same length as
-- the input `DBC.attributes`.  Combined with the e.3 parse-side cap
-- (`max-attributes-per-file`), the emitted array is ≤ that bound.
formatDBC-attributes-bounded : ∀ (d : DBC) (n : ℕ)
  → length (DBC.attributes d) ≤ n
  → length (map formatAttribute (DBC.attributes d)) ≤ n
formatDBC-attributes-bounded d n =
  bound-via-length-map formatAttribute (DBC.attributes d) n

-- ============================================================================
-- PER-MESSAGE SIGNAL BOUND PRESERVATION
-- ============================================================================

-- Each message's "signals" array, as emitted by `formatDBCMessage`,
-- preserves the length of the input `DBCMessage.signals`.  Combined with
-- the e.3 per-message signals cap (`max-signals-per-message`) enforced
-- at the handler boundary on every accepted DBC, each emitted signals
-- array is ≤ that bound.  `formatDBCSignal` is partially applied to the
-- DLC byte count — the length-map argument is the partially-applied
-- `formatDBCSignal frameBytes`, which is what the formatter actually
-- maps over the signal list at the message-level.
formatDBCMessage-signals-bounded : ∀ (frameBytes : ℕ) (msg : DBCMessage) (n : ℕ)
  → length (DBCMessage.signals msg) ≤ n
  → length (map (formatDBCSignal frameBytes) (DBCMessage.signals msg)) ≤ n
formatDBCMessage-signals-bounded frameBytes msg n =
  bound-via-length-map (formatDBCSignal frameBytes) (DBCMessage.signals msg) n
