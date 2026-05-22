{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.8 — DSL-side `messageHeaderFmt`.
--
-- The BO_ header line as a single `Format (ℕ × Identifier × ℕ × Identifier)`.
-- Captures the prefix that precedes the SG_ block in `emitMessage-chars`:
--
--     BO_ <rawId> <msgName>: <rawDlc> <msgSender>\n
--
-- Production `parseMessage` (in `Topology.SignalLine`) is refactored
-- alongside this commit to drive the header through `parse messageHeaderFmt`,
-- mirroring η's `parseSignalLine = parse signalLineFmt` migration.  The
-- universal `roundtrip` theorem in `Format.agda` discharges the header
-- parse-after-emit pass in one structural sweep — the SG_ block + trailing
-- newlines + `buildMessage` close compose around it (see
-- `Properties.Topology.Message`).
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `ws`     — mandatory one-or-more (after "BO_", between rawId and
--                msgName, after ":", between rawDlc and msgSender).
--                Canonical emit `' ' ∷ []`.
--   * `wsOpt`  — optional zero-or-more (pre-`:`, pre-newline post-sender).
--                Canonical emit `[]`.
--
-- Newline: re-uses η's `newlineFmt = altSum "\r\n" "\n"` exposed at the
-- top level of `Format.SignalLine`.  Canonical emit picks the lone-`\n`
-- branch.
--
-- Structure: 5 sequential captures (literal "BO_", nat, ident, ":", nat,
-- ident) glued with `withWS`/`withWSOpt`/`withPrefix`, with a top-level
-- iso flattening the trailing `Identifier × ⊤` (from the closing newline)
-- into `ℕ × Identifier × ℕ × Identifier`.
module Aletheia.DBC.TextParser.Format.Message where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Format using
  (Format; literal; ident; nat; pair; iso;
   wsOpt; ws; withPrefix)
open import Aletheia.DBC.TextParser.Format.SignalLine using
  (newlineFmt; withWS; withWSOpt)


-- ============================================================================
-- HEADER FORMAT
-- ============================================================================

-- Underlying nested-pair carrier.  Final `⊤` consumes the closing newline.
private
  HeaderCarrier : Set
  HeaderCarrier =
    ℕ × (Identifier × (ℕ × (Identifier × ⊤)))

  φHdr : HeaderCarrier → ℕ × Identifier × ℕ × Identifier
  φHdr (rawId , msgName , rawDlc , msgSender , _) =
    rawId , msgName , rawDlc , msgSender

  ψHdr : ℕ × Identifier × ℕ × Identifier → HeaderCarrier
  ψHdr (rawId , msgName , rawDlc , msgSender) =
    rawId , msgName , rawDlc , msgSender , tt

  -- Σ-η on nested products discharges this directly.
  φψ-Hdr : ∀ b → φHdr (ψHdr b) ≡ b
  φψ-Hdr _ = refl

  -- Inner pair-tower:
  --   "BO_" then ws then nat then ws then ident then wsOpt then ":"
  --   then ws then nat then ws then ident then wsOpt then "\n"
  innerFmt : Format HeaderCarrier
  innerFmt =
    withPrefix (toList "BO_") (
      withWS (
        pair nat (
          withWS (
            pair ident (
              withWSOpt (
                withPrefix (':' ∷ []) (
                  withWS (
                    pair nat (
                      withWS (
                        pair ident (
                          withWSOpt newlineFmt)))))))))))

messageHeaderFmt : Format (ℕ × Identifier × ℕ × Identifier)
messageHeaderFmt = iso φHdr ψHdr φψ-Hdr innerFmt
