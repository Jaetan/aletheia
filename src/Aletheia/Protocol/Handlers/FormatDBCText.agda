-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- FormatDBCText command handler — split from Handlers.agda.
--
-- Purpose: Isolate the DBC text formatter's transitive import closure
-- (TextFormatter → TopLevel → Attributes/EnvVars/Comments/SignalGroups/
--  ValueTables/Emitter → ~30 modules) from the main Handlers module.
-- Mirrors `Handlers/ParseDBCText.agda`'s split rationale: pre-split,
-- importing `formatText` directly into `Handlers.agda` would push the
-- StreamCommand → Handlers → Main compile chain past the 16 GiB heap cap.
--
-- Role: Imported by `Aletheia.Protocol.Handlers` for the
-- `processStreamCommand (FormatDBCText _) _` dispatch case.
--
-- Pipeline: JSON DBC → parseDBCWithErrors → DBC value → deriveNodesIfEmpty
-- → formatText → String.  `deriveNodesIfEmpty` runs at the protocol layer
-- so every binding's `format_dbc_text` (Python / C++ / Go / Rust) gets uniform
-- sender→nodes derivation; pushing it here avoided a Python-only shim.
-- Both proof halves (JSONParser roundtrip + universal text-roundtrip)
-- still apply — `deriveNodesIfEmpty` is upstream of `formatText`, so the
-- universal `parseText (formatText d) ≡ inj₂ d` holds for the
-- *normalized* `d`.
module Aletheia.Protocol.Handlers.FormatDBCText where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; map; concatMap)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; Node; mkNode
  ; IsError; ValidationIssue; mkIssue; TextRoundTripDivergence )
open import Aletheia.DBC.Identifier using (Identifier; _≟ᴵ_)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.DBC.TextParser.RoundTripCheck using (roundTripsWithᵇ)
open import Aletheia.DBC.TextParser.WellFormedCheck using (wfTextIssues)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Error using (WithContext; HandlerErr; TextRoundTripFailed)

private
  -- True if `i` is structurally equal to any element of `xs`.
  containsId : Identifier → List Identifier → Bool
  containsId i []       = false
  containsId i (x ∷ xs) = ⌊ i ≟ᴵ x ⌋ ∨ containsId i xs

  -- Order-preserving dedupe by Identifier equality.  First occurrence wins.
  -- Termination: structural recursion on the input list.
  nubIds : List Identifier → List Identifier
  nubIds = go []
    where
      go : List Identifier → List Identifier → List Identifier
      go _    []       = []
      go seen (x ∷ xs) with containsId x seen
      ... | true  = go seen xs
      ... | false = x ∷ go (x ∷ seen) xs

  -- All node identifiers a single message references as a transmitter:
  -- the primary BO_ sender plus any BO_TX_BU_ extras.
  msgSenders : DBCMessage → List Identifier
  msgSenders m = DBCMessage.sender m ∷ DBCMessage.senders m

  -- Union of every message's transmitter set, encounter order, deduped,
  -- wrapped as Node values.
  uniqueSenderNodes : List DBCMessage → List Node
  uniqueSenderNodes ms = map mkNode (nubIds (concatMap msgSenders ms))

-- If `nodes` is empty, populate from the union of all message senders.
-- Already-non-empty `nodes` lists pass through unchanged.  Applied at the
-- protocol-handler boundary so every binding sees the same behavior.
deriveNodesIfEmpty : DBC → DBC
deriveNodesIfEmpty d with DBC.nodes d
... | _ ∷ _ = d
... | []    = record d { nodes = uniqueSenderNodes (DBC.messages d) }

-- Format a DBC (given as a JSON dict) back to `.dbc` text using the verified
-- Agda formatter.  State is never mutated — a read-only operation on the JSON
-- argument; the currently-loaded DBC (if any) is untouched.
--
-- ROUND-TRIP CONTRACT (always strict):
--
-- `FormatDBCText` emits text ONLY when that text provably re-parses to the input
-- DBC; otherwise it refuses with a typed `TextRoundTripFailed` error.  There is
-- no lenient mode — emitting text we KNOW will not round-trip is exactly the
-- silent lossy output this command exists to prevent.
--
-- The runtime discharge is the exact round-trip check `roundTripsWithᵇ d′ (formatText d′)`
-- (`RoundTripCheck.agda`): it decides `parseText (formatText d′) ≡ inj₂ d′` by
-- executable decidable equality on the whole DBC — no well-formedness
-- precondition, no caller obligation.  On `true` the response carries the text
-- plus `wfTextIssues d′` (diagnostic warnings only, see below); on `false` the
-- handler refuses.  `formatDBCTextResult-sound`
-- (`Handlers.Properties.FormatDBCText`) machine-checks that every emitted
-- `DBCTextResponse txt` satisfies `parseText txt ≡ inj₂ d′` — the guarantee is
-- verified, not merely definitional.
--
-- `wfTextIssues` (the per-field well-formedness checker) is SUFFICIENT-but-not-
-- necessary for the round-trip: it flags text-DBC shapes known to diverge, but
-- does NOT discharge the text-side aggregator `WellFormedTextDBCAgg d′` at runtime
-- (the per-field checker is weaker than the exact check) and appears here for
-- diagnostics only — the actual guarantee is the exact round-trip verdict.
--
-- Node derivation: `deriveNodesIfEmpty` populates an empty `nodes` list from the
-- union of message senders BEFORE the check, so the verdict (and the emitted
-- text) are against the normalized `d′`, not the caller's raw JSON.
--
-- SHARING: `formatText d′` is threaded as an ARGUMENT (via
-- `withText`, not re-`let`), so it is one shared thunk feeding BOTH the wire
-- output and `roundTripsWithᵇ` — this is what lets `formatDBCTextResult-sound`
-- transfer to the emitted text verbatim (same `txt` decided and shipped).

-- FormatDBCText is ALWAYS strict: when the exact round-trip verdict is false,
-- divergence is an error, never a warning.
divergenceIssue : ValidationIssue
divergenceIssue =
  mkIssue IsError TextRoundTripDivergence
    "re-parsing the emitted text does not reproduce the input DBC"

finish : String → Bool → List ValidationIssue → Response
finish txt rt diags =
  if rt
  then Response.DBCTextResponse txt diags
  else Response.Error (WithContext "FormatDBCText"
         (HandlerErr (TextRoundTripFailed (divergenceIssue ∷ diags))))

-- Response for a node-normalized DBC `d′`: emit text with `wfTextIssues`
-- diagnostics iff it provably round-trips (the exact round-trip check —
-- evaluate `parseText (formatText d′)` and deep-compare), else refuse.
-- Top-level (not a `where` of the handler) so `Handlers.Properties.FormatDBCText`
-- can name it and machine-check the emitted-text round-trip guarantee.
formatDBCTextResult : DBC → Response
formatDBCTextResult d′ = withText (formatText d′)
  where
  withText : String → Response
  withText txt = finish txt (roundTripsWithᵇ d′ txt) (wfTextIssues d′)

handleFormatDBCText : JSON → StreamState → StreamState × Response
handleFormatDBCText dbcJSON state with parseDBCWithErrors dbcJSON
... | inj₁ err = (state , Response.Error (WithContext "FormatDBCText" err))
... | inj₂ dbc = (state , formatDBCTextResult (deriveNodesIfEmpty dbc))
