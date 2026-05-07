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
-- so every binding's `format_dbc_text` (Python / C++ / Go) gets uniform
-- sender→nodes derivation; pushing it here avoided a Python-only shim.
-- Both proof halves (JSONParser roundtrip + B.3.d universal) still apply
-- — `deriveNodesIfEmpty` is upstream of `formatText`, so the universal
-- `parseText (formatText d) ≡ inj₂ d` holds for the *normalized* `d`.
module Aletheia.Protocol.Handlers.FormatDBCText where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; map; concatMap)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Types using (DBC; DBCMessage; Node; mkNode)
open import Aletheia.DBC.Identifier using (Identifier; _≟ᴵ_)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.TextFormatter using (formatText)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Error using (WithContext; HandlerErr; WrappedParse)

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

-- Format DBC JSON dict back to .dbc text using the verified Agda formatter.
-- State is never mutated — read-only operation on the JSON argument; the
-- currently-loaded DBC (if any) is untouched.  This is the inverse of
-- ParseDBCText at the wire level: text → JSON → text closes byte-identical
-- modulo `WellFormedDBC d` (post-Phase-E.9a, modulo other WF fields only).
handleFormatDBCText : JSON → StreamState → StreamState × Response
handleFormatDBCText dbcJSON state with parseDBCWithErrors dbcJSON
... | inj₁ parseErr = (state , Response.Error (WithContext "FormatDBCText" (HandlerErr (WrappedParse parseErr))))
... | inj₂ dbc      = (state , Response.DBCTextResponse (formatText (deriveNodesIfEmpty dbc)))
