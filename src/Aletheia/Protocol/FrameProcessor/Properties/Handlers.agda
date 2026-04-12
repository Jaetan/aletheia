{-# OPTIONS --safe --without-K #-}

-- FFI link properties and read-only handler state preservation.
--
--   PROPERTY 16 — `processFrameDirect` state component
--                 ≡ first projection of `handleDataFrame`
--   PROPERTY 17 — `processFrameDirect` response component
--                 ≡ formatJSON ∘ formatResponse of `handleDataFrame`'s response
--   PROPERTY 18 — End-to-end Ack soundness at the JSON level
--                 (composes the Step `handleDataFrame-ack-sound` lemma
--                  with `formatResponse-ack-unique` to lift the soundness
--                  guarantee through the FFI shim's JSON serialization).
--   PROPERTIES 19–22 — `handleExtractAllSignals`,
--                       `handleBuildFrameByIndex`,
--                       `handleUpdateFrameByIndex`,
--                       `handleFormatDBC` never modify `StreamState`.
--
-- The Step lemmas this module composes with come from
-- `FrameProcessor.Properties.Step`.
module Aletheia.Protocol.FrameProcessor.Properties.Handlers where

open import Aletheia.Protocol.StreamState using (StreamState; getDBC)
open import Aletheia.Protocol.StreamState.Internals using (stepProperty)
open import Aletheia.Protocol.Message using (Response; Ack)
open import Aletheia.Protocol.ResponseFormat using (formatResponse)
open import Aletheia.Protocol.ResponseFormat.Properties using (formatResponse-ack-unique)
open import Aletheia.Protocol.JSON using (JSON; formatJSON)
open import Aletheia.Main using (processFrameDirect)
open import Aletheia.Protocol.Handlers
    using (handleExtractAllSignals; handleBuildFrameByIndex;
           handleUpdateFrameByIndex; handleFormatDBC)
open import Aletheia.Protocol.Iteration using (iterate)
open import Aletheia.Protocol.FrameProcessor.Properties.Step
    using (handleDataFrame-ack-sound)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.DLC using (DLC)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex)
open import Aletheia.Protocol.StreamState using (handleDataFrame; checkMonotonic; Streaming)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- PROPERTY 16-17: processFrameDirect decomposition
-- ============================================================================

-- processFrameDirect = handleDataFrame + formatJSON ∘ formatResponse.
-- State component passes through unchanged.
processFrameDirect-state : ∀ state tf
  → proj₁ (processFrameDirect state tf) ≡ proj₁ (handleDataFrame state tf)
processFrameDirect-state state tf with handleDataFrame state tf
... | (_ , _) = refl

-- Response component is formatJSON ∘ formatResponse of handleDataFrame's response.
processFrameDirect-response : ∀ state tf
  → proj₂ (processFrameDirect state tf)
    ≡ formatJSON (formatResponse (proj₂ (handleDataFrame state tf)))
processFrameDirect-response state tf with handleDataFrame state tf
... | (_ , _) = refl

-- ============================================================================
-- PROPERTY 18: End-to-end Ack soundness at JSON level
-- ============================================================================

-- If the frame is monotonic and formatResponse maps the handler response to
-- the Ack JSON tree, no property was violated.
processFrameDirect-ack-sound-json : ∀ dbc props prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → formatResponse (proj₂ (handleDataFrame (Streaming dbc props prev cache) tf)) ≡ formatResponse Ack
  → proj₂ (iterate (stepProperty dbc cache tf) props) ≡ nothing
processFrameDirect-ack-sound-json dbc props prev cache tf mono fmt-eq =
  handleDataFrame-ack-sound dbc props prev cache tf mono
    (formatResponse-ack-unique (proj₂ (handleDataFrame (Streaming dbc props prev cache) tf)) fmt-eq)

-- ============================================================================
-- PROPERTIES 19-22: Read-only handler state preservation
-- ============================================================================

-- Extract, build, update, formatDBC handlers never modify StreamState.
-- Each proof case-splits on getDBC (withDBC pattern) and, for
-- build/update, on the Either result.

handleExtractAllSignals-preserves-state : ∀ canId dlc bytes state
  → proj₁ (handleExtractAllSignals canId dlc bytes state) ≡ state
handleExtractAllSignals-preserves-state canId dlc bytes state
  with getDBC state
... | nothing = refl
... | just _  = refl

handleBuildFrameByIndex-preserves-state : ∀ canId dlc signalPairs state
  → proj₁ (handleBuildFrameByIndex canId dlc signalPairs state) ≡ state
handleBuildFrameByIndex-preserves-state canId dlc signalPairs state
  with getDBC state
... | nothing = refl
... | just dbc with buildFrameByIndex dbc canId dlc signalPairs
...   | inj₁ _ = refl
...   | inj₂ _ = refl

handleUpdateFrameByIndex-preserves-state : ∀ canId dlc bytes signalPairs state
  → proj₁ (handleUpdateFrameByIndex canId dlc bytes signalPairs state) ≡ state
handleUpdateFrameByIndex-preserves-state canId dlc bytes signalPairs state
  with getDBC state
... | nothing = refl
... | just _  = refl

handleFormatDBC-preserves-state : ∀ state
  → proj₁ (handleFormatDBC state) ≡ state
handleFormatDBC-preserves-state state
  with getDBC state
... | nothing = refl
... | just _  = refl
