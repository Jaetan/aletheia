{-# OPTIONS --safe --without-K #-}

-- ParseDBCText command handler — split from Handlers.agda.
--
-- Purpose: Isolate the DBC text parser's transitive import closure
-- (TextParser → TopLevel → Attributes → ~30 modules) from the main
-- Handlers module.  Pre-split, importing `parseText` directly into
-- `Handlers.agda` exhausted the 16 GiB elaborator cap during the
-- StreamCommand → Handlers → Main compile chain.
--
-- Role: Imported by `Aletheia.Protocol.Handlers` for the
-- `processStreamCommand (ParseDBCText _) _` dispatch case.
module Aletheia.Protocol.Handlers.ParseDBCText where

open import Data.Char using (Char)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; ValueTable; RawValueDesc; DBCComment;
  DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign;
  AttrDef; AttrDefault; AttrAssign; AttrType; ATEnum; AttrValue; AVString)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; errorIssues; warningIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.DBC.TextParser using (parseText)
open import Aletheia.LTL.SignalPredicate using (emptyCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState; ReadyToStream)
open import Aletheia.Error using
  ( DBCTextParseError; InputBoundExceeded
  ; WithContext; HandlerErr; DBCTextParseErr
  ; ValidationFailed
  )
open import Aletheia.Limits using
  ( BoundKind; InputLengthBytes; ArrayCardinality; StringLength
  ; max-dbc-text-bytes
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-comments-per-file; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file
  ; max-string-length-bytes
  )

-- Parse DBC from raw DBC text using the verified Agda text parser.
-- Track B.3.e — composes the proven parseText (DBC/TextParser.agda) with the
-- runtime validator so the success path returns a parsed-AND-validated DBC.
-- Three result categories:
--   • parseText fails        → Error wrapping a typed DBCTextParseError.
--   • parser succeeds, errors → Error wrapping ValidationFailed (errorIssues).
--   • parser+validator clean  → ParsedDBCResponse with body + warnings.
--
-- Implementation note: pattern-match through a helper (rather than `with
-- parseText text`) so the elaborator does not abstract `parseText text`
-- in the goal type during type-checking — inlining the `with` form here
-- exhausts the 16 GiB heap cap.  See feedback_expose_scrutinee_for_external_rewrite.
-- R19 cluster 8 phase e.3: cardinality refinement at the handler boundary
-- (mirror of the same helpers in `Aletheia.Protocol.Handlers`).  parseText
-- itself is unchanged so existing roundtrip proofs preserve their shape.
-- The check is duplicated here (not imported from Handlers.agda) because
-- Handlers.agda imports this module → no upward dependency.

private
  signalsBound : List DBCMessage → Maybe (ℕ × ℕ)
  signalsBound [] = nothing
  signalsBound (msg ∷ rest) with length (DBCMessage.signals msg) <ᵇ suc max-signals-per-message
  ... | true  = signalsBound rest
  ... | false = just (length (DBCMessage.signals msg) , max-signals-per-message)

  -- R20 cluster H — mirror of `Handlers.totalValueDescriptions`; see the
  -- rationale comment there.  Duplicated here (not imported) for the same
  -- cycle-avoidance reason the rest of this private block is duplicated.
  vdsInSignals : List DBCSignal → ℕ
  vdsInSignals [] = 0
  vdsInSignals (s ∷ rest) = length (DBCSignal.valueDescriptions s) + vdsInSignals rest

  vdsInMessages : List DBCMessage → ℕ
  vdsInMessages [] = 0
  vdsInMessages (m ∷ rest) = vdsInSignals (DBCMessage.signals m) + vdsInMessages rest

  vdsInTables : List ValueTable → ℕ
  vdsInTables [] = 0
  vdsInTables (t ∷ rest) = length (ValueTable.entries t) + vdsInTables rest

  vdsInUnresolved : List RawValueDesc → ℕ
  vdsInUnresolved [] = 0
  vdsInUnresolved (rv ∷ rest) = length (RawValueDesc.entries rv) + vdsInUnresolved rest

  totalValueDescriptions : DBC → ℕ
  totalValueDescriptions dbc =
    vdsInMessages (DBC.messages dbc) +
    vdsInTables (DBC.valueTables dbc) +
    vdsInUnresolved (DBC.unresolvedValueDescs dbc)

  firstDBCOverBound : DBC → Maybe (ℕ × ℕ)
  firstDBCOverBound dbc with length (DBC.messages dbc) <ᵇ suc max-messages-per-file
  ... | false = just (length (DBC.messages dbc) , max-messages-per-file)
  ... | true  with signalsBound (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with length (DBC.attributes dbc) <ᵇ suc max-attributes-per-file
  ...     | false = just (length (DBC.attributes dbc) , max-attributes-per-file)
  ...     | true  with length (DBC.comments dbc) <ᵇ suc max-comments-per-file
  ...       | false = just (length (DBC.comments dbc) , max-comments-per-file)
  ...       | true  with length (DBC.nodes dbc) <ᵇ suc max-nodes-per-file
  ...         | false = just (length (DBC.nodes dbc) , max-nodes-per-file)
  ...         | true  with length (DBC.valueTables dbc) <ᵇ suc max-value-tables-per-file
  ...           | false = just (length (DBC.valueTables dbc) , max-value-tables-per-file)
  ...           | true  with totalValueDescriptions dbc <ᵇ suc max-value-descriptions-per-file
  ...             | false = just (totalValueDescriptions dbc , max-value-descriptions-per-file)
  ...             | true  = nothing

  -- R20 cluster I — AGDA-D-32.2 — mirror of `firstStringOverBound` in
  -- `Handlers.agda` (see rationale there).  Duplicated here, not imported,
  -- for the same cycle-avoidance reason as the cardinality block above.
  firstOverBoundLC : List Char → Maybe (ℕ × ℕ)
  firstOverBoundLC cs with length cs <ᵇ suc max-string-length-bytes
  ... | true  = nothing
  ... | false = just (length cs , max-string-length-bytes)

  firstOverBoundEntries : List (ℕ × List Char) → Maybe (ℕ × ℕ)
  firstOverBoundEntries [] = nothing
  firstOverBoundEntries ((_ , cs) ∷ rest) with firstOverBoundLC cs
  ... | just over = just over
  ... | nothing   = firstOverBoundEntries rest

  firstOverBoundSignal : DBCSignal → Maybe (ℕ × ℕ)
  firstOverBoundSignal sig with firstOverBoundLC (DBCSignal.unit sig)
  ... | just over = just over
  ... | nothing   = firstOverBoundEntries (DBCSignal.valueDescriptions sig)

  firstOverBoundInSignals : List DBCSignal → Maybe (ℕ × ℕ)
  firstOverBoundInSignals [] = nothing
  firstOverBoundInSignals (s ∷ rest) with firstOverBoundSignal s
  ... | just over = just over
  ... | nothing   = firstOverBoundInSignals rest

  firstOverBoundInMessages : List DBCMessage → Maybe (ℕ × ℕ)
  firstOverBoundInMessages [] = nothing
  firstOverBoundInMessages (m ∷ rest) with firstOverBoundInSignals (DBCMessage.signals m)
  ... | just over = just over
  ... | nothing   = firstOverBoundInMessages rest

  firstOverBoundInComments : List DBCComment → Maybe (ℕ × ℕ)
  firstOverBoundInComments [] = nothing
  firstOverBoundInComments (c ∷ rest) with firstOverBoundLC (DBCComment.text c)
  ... | just over = just over
  ... | nothing   = firstOverBoundInComments rest

  firstOverBoundEnumLabels : List (List Char) → Maybe (ℕ × ℕ)
  firstOverBoundEnumLabels [] = nothing
  firstOverBoundEnumLabels (cs ∷ rest) with firstOverBoundLC cs
  ... | just over = just over
  ... | nothing   = firstOverBoundEnumLabels rest

  firstOverBoundAttrType : AttrType → Maybe (ℕ × ℕ)
  firstOverBoundAttrType (ATEnum vs) = firstOverBoundEnumLabels vs
  firstOverBoundAttrType _           = nothing

  firstOverBoundAttrValue : AttrValue → Maybe (ℕ × ℕ)
  firstOverBoundAttrValue (AVString cs) = firstOverBoundLC cs
  firstOverBoundAttrValue _             = nothing

  firstOverBoundAttr : DBCAttribute → Maybe (ℕ × ℕ)
  firstOverBoundAttr (DBCAttrDef ad) with firstOverBoundLC (AttrDef.name ad)
  ... | just over = just over
  ... | nothing   = firstOverBoundAttrType (AttrDef.attrType ad)
  firstOverBoundAttr (DBCAttrDefault adef) with firstOverBoundLC (AttrDefault.name adef)
  ... | just over = just over
  ... | nothing   = firstOverBoundAttrValue (AttrDefault.value adef)
  firstOverBoundAttr (DBCAttrAssign aa) with firstOverBoundLC (AttrAssign.name aa)
  ... | just over = just over
  ... | nothing   = firstOverBoundAttrValue (AttrAssign.value aa)

  firstOverBoundInAttrs : List DBCAttribute → Maybe (ℕ × ℕ)
  firstOverBoundInAttrs [] = nothing
  firstOverBoundInAttrs (a ∷ rest) with firstOverBoundAttr a
  ... | just over = just over
  ... | nothing   = firstOverBoundInAttrs rest

  firstOverBoundInValueTables : List ValueTable → Maybe (ℕ × ℕ)
  firstOverBoundInValueTables [] = nothing
  firstOverBoundInValueTables (vt ∷ rest) with firstOverBoundEntries (ValueTable.entries vt)
  ... | just over = just over
  ... | nothing   = firstOverBoundInValueTables rest

  firstOverBoundInUnresolved : List RawValueDesc → Maybe (ℕ × ℕ)
  firstOverBoundInUnresolved [] = nothing
  firstOverBoundInUnresolved (rv ∷ rest) with firstOverBoundEntries (RawValueDesc.entries rv)
  ... | just over = just over
  ... | nothing   = firstOverBoundInUnresolved rest

  firstStringOverBound : DBC → Maybe (ℕ × ℕ)
  firstStringOverBound dbc with firstOverBoundLC (DBC.version dbc)
  ... | just over = just over
  ... | nothing with firstOverBoundInMessages (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with firstOverBoundInComments (DBC.comments dbc)
  ...     | just over = just over
  ...     | nothing with firstOverBoundInAttrs (DBC.attributes dbc)
  ...       | just over = just over
  ...       | nothing with firstOverBoundInValueTables (DBC.valueTables dbc)
  ...         | just over = just over
  ...         | nothing = firstOverBoundInUnresolved (DBC.unresolvedValueDescs dbc)

handleParseDBCTextResult : DBCTextParseError ⊎ DBC → StreamState → StreamState × Response
handleParseDBCTextResult (inj₁ err)  state =
  (state , Response.Error (WithContext "ParseDBCText" (DBCTextParseErr err)))
handleParseDBCTextResult (inj₂ dbc) state =
  helper dbc (firstDBCOverBound dbc) (firstStringOverBound dbc)
  where
    helper : DBC → Maybe (ℕ × ℕ) → Maybe (ℕ × ℕ) → StreamState × Response
    helper dbc (just (obs , lim)) _ =
      (state , Response.Error (WithContext "ParseDBCText"
        (InputBoundExceeded ArrayCardinality obs lim)))
    helper dbc nothing (just (obs , lim)) =
      (state , Response.Error (WithContext "ParseDBCText"
        (InputBoundExceeded StringLength obs lim)))
    helper dbc nothing nothing =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error (WithContext "ParseDBCText" (HandlerErr (ValidationFailed (errorIssues issues)))))
         else (ReadyToStream dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

-- Adversarial-input bound: rejects inputs longer than `max-dbc-text-bytes`
-- (`Aletheia.Limits`) with a typed `DBCTextParseError.InputBoundExceeded`
-- before invoking the parser, per AGENTS.md universal rule "Adversarial-input
-- bounds at parser surfaces".
handleParseDBCText : String → StreamState → StreamState × Response
handleParseDBCText text state =
  let inputLen = length (toList text)
  in if inputLen ≤ᵇ max-dbc-text-bytes
     then handleParseDBCTextResult (parseText text) state
     else (state , Response.Error (WithContext "ParseDBCText"
              (InputBoundExceeded InputLengthBytes inputLen max-dbc-text-bytes)))
