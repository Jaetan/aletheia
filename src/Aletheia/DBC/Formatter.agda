{-# OPTIONS --safe --without-K #-}

-- DBC pretty-printer: serialize DBC AST back to JSON.
--
-- Purpose: Convert a DBC value to JSON matching the parseDBCWithErrors schema.
-- Enables roundtrip testing (parse -> format -> parse = identity) and
-- exporting validated/modified DBC definitions.
-- Role: Used by Protocol.StreamState to handle FormatDBC command.
--
-- Identifier-typed fields and AST text fields (unit, version, comment text,
-- AVString payload, ATEnum labels, value-table entries, attribute names) all
-- emit `JString : List Char → JSON` directly via the underlying List Char
-- field — no `fromList` round-trip — so the per-construct roundtrip lemmas
-- can close axiom-free (no `toList∘fromList`). Kind-discriminator literals
-- (`"node"`, `"network"`, `"int"`, …) use the ergonomic `JStringS` helper
-- since their parse-side is `JString (toList "literal")` and the literal-form
-- equality is locally provable.
module Aletheia.DBC.Formatter where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.DecRat.Refinement using (intDecRatToℤ; natDecRatToℕ)

open import Data.String as String using (String; toList)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Aletheia.JSON using (JSON; JObject; JString; JStringS; JNumber; JBool; JArray)
open import Aletheia.Prelude using (ℕtoℚ; fromℤ)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When;
  SignalGroup; EnvironmentVar; ValueTable; varTypeToℕ;
  Node; mkNode; DBCComment; mkComment;
  CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar;
  AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar; ASNodeMsg; ASNodeSig;
  AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex;
  AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex;
  AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig;
  AttrDef; mkAttrDef; AttrDefault; mkAttrDefault; AttrAssign; mkAttrAssign;
  DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign;
  RawValueDesc; mkRawValueDesc)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.DecRat using (DecRat; toℚ)

-- ============================================================================
-- HELPER: ℕ → JNumber
-- ============================================================================

ℕtoJSON : ℕ → JSON
ℕtoJSON n = JNumber (ℕtoℚ n)

ℤtoJSON : ℤ → JSON
ℤtoJSON z = JNumber (fromℤ z)

-- Identifier → JString carrying List Char directly (bypasses fromList).
identJSON : Identifier → JSON
identJSON i = JString (Identifier.name i)

-- ============================================================================
-- FIELD FORMATTERS
-- ============================================================================

-- Closed-form `List Char` so that `parseByteOrder (formatByteOrder bo)`
-- reduces under abstract `bo` after a single roundtrip rewrite (no
-- `fromList∘toList` axiom slipped in by `JStringS`).  The wire-level UTF-8
-- bytes are unchanged because `JString` serialises char-by-char.
formatByteOrder : ByteOrder → List Char
formatByteOrder LittleEndian = toList "little_endian"
formatByteOrder BigEndian    = toList "big_endian"

formatCANId : CANId → List (String × JSON)
formatCANId (CANId.Standard n _) = ("id" , ℕtoJSON n) ∷ []
formatCANId (CANId.Extended n _) = ("id" , ℕtoJSON n) ∷ ("extended" , JBool true) ∷ []

formatPresence : SignalPresence → List (String × JSON)
formatPresence Always        = ("presence" , JStringS "always") ∷ []
formatPresence (When mux vs) = ("multiplexor" , identJSON mux)
  ∷ ("multiplex_values" , JArray (map ℕtoJSON (List⁺.toList vs))) ∷ []

-- Format a single (value, description) entry for a value table OR a signal's
-- valueDescriptions.  Hoisted above formatDBCSignal so the signal formatter
-- can use it for its `"valueDescriptions"` array.
formatValueEntry : ℕ × List Char → JSON
formatValueEntry (n , s) = JObject (
  ("value" , ℕtoJSON n) ∷
  ("description" , JString s) ∷
  [])

-- ============================================================================
-- SIGNAL / MESSAGE / DBC FORMATTERS
-- ============================================================================

formatDBCSignal : ℕ → DBCSignal → JSON
formatDBCSignal frameBytes sig =
  let def = DBCSignal.signalDef sig
      bo  = DBCSignal.byteOrder sig
      sb  = unconvertStartBit frameBytes bo (SignalDef.startBit def) (SignalDef.bitLength def)
  in JObject (
    ("name"      , identJSON (DBCSignal.name sig)) ∷
    ("startBit"  , ℕtoJSON sb) ∷
    ("length"    , ℕtoJSON (SignalDef.bitLength def)) ∷
    ("byteOrder" , JString (formatByteOrder (DBCSignal.byteOrder sig))) ∷
    ("signed"    , JBool (SignalDef.isSigned def)) ∷
    ("factor"    , JNumber (toℚ (SignalDef.factor def))) ∷
    ("offset"    , JNumber (toℚ (SignalDef.offset def))) ∷
    ("minimum"   , JNumber (toℚ (SignalDef.minimum def))) ∷
    ("maximum"   , JNumber (toℚ (SignalDef.maximum def))) ∷
    ("unit"      , JString (DBCSignal.unit sig)) ∷
    ("receivers" , JArray (map identJSON (CanonicalReceivers.list (DBCSignal.receivers sig)))) ∷
    ("valueDescriptions" , JArray (map formatValueEntry (DBCSignal.valueDescriptions sig))) ∷
    formatPresence (DBCSignal.presence sig))

formatDBCMessage : DBCMessage → JSON
formatDBCMessage msg = JObject (
  formatCANId (DBCMessage.id msg) ++ₗ
  ("name"    , identJSON (DBCMessage.name msg)) ∷
  ("dlc"     , ℕtoJSON (dlcBytes (DBCMessage.dlc msg))) ∷
  ("sender"  , identJSON (DBCMessage.sender msg)) ∷
  ("senders" , JArray (map identJSON (DBCMessage.senders msg))) ∷
  ("signals" , JArray (map (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg))) ∷
  [])

formatSignalGroup : SignalGroup → JSON
formatSignalGroup sg = JObject (
  ("name"    , identJSON (SignalGroup.name sg)) ∷
  ("signals" , JArray (map identJSON (SignalGroup.signals sg))) ∷
  [])

formatEnvironmentVar : EnvironmentVar → JSON
formatEnvironmentVar ev = JObject (
  ("name"    , identJSON (EnvironmentVar.name ev)) ∷
  ("varType" , ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))) ∷
  ("initial" , JNumber (toℚ (EnvironmentVar.initial ev))) ∷
  ("minimum" , JNumber (toℚ (EnvironmentVar.minimum ev))) ∷
  ("maximum" , JNumber (toℚ (EnvironmentVar.maximum ev))) ∷
  [])

formatValueTable : ValueTable → JSON
formatValueTable vt = JObject (
  ("name"    , identJSON (ValueTable.name vt)) ∷
  ("entries" , JArray (map formatValueEntry (ValueTable.entries vt))) ∷
  [])

-- Phase E.8 (Plan B): JSON wire shape for one RawValueDesc.
-- The CAN-ID half mirrors `formatDBCMessage`'s leading `("id", …) ± ("extended", true)`
-- pair (via `formatCANId`); the signal target + entries follow.
formatRawValueDesc : RawValueDesc → JSON
formatRawValueDesc rvd = JObject (
  formatCANId (RawValueDesc.canId rvd) ++ₗ
  ("signalName" , identJSON (RawValueDesc.signalName rvd)) ∷
  ("entries"    , JArray (map formatValueEntry (RawValueDesc.entries rvd))) ∷
  [])

-- ============================================================================
-- TIER 2 METADATA FORMATTERS (nodes, comments, attributes)
-- ============================================================================

-- ---- Nodes (BU_) ----

formatNode : Node → JSON
formatNode n = JObject (("name" , identJSON (Node.name n)) ∷ [])

-- ---- Comments (CM_) ----

-- Emit a CommentTarget as a raw field list so callers can wrap it in JObject.
-- The "kind" discriminator is always the first field; subsequent fields
-- mirror the variant payload exactly (via formatCANId for message/signal).
formatCommentTarget : CommentTarget → List (String × JSON)
formatCommentTarget CTNetwork = ("kind" , JStringS "network") ∷ []
formatCommentTarget (CTNode n) =
  ("kind" , JStringS "node") ∷ ("node" , identJSON n) ∷ []
formatCommentTarget (CTMessage id) =
  ("kind" , JStringS "message") ∷ formatCANId id
formatCommentTarget (CTSignal id s) =
  ("kind" , JStringS "signal") ∷ formatCANId id ++ₗ ("signal" , identJSON s) ∷ []
formatCommentTarget (CTEnvVar ev) =
  ("kind" , JStringS "envVar") ∷ ("envVar" , identJSON ev) ∷ []

formatComment : DBCComment → JSON
formatComment c = JObject (
  ("target" , JObject (formatCommentTarget (DBCComment.target c))) ∷
  ("text"   , JString (DBCComment.text c)) ∷
  [])

-- ---- Attributes (BA_*) ----

-- Closed-form `List Char` for the same reason as `formatByteOrder`: keeps
-- attribute roundtrip proofs axiom-free under abstract `AttrDef.scope d`.
formatAttrScope : AttrScope → List Char
formatAttrScope ASNetwork = toList "network"
formatAttrScope ASNode    = toList "node"
formatAttrScope ASMessage = toList "message"
formatAttrScope ASSignal  = toList "signal"
formatAttrScope ASEnvVar  = toList "envVar"
formatAttrScope ASNodeMsg = toList "nodeMsg"
formatAttrScope ASNodeSig = toList "nodeSig"

-- Emit AttrType as a raw field list (callers wrap in JObject).
formatAttrType : AttrType → List (String × JSON)
formatAttrType (ATInt mn mx) =
  ("kind" , JStringS "int") ∷ ("min" , ℤtoJSON (intDecRatToℤ mn)) ∷ ("max" , ℤtoJSON (intDecRatToℤ mx)) ∷ []
formatAttrType (ATFloat mn mx) =
  ("kind" , JStringS "float") ∷ ("min" , JNumber (toℚ mn)) ∷ ("max" , JNumber (toℚ mx)) ∷ []
formatAttrType ATString =
  ("kind" , JStringS "string") ∷ []
formatAttrType (ATEnum labels) =
  ("kind" , JStringS "enum") ∷ ("values" , JArray (map JString labels)) ∷ []
formatAttrType (ATHex mn mx) =
  ("kind" , JStringS "hex") ∷ ("min" , ℕtoJSON (natDecRatToℕ mn)) ∷ ("max" , ℕtoJSON (natDecRatToℕ mx)) ∷ []

-- Emit AttrValue as a raw field list (callers wrap in JObject).
formatAttrValue : AttrValue → List (String × JSON)
formatAttrValue (AVInt v) =
  ("kind" , JStringS "int") ∷ ("value" , ℤtoJSON (intDecRatToℤ v)) ∷ []
formatAttrValue (AVFloat v) =
  ("kind" , JStringS "float") ∷ ("value" , JNumber (toℚ v)) ∷ []
formatAttrValue (AVString v) =
  ("kind" , JStringS "string") ∷ ("value" , JString v) ∷ []
formatAttrValue (AVEnum v) =
  ("kind" , JStringS "enum") ∷ ("value" , ℕtoJSON (natDecRatToℕ v)) ∷ []
formatAttrValue (AVHex v) =
  ("kind" , JStringS "hex") ∷ ("value" , ℕtoJSON (natDecRatToℕ v)) ∷ []

-- Emit AttrTarget as a raw field list (callers wrap in JObject).
formatAttrTarget : AttrTarget → List (String × JSON)
formatAttrTarget ATgtNetwork =
  ("kind" , JStringS "network") ∷ []
formatAttrTarget (ATgtNode n) =
  ("kind" , JStringS "node") ∷ ("node" , identJSON n) ∷ []
formatAttrTarget (ATgtMessage id) =
  ("kind" , JStringS "message") ∷ formatCANId id
formatAttrTarget (ATgtSignal id s) =
  ("kind" , JStringS "signal") ∷ formatCANId id ++ₗ ("signal" , identJSON s) ∷ []
formatAttrTarget (ATgtEnvVar ev) =
  ("kind" , JStringS "envVar") ∷ ("envVar" , identJSON ev) ∷ []
formatAttrTarget (ATgtNodeMsg n id) =
  ("kind" , JStringS "nodeMsg") ∷ ("node" , identJSON n) ∷ formatCANId id
formatAttrTarget (ATgtNodeSig n id s) =
  ("kind" , JStringS "nodeSig") ∷ ("node" , identJSON n) ∷ formatCANId id
    ++ₗ ("signal" , identJSON s) ∷ []

-- Raw field lists for each BA_* sub-record. `formatAttribute` prepends the
-- "kind" discriminator so the three variants live in a single flat object.
attrDefFields : AttrDef → List (String × JSON)
attrDefFields d =
  ("name"     , JString (AttrDef.name d)) ∷
  ("scope"    , JString (formatAttrScope (AttrDef.scope d))) ∷
  ("attrType" , JObject (formatAttrType (AttrDef.attrType d))) ∷
  []

attrDefaultFields : AttrDefault → List (String × JSON)
attrDefaultFields d =
  ("name"  , JString (AttrDefault.name d)) ∷
  ("value" , JObject (formatAttrValue (AttrDefault.value d))) ∷
  []

attrAssignFields : AttrAssign → List (String × JSON)
attrAssignFields a =
  ("name"   , JString (AttrAssign.name a)) ∷
  ("target" , JObject (formatAttrTarget (AttrAssign.target a))) ∷
  ("value"  , JObject (formatAttrValue (AttrAssign.value a))) ∷
  []

-- Discriminated union: prepend "kind" so parseAttribute can dispatch on it
-- before calling the appropriate sub-parser on the full object.
formatAttribute : DBCAttribute → JSON
formatAttribute (DBCAttrDef d) = JObject (
  ("kind" , JStringS "definition") ∷ attrDefFields d)
formatAttribute (DBCAttrDefault d) = JObject (
  ("kind" , JStringS "default") ∷ attrDefaultFields d)
formatAttribute (DBCAttrAssign a) = JObject (
  ("kind" , JStringS "assignment") ∷ attrAssignFields a)

-- ============================================================================
-- TOP-LEVEL DBC FORMATTER
-- ============================================================================

formatDBC : DBC → JSON
formatDBC dbc = JObject (
  ("version"  , JString (DBC.version dbc)) ∷
  ("messages" , JArray (map formatDBCMessage (DBC.messages dbc))) ∷
  ("signalGroups"    , JArray (map formatSignalGroup (DBC.signalGroups dbc))) ∷
  ("environmentVars" , JArray (map formatEnvironmentVar (DBC.environmentVars dbc))) ∷
  ("valueTables"     , JArray (map formatValueTable (DBC.valueTables dbc))) ∷
  ("nodes"           , JArray (map formatNode (DBC.nodes dbc))) ∷
  ("comments"        , JArray (map formatComment (DBC.comments dbc))) ∷
  ("attributes"      , JArray (map formatAttribute (DBC.attributes dbc))) ∷
  -- Phase E.8 (Plan B): always emit (defaults to `[]` on JSON path; only
  -- the text-parse path can populate this with non-empty entries).
  ("unresolvedValueDescs" , JArray (map formatRawValueDesc (DBC.unresolvedValueDescs dbc))) ∷
  [])
