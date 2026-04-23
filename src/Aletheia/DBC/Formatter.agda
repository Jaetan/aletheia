{-# OPTIONS --safe --without-K #-}

-- DBC pretty-printer: serialize DBC AST back to JSON.
--
-- Purpose: Convert a DBC value to JSON matching the parseDBCWithErrors schema.
-- Enables roundtrip testing (parse -> format -> parse = identity) and
-- exporting validated/modified DBC definitions.
-- Role: Used by Protocol.StreamState to handle FormatDBC command.
module Aletheia.DBC.Formatter where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Aletheia.JSON using (JSON; JObject; JString; JNumber; JBool; JArray)
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
  DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign)
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

-- ============================================================================
-- FIELD FORMATTERS
-- ============================================================================

formatByteOrder : ByteOrder → String
formatByteOrder LittleEndian = "little_endian"
formatByteOrder BigEndian    = "big_endian"

formatCANId : CANId → List (String × JSON)
formatCANId (CANId.Standard n _) = ("id" , ℕtoJSON n) ∷ []
formatCANId (CANId.Extended n _) = ("id" , ℕtoJSON n) ∷ ("extended" , JBool true) ∷ []

formatPresence : SignalPresence → List (String × JSON)
formatPresence Always        = ("presence" , JString "always") ∷ []
formatPresence (When mux vs) = ("multiplexor" , JString mux)
  ∷ ("multiplex_values" , JArray (map ℕtoJSON (List⁺.toList vs))) ∷ []

-- ============================================================================
-- SIGNAL / MESSAGE / DBC FORMATTERS
-- ============================================================================

formatDBCSignal : ℕ → DBCSignal → JSON
formatDBCSignal frameBytes sig =
  let def = DBCSignal.signalDef sig
      bo  = DBCSignal.byteOrder sig
      sb  = unconvertStartBit frameBytes bo (SignalDef.startBit def) (SignalDef.bitLength def)
  in JObject (
    ("name"      , JString (DBCSignal.name sig)) ∷
    ("startBit"  , ℕtoJSON sb) ∷
    ("length"    , ℕtoJSON (SignalDef.bitLength def)) ∷
    ("byteOrder" , JString (formatByteOrder (DBCSignal.byteOrder sig))) ∷
    ("signed"    , JBool (SignalDef.isSigned def)) ∷
    ("factor"    , JNumber (toℚ (SignalDef.factor def))) ∷
    ("offset"    , JNumber (toℚ (SignalDef.offset def))) ∷
    ("minimum"   , JNumber (toℚ (SignalDef.minimum def))) ∷
    ("maximum"   , JNumber (toℚ (SignalDef.maximum def))) ∷
    ("unit"      , JString (DBCSignal.unit sig)) ∷
    ("receivers" , JArray (map JString (DBCSignal.receivers sig))) ∷
    formatPresence (DBCSignal.presence sig))

formatDBCMessage : DBCMessage → JSON
formatDBCMessage msg = JObject (
  formatCANId (DBCMessage.id msg) ++ₗ
  ("name"    , JString (DBCMessage.name msg)) ∷
  ("dlc"     , ℕtoJSON (dlcBytes (DBCMessage.dlc msg))) ∷
  ("sender"  , JString (DBCMessage.sender msg)) ∷
  ("senders" , JArray (map JString (DBCMessage.senders msg))) ∷
  ("signals" , JArray (map (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg))) ∷
  [])

formatValueEntry : ℕ × String → JSON
formatValueEntry (n , s) = JObject (
  ("value" , ℕtoJSON n) ∷
  ("description" , JString s) ∷
  [])

formatSignalGroup : SignalGroup → JSON
formatSignalGroup sg = JObject (
  ("name"    , JString (SignalGroup.name sg)) ∷
  ("signals" , JArray (map JString (SignalGroup.signals sg))) ∷
  [])

formatEnvironmentVar : EnvironmentVar → JSON
formatEnvironmentVar ev = JObject (
  ("name"    , JString (EnvironmentVar.name ev)) ∷
  ("varType" , ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))) ∷
  ("initial" , JNumber (toℚ (EnvironmentVar.initial ev))) ∷
  ("minimum" , JNumber (toℚ (EnvironmentVar.minimum ev))) ∷
  ("maximum" , JNumber (toℚ (EnvironmentVar.maximum ev))) ∷
  [])

formatValueTable : ValueTable → JSON
formatValueTable vt = JObject (
  ("name"    , JString (ValueTable.name vt)) ∷
  ("entries" , JArray (map formatValueEntry (ValueTable.entries vt))) ∷
  [])

-- ============================================================================
-- TIER 2 METADATA FORMATTERS (nodes, comments, attributes)
-- ============================================================================

-- ---- Nodes (BU_) ----

formatNode : Node → JSON
formatNode n = JObject (("name" , JString (Node.name n)) ∷ [])

-- ---- Comments (CM_) ----

-- Emit a CommentTarget as a raw field list so callers can wrap it in JObject.
-- The "kind" discriminator is always the first field; subsequent fields
-- mirror the variant payload exactly (via formatCANId for message/signal).
formatCommentTarget : CommentTarget → List (String × JSON)
formatCommentTarget CTNetwork = ("kind" , JString "network") ∷ []
formatCommentTarget (CTNode n) =
  ("kind" , JString "node") ∷ ("node" , JString n) ∷ []
formatCommentTarget (CTMessage id) =
  ("kind" , JString "message") ∷ formatCANId id
formatCommentTarget (CTSignal id s) =
  ("kind" , JString "signal") ∷ formatCANId id ++ₗ ("signal" , JString s) ∷ []
formatCommentTarget (CTEnvVar ev) =
  ("kind" , JString "envVar") ∷ ("envVar" , JString ev) ∷ []

formatComment : DBCComment → JSON
formatComment c = JObject (
  ("target" , JObject (formatCommentTarget (DBCComment.target c))) ∷
  ("text"   , JString (DBCComment.text c)) ∷
  [])

-- ---- Attributes (BA_*) ----

formatAttrScope : AttrScope → String
formatAttrScope ASNetwork = "network"
formatAttrScope ASNode    = "node"
formatAttrScope ASMessage = "message"
formatAttrScope ASSignal  = "signal"
formatAttrScope ASEnvVar  = "envVar"
formatAttrScope ASNodeMsg = "nodeMsg"
formatAttrScope ASNodeSig = "nodeSig"

-- Emit AttrType as a raw field list (callers wrap in JObject).
formatAttrType : AttrType → List (String × JSON)
formatAttrType (ATInt mn mx) =
  ("kind" , JString "int") ∷ ("min" , ℤtoJSON mn) ∷ ("max" , ℤtoJSON mx) ∷ []
formatAttrType (ATFloat mn mx) =
  ("kind" , JString "float") ∷ ("min" , JNumber (toℚ mn)) ∷ ("max" , JNumber (toℚ mx)) ∷ []
formatAttrType ATString =
  ("kind" , JString "string") ∷ []
formatAttrType (ATEnum labels) =
  ("kind" , JString "enum") ∷ ("values" , JArray (map JString labels)) ∷ []
formatAttrType (ATHex mn mx) =
  ("kind" , JString "hex") ∷ ("min" , ℕtoJSON mn) ∷ ("max" , ℕtoJSON mx) ∷ []

-- Emit AttrValue as a raw field list (callers wrap in JObject).
formatAttrValue : AttrValue → List (String × JSON)
formatAttrValue (AVInt v) =
  ("kind" , JString "int") ∷ ("value" , ℤtoJSON v) ∷ []
formatAttrValue (AVFloat v) =
  ("kind" , JString "float") ∷ ("value" , JNumber (toℚ v)) ∷ []
formatAttrValue (AVString v) =
  ("kind" , JString "string") ∷ ("value" , JString v) ∷ []
formatAttrValue (AVEnum v) =
  ("kind" , JString "enum") ∷ ("value" , ℕtoJSON v) ∷ []
formatAttrValue (AVHex v) =
  ("kind" , JString "hex") ∷ ("value" , ℕtoJSON v) ∷ []

-- Emit AttrTarget as a raw field list (callers wrap in JObject).
formatAttrTarget : AttrTarget → List (String × JSON)
formatAttrTarget ATgtNetwork =
  ("kind" , JString "network") ∷ []
formatAttrTarget (ATgtNode n) =
  ("kind" , JString "node") ∷ ("node" , JString n) ∷ []
formatAttrTarget (ATgtMessage id) =
  ("kind" , JString "message") ∷ formatCANId id
formatAttrTarget (ATgtSignal id s) =
  ("kind" , JString "signal") ∷ formatCANId id ++ₗ ("signal" , JString s) ∷ []
formatAttrTarget (ATgtEnvVar ev) =
  ("kind" , JString "envVar") ∷ ("envVar" , JString ev) ∷ []
formatAttrTarget (ATgtNodeMsg n id) =
  ("kind" , JString "nodeMsg") ∷ ("node" , JString n) ∷ formatCANId id
formatAttrTarget (ATgtNodeSig n id s) =
  ("kind" , JString "nodeSig") ∷ ("node" , JString n) ∷ formatCANId id
    ++ₗ ("signal" , JString s) ∷ []

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
  ("kind" , JString "definition") ∷ attrDefFields d)
formatAttribute (DBCAttrDefault d) = JObject (
  ("kind" , JString "default") ∷ attrDefaultFields d)
formatAttribute (DBCAttrAssign a) = JObject (
  ("kind" , JString "assignment") ∷ attrAssignFields a)

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
  [])
