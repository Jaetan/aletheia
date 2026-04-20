{-# OPTIONS --safe --without-K #-}

-- DBC JSON parser for the streaming protocol (Phase 2B).
--
-- Purpose: Parse DBC structures from JSON format sent by Python client.
-- Handles: Complete DBC JSON objects (messages, signals, all metadata).
-- Role: Used by Protocol.StreamState to process parseDBC commands.
--
-- Design: Parses JSON → DBC.Types, validates all required fields, bounded types.
-- Returns typed ParseError values on parse failures.
-- Current protocol: Python converts .dbc → JSON, Agda parses JSON → DBC types.
module Aletheia.DBC.JSONParser where

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When;
  SignalGroup; EnvironmentVar; ValueTable; VarType; IntVar; FloatVar; StringVar;
  Node; mkNode; CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar;
  DBCComment; mkComment; AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar;
  ASNodeMsg; ASNodeSig; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex;
  AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex;
  AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar;
  ATgtNodeMsg; ATgtNodeSig;
  AttrDef; mkAttrDef; AttrDefault; mkAttrDefault; AttrAssign; mkAttrAssign;
  DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign)
open import Aletheia.JSON using (JSON; JObject; JString; lookupString; lookupBool; lookupInt;
  lookupNat; lookupRational; lookupObject; lookupArray; getNat)
open import Aletheia.CAN.DLC using (bytesToValidDLC)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; convertStartBit)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; suc; _%_; _≤ᵇ_; _+_; _<ᵇ_; _∸_; _*_)
open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max; max-physical-bits)
open import Aletheia.Prelude using (require; _>>=ₑ_; ifᵀ_then_else_; mapₑ)
open import Aletheia.Error using
  ( ParseError; MissingField; InvalidByteOrder; InvalidPresence
  ; MissingSigned; InvalidSigned; NotAnObject; ExtCANIdOutOfRange
  ; StdCANIdOutOfRange; DefaultCANIdOutOfRange; InvalidDLCBytes
  ; RootNotObject; MissingSignalName; InContext
  ; SignalBitLengthZero; SignalOverflowsFrame; SignalMSBBelowBitLength
  ; InvalidKind
  )

-- ============================================================================
-- JSON → DBC PARSERS (with typed ParseError)
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : String → ParseError ⊎ ByteOrder
parseByteOrder s =
  if ⌊ s ≟ₛ"little_endian" ⌋ then inj₂ LittleEndian
  else if ⌊ s ≟ₛ"big_endian" ⌋ then inj₂ BigEndian
  else inj₁ (InvalidByteOrder s)

-- Parse a JSON array of naturals into a List ℕ (helper for parseNatList⁺)
parseNatList : List JSON → ParseError ⊎ List ℕ
parseNatList [] = inj₂ []
parseNatList (j ∷ rest) with getNat j
... | nothing = inj₁ (InvalidPresence "non-integer in multiplex_values")
... | just n  = parseNatList rest >>=ₑ λ ns → inj₂ (n ∷ ns)

-- Parse a non-empty JSON array of naturals into a List⁺ ℕ.
-- Produces a List⁺ directly so callers that require non-emptiness (e.g.
-- SignalPresence's `When` constructor) don't need a `λ where` with a dead
-- empty-list branch; the type system rules out the empty result.
parseNatList⁺ : List⁺ JSON → ParseError ⊎ List⁺ ℕ
parseNatList⁺ (j List⁺.∷ rest) with getNat j
... | nothing = inj₁ (InvalidPresence "non-integer in multiplex_values")
... | just n  = parseNatList rest >>=ₑ λ ns → inj₂ (n List⁺.∷ ns)

-- Parse SignalPresence from JSON object
-- Can be: {"presence": "always"} or {"multiplexor": "...", "multiplex_values": [N, ...]}
parseSignalPresence : List (String × JSON) → ParseError ⊎ SignalPresence
parseSignalPresence obj = tryMux
  where
    -- Try explicit "presence" field, default to Always
    tryPresence : ParseError ⊎ SignalPresence
    tryPresence with lookupString "presence" obj
    ... | nothing = inj₂ Always  -- Default to Always
    ... | just presenceStr =
      if ⌊ presenceStr ≟ₛ "always" ⌋ then inj₂ Always
      else inj₁ (InvalidPresence presenceStr)

    -- Try to parse multiplexor and multiplex_values fields
    tryMux : ParseError ⊎ SignalPresence
    tryMux with lookupString "multiplexor" obj
    ... | nothing = tryPresence  -- No multiplexor, try explicit presence field
    ... | just muxName with lookupArray "multiplex_values" obj
    ...   | nothing = tryPresence  -- Have multiplexor but no values, fall back
    ...   | just [] = tryPresence  -- Empty array, treat as always-present
    ...   | just (v ∷ rest) = parseNatList⁺ (v List⁺.∷ rest) >>=ₑ λ ns →
                                inj₂ (When muxName ns)

-- Parse signed field (can be boolean or string "signed"/"unsigned")
parseSigned : List (String × JSON) → ParseError ⊎ Bool
parseSigned obj with lookupBool "signed" obj
... | just b = inj₂ b  -- Found boolean field
... | nothing with lookupString "signed" obj
...   | nothing = inj₁ MissingSigned
...   | just signedStr =
    if ⌊ signedStr ≟ₛ "signed" ⌋ then inj₂ true
    else if ⌊ signedStr ≟ₛ "unsigned" ⌋ then inj₂ false
    else inj₁ (InvalidSigned signedStr)

-- Context wrapper for signal parse errors (extracted from parseSignal where-block so proofs can case-split).
-- Top-level (not private) so SignalWF proofs can mention it in helper signatures.
-- Defined point-free as `mapₑ (InContext ctx)` where `mapₑ = Data.Sum.map₁`.
addSignalContext : String → ParseError ⊎ DBCSignal → ParseError ⊎ DBCSignal
addSignalContext ctx = mapₑ (InContext ctx)

-- Physical-validity gate (BigEndian signals only).
-- LE signals pass through unchanged — PhysicallyValid is trivially `pv-LE refl`
-- because the unconvert→convert roundtrip is the identity for LE.
-- BE signals must satisfy three constraints needed by the BE roundtrip:
--   • bitLength ≥ 1                                  (signal occupies ≥ 1 bit)
--   • startBit + bitLength − 1 < frameBytes * 8       (signal fits in the frame)
--   • bitLength − 1 ≤ startBit                        (BE LSB is below the MSB)
-- Defined as a top-level function (not where-bound) so SignalWF proofs can
-- case-split on the byte order without crossing a private where-scope.
physicalGate : ℕ → ByteOrder → ℕ → ℕ → DBCSignal → ParseError ⊎ DBCSignal
physicalGate _         LittleEndian _   _  sig = inj₂ sig
physicalGate frameBytes BigEndian   csb bl sig =
  ifᵀ 1 ≤ᵇ bl
    then (λ _ →
      ifᵀ csb + bl ∸ 1 <ᵇ frameBytes * 8
        then (λ _ →
          ifᵀ bl ∸ 1 ≤ᵇ csb
            then (λ _ → inj₂ sig)
            else inj₁ (SignalMSBBelowBitLength csb bl))
        else inj₁ (SignalOverflowsFrame csb bl frameBytes))
    else inj₁ SignalBitLengthZero

-- Parse signal fields from JSON (extracted from parseSignal where-block so proofs can case-split).
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignalFields : ℕ → String → String → List (String × JSON) → ParseError ⊎ DBCSignal
parseSignalFields frameBytes ctx name obj =
  addSignalContext ctx (
    require (MissingField "startBit") (lookupNat "startBit" obj) >>=ₑ λ startBit →
    require (MissingField "length") (lookupNat "length" obj) >>=ₑ λ bitLength →
    require (MissingField "byteOrder") (lookupString "byteOrder" obj) >>=ₑ λ byteOrderStr →
    parseByteOrder byteOrderStr >>=ₑ λ byteOrder →
    parseSigned obj >>=ₑ λ isSigned →
    require (MissingField "factor") (lookupRational "factor" obj) >>=ₑ λ factor →
    require (MissingField "offset") (lookupRational "offset" obj) >>=ₑ λ offset →
    require (MissingField "minimum") (lookupRational "minimum" obj) >>=ₑ λ minimum →
    require (MissingField "maximum") (lookupRational "maximum" obj) >>=ₑ λ maximum →
    require (MissingField "unit") (lookupString "unit" obj) >>=ₑ λ unit →
    parseSignalPresence obj >>=ₑ λ presence →
    let sb  = startBit % max-physical-bits
        bl  = bitLength % (1 + max-physical-bits)
        csb = convertStartBit frameBytes byteOrder sb bl
    in physicalGate frameBytes byteOrder csb bl (record
      { name = name
      ; signalDef = record
          { startBit = csb
          ; bitLength = bl
          ; isSigned = isSigned
          ; factor = factor
          ; offset = offset
          ; minimum = minimum
          ; maximum = maximum
          }
      ; byteOrder = byteOrder
      ; unit = unit
      ; presence = presence
      }))

-- Parse a single signal from JSON object.
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignal : ℕ → String → List (String × JSON) → ParseError ⊎ DBCSignal
parseSignal frameBytes context obj =
  require (InContext context MissingSignalName) (lookupString "name" obj) >>=ₑ λ name →
  let ctx = context ++ₛ ", signal '" ++ₛ name ++ₛ "'"
  in parseSignalFields frameBytes ctx name obj

-- Parse a list of signals from JSON array.
-- frameBytes: the message's DLC byte count, used for convertStartBit on BE signals.
parseSignalList : ℕ → String → List JSON → ℕ → ParseError ⊎ (List DBCSignal)
parseSignalList frameBytes context [] _ = inj₂ []
parseSignalList frameBytes context (JObject sigObj ∷ rest) idx =
  parseSignal frameBytes context sigObj >>=ₑ λ sig →
  parseSignalList frameBytes context rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (sig ∷ restParsed)
parseSignalList frameBytes context (_ ∷ _) idx =
  inj₁ (InContext context (NotAnObject "signal" idx))

-- Parse CAN ID from natural and optional "extended" field.
-- Bounds are embedded in the CANId type via T (n <ᵇ max).
-- Uses ifᵀ (regular function, not with) so that rewrite works in roundtrip proofs.
parseCANId : String → ℕ → List (String × JSON) → ParseError ⊎ CANId
parseCANId context rawId obj with lookupBool "extended" obj
... | just true  = ifᵀ rawId <ᵇ extended-can-id-max
                    then (λ pf → inj₂ (Extended rawId pf))
                    else inj₁ (InContext context (ExtCANIdOutOfRange rawId))
... | just false = ifᵀ rawId <ᵇ standard-can-id-max
                    then (λ pf → inj₂ (Standard rawId pf))
                    else inj₁ (InContext context (StdCANIdOutOfRange rawId))
... | nothing    = ifᵀ rawId <ᵇ standard-can-id-max
                    then (λ pf → inj₂ (Standard rawId pf))
                    else inj₁ (InContext context (DefaultCANIdOutOfRange rawId))

-- Stage 1: Parse id + CAN ID from message fields.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageId : String → List (String × JSON) → ParseError ⊎ CANId
parseMessageId context obj =
  require (InContext context (MissingField "id")) (lookupNat "id" obj) >>=ₑ λ rawId →
  parseCANId context rawId obj

-- Stage 2: Parse remaining message fields given a resolved CAN ID.
-- Split out for compositional roundtrip proofs (keeps normalization bounded).
parseMessageBody : String → String → CANId → List (String × JSON) → ParseError ⊎ DBCMessage
parseMessageBody context name canId obj =
  require (InContext context (MissingField "dlc")) (lookupNat "dlc" obj) >>=ₑ λ rawDlc →
  require (InContext context (InvalidDLCBytes rawDlc))
          (bytesToValidDLC rawDlc) >>=ₑ λ dlc →
  require (InContext context (MissingField "sender")) (lookupString "sender" obj) >>=ₑ λ sender →
  require (InContext context (MissingField "signals")) (lookupArray "signals" obj) >>=ₑ λ signalsJSON →
  parseSignalList rawDlc context signalsJSON 0 >>=ₑ λ signals →
  inj₂ (record
    { id = canId
    ; name = name
    ; dlc = dlc
    ; sender = sender
    ; signals = signals
    })

-- Compose stages into full message field parser.
-- Exposed at top level for compositional roundtrip proofs.
parseMessageFields : String → String → List (String × JSON) → ParseError ⊎ DBCMessage
parseMessageFields context name obj =
  parseMessageId context obj >>=ₑ λ canId →
  parseMessageBody context name canId obj

-- Parse a single message from JSON object
parseMessage : List (String × JSON) → ParseError ⊎ DBCMessage
parseMessage obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  let context = "message '" ++ₛ name ++ₛ "'"
  in parseMessageFields context name obj

-- Parse a list of messages from JSON array
parseMessageList : List JSON → ℕ → ParseError ⊎ (List DBCMessage)
parseMessageList [] _ = inj₂ []
parseMessageList (JObject msgObj ∷ rest) idx =
  parseMessage msgObj >>=ₑ λ msg →
  parseMessageList rest (idx + 1) >>=ₑ λ restParsed →
  inj₂ (msg ∷ restParsed)
parseMessageList (_ ∷ _) idx =
  inj₁ (NotAnObject "message" idx)

-- ============================================================================
-- METADATA PARSERS (signal groups, environment vars, value tables)
-- ============================================================================

-- Parse a list of JSON strings
parseStringList : List JSON → ParseError ⊎ List String
parseStringList [] = inj₂ []
parseStringList (JString s ∷ rest) =
  parseStringList rest >>=ₑ λ ss → inj₂ (s ∷ ss)
parseStringList (_ ∷ _) = inj₁ (MissingField "string in array")

-- Parse VarType from natural (0=Int, 1=Float, 2=String)
parseVarType : ℕ → ParseError ⊎ VarType
parseVarType 0 = inj₂ IntVar
parseVarType 1 = inj₂ FloatVar
parseVarType 2 = inj₂ StringVar
parseVarType _ = inj₁ (MissingField "valid varType")

-- Parse a single signal group from JSON object
parseSignalGroup : List (String × JSON) → ParseError ⊎ SignalGroup
parseSignalGroup obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "signals") (lookupArray "signals" obj) >>=ₑ λ sigsJSON →
  parseStringList sigsJSON >>=ₑ λ sigs →
  inj₂ (record { name = name ; signals = sigs })

-- Parse a JSON array of objects, applying a per-element parser.
-- Threads an index for NotAnObject error reporting (fixes hardcoded 0).
-- Directly recursive (not where-block) so roundtrip proofs can generalise over
-- any starting index without needing to reach inside a private helper.
parseObjectList : {A : Set} → String → (List (String × JSON) → ParseError ⊎ A)
  → ℕ → List JSON → ParseError ⊎ List A
parseObjectList typeName parser _ [] = inj₂ []
parseObjectList typeName parser idx (JObject obj ∷ rest) =
  parser obj >>=ₑ λ a →
  parseObjectList typeName parser (suc idx) rest >>=ₑ λ as →
  inj₂ (a ∷ as)
parseObjectList typeName parser idx (_ ∷ _) = inj₁ (NotAnObject typeName idx)

parseSignalGroupList : List JSON → ParseError ⊎ List SignalGroup
parseSignalGroupList = parseObjectList "signalGroup" parseSignalGroup 0

-- Parse a single environment variable from JSON object
parseEnvironmentVar : List (String × JSON) → ParseError ⊎ EnvironmentVar
parseEnvironmentVar obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "varType") (lookupNat "varType" obj) >>=ₑ λ vtNat →
  parseVarType vtNat >>=ₑ λ vt →
  require (MissingField "initial") (lookupRational "initial" obj) >>=ₑ λ initial →
  require (MissingField "minimum") (lookupRational "minimum" obj) >>=ₑ λ minimum →
  require (MissingField "maximum") (lookupRational "maximum" obj) >>=ₑ λ maximum →
  inj₂ (record
    { name = name ; varType = vt ; initial = initial
    ; minimum = minimum ; maximum = maximum })

parseEnvironmentVarList : List JSON → ParseError ⊎ List EnvironmentVar
parseEnvironmentVarList = parseObjectList "environmentVar" parseEnvironmentVar 0

-- Parse a single value table entry from JSON object
parseValueEntry : List (String × JSON) → ParseError ⊎ (ℕ × String)
parseValueEntry obj =
  require (MissingField "value") (lookupNat "value" obj) >>=ₑ λ val →
  require (MissingField "description") (lookupString "description" obj) >>=ₑ λ desc →
  inj₂ (val , desc)

parseValueEntryList : List JSON → ParseError ⊎ List (ℕ × String)
parseValueEntryList = parseObjectList "valueEntry" parseValueEntry 0

-- Parse a single value table from JSON object
parseValueTable : List (String × JSON) → ParseError ⊎ ValueTable
parseValueTable obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "entries") (lookupArray "entries" obj) >>=ₑ λ entriesJSON →
  parseValueEntryList entriesJSON >>=ₑ λ entries →
  inj₂ (record { name = name ; entries = entries })

parseValueTableList : List JSON → ParseError ⊎ List ValueTable
parseValueTableList = parseObjectList "valueTable" parseValueTable 0

-- ============================================================================
-- TIER 2 METADATA PARSERS (nodes, comments, attributes)
-- ============================================================================

-- ---- Nodes (BU_) ----

parseNode : List (String × JSON) → ParseError ⊎ Node
parseNode obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  inj₂ (mkNode name)

parseNodeList : List JSON → ParseError ⊎ List Node
parseNodeList = parseObjectList "node" parseNode 0

-- ---- Comments (CM_) ----

-- Parse a CommentTarget from an object keyed on "kind".
-- Variants:
--   {"kind": "network"}
--   {"kind": "node",    "node": String}
--   {"kind": "message", "id": ℕ, "extended": Bool?}
--   {"kind": "signal",  "id": ℕ, "extended": Bool?, "signal": String}
--   {"kind": "envVar",  "envVar": String}
parseCommentTarget : List (String × JSON) → ParseError ⊎ CommentTarget
parseCommentTarget obj =
  require (MissingField "kind") (lookupString "kind" obj) >>=ₑ λ kind →
  (if ⌊ kind ≟ₛ "network" ⌋ then inj₂ CTNetwork
  else if ⌊ kind ≟ₛ "node" ⌋ then
    (require (MissingField "node") (lookupString "node" obj) >>=ₑ λ n →
     inj₂ (CTNode n))
  else if ⌊ kind ≟ₛ "message" ⌋ then
    (require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "comment target" rawId obj >>=ₑ λ cid →
     inj₂ (CTMessage cid))
  else if ⌊ kind ≟ₛ "signal" ⌋ then
    (require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "comment target" rawId obj >>=ₑ λ cid →
     require (MissingField "signal") (lookupString "signal" obj) >>=ₑ λ sig →
     inj₂ (CTSignal cid sig))
  else if ⌊ kind ≟ₛ "envVar" ⌋ then
    (require (MissingField "envVar") (lookupString "envVar" obj) >>=ₑ λ ev →
     inj₂ (CTEnvVar ev))
  else inj₁ (InvalidKind "commentTarget" kind))

parseComment : List (String × JSON) → ParseError ⊎ DBCComment
parseComment obj =
  require (MissingField "target") (lookupObject "target" obj) >>=ₑ λ tgtObj →
  parseCommentTarget tgtObj >>=ₑ λ target →
  require (MissingField "text") (lookupString "text" obj) >>=ₑ λ text →
  inj₂ (mkComment target text)

parseCommentList : List JSON → ParseError ⊎ List DBCComment
parseCommentList = parseObjectList "comment" parseComment 0

-- ---- Attributes (BA_*) ----

parseAttrScope : String → ParseError ⊎ AttrScope
parseAttrScope s =
  if ⌊ s ≟ₛ "network" ⌋ then inj₂ ASNetwork
  else if ⌊ s ≟ₛ "node"    ⌋ then inj₂ ASNode
  else if ⌊ s ≟ₛ "message" ⌋ then inj₂ ASMessage
  else if ⌊ s ≟ₛ "signal"  ⌋ then inj₂ ASSignal
  else if ⌊ s ≟ₛ "envVar"  ⌋ then inj₂ ASEnvVar
  else if ⌊ s ≟ₛ "nodeMsg" ⌋ then inj₂ ASNodeMsg
  else if ⌊ s ≟ₛ "nodeSig" ⌋ then inj₂ ASNodeSig
  else inj₁ (InvalidKind "attrScope" s)

-- Attribute type declaration (RHS of BA_DEF_).
-- Variants keyed on "kind":
--   {"kind": "int",    "min": ℤ, "max": ℤ}
--   {"kind": "float",  "min": ℚ, "max": ℚ}
--   {"kind": "string"}
--   {"kind": "enum",   "values": [String, ...]}
--   {"kind": "hex",    "min": ℕ, "max": ℕ}
parseAttrType : List (String × JSON) → ParseError ⊎ AttrType
parseAttrType obj =
  require (MissingField "kind") (lookupString "kind" obj) >>=ₑ λ kind →
  (if ⌊ kind ≟ₛ "int" ⌋ then
    (require (MissingField "min") (lookupInt "min" obj) >>=ₑ λ mn →
     require (MissingField "max") (lookupInt "max" obj) >>=ₑ λ mx →
     inj₂ (ATInt mn mx))
  else if ⌊ kind ≟ₛ "float" ⌋ then
    (require (MissingField "min") (lookupRational "min" obj) >>=ₑ λ mn →
     require (MissingField "max") (lookupRational "max" obj) >>=ₑ λ mx →
     inj₂ (ATFloat mn mx))
  else if ⌊ kind ≟ₛ "string" ⌋ then inj₂ ATString
  else if ⌊ kind ≟ₛ "enum" ⌋ then
    (require (MissingField "values") (lookupArray "values" obj) >>=ₑ λ vs →
     parseStringList vs >>=ₑ λ labels →
     inj₂ (ATEnum labels))
  else if ⌊ kind ≟ₛ "hex" ⌋ then
    (require (MissingField "min") (lookupNat "min" obj) >>=ₑ λ mn →
     require (MissingField "max") (lookupNat "max" obj) >>=ₑ λ mx →
     inj₂ (ATHex mn mx))
  else inj₁ (InvalidKind "attrType" kind))

-- Concrete attribute value (BA_, BA_REL_, BA_DEF_DEF_).
-- Variants keyed on "kind":
--   {"kind": "int",    "value": ℤ}
--   {"kind": "float",  "value": ℚ}
--   {"kind": "string", "value": String}
--   {"kind": "enum",   "value": ℕ}   -- 0-based index into definition's labels
--   {"kind": "hex",    "value": ℕ}
parseAttrValue : List (String × JSON) → ParseError ⊎ AttrValue
parseAttrValue obj =
  require (MissingField "kind") (lookupString "kind" obj) >>=ₑ λ kind →
  (if ⌊ kind ≟ₛ "int" ⌋ then
    (require (MissingField "value") (lookupInt "value" obj) >>=ₑ λ v →
     inj₂ (AVInt v))
  else if ⌊ kind ≟ₛ "float" ⌋ then
    (require (MissingField "value") (lookupRational "value" obj) >>=ₑ λ v →
     inj₂ (AVFloat v))
  else if ⌊ kind ≟ₛ "string" ⌋ then
    (require (MissingField "value") (lookupString "value" obj) >>=ₑ λ v →
     inj₂ (AVString v))
  else if ⌊ kind ≟ₛ "enum" ⌋ then
    (require (MissingField "value") (lookupNat "value" obj) >>=ₑ λ v →
     inj₂ (AVEnum v))
  else if ⌊ kind ≟ₛ "hex" ⌋ then
    (require (MissingField "value") (lookupNat "value" obj) >>=ₑ λ v →
     inj₂ (AVHex v))
  else inj₁ (InvalidKind "attrValue" kind))

-- Attribute assignment target (LHS of BA_ / BA_REL_). Superset of CommentTarget
-- with two extra relation variants.
parseAttrTarget : List (String × JSON) → ParseError ⊎ AttrTarget
parseAttrTarget obj =
  require (MissingField "kind") (lookupString "kind" obj) >>=ₑ λ kind →
  (if ⌊ kind ≟ₛ "network" ⌋ then inj₂ ATgtNetwork
  else if ⌊ kind ≟ₛ "node" ⌋ then
    (require (MissingField "node") (lookupString "node" obj) >>=ₑ λ n →
     inj₂ (ATgtNode n))
  else if ⌊ kind ≟ₛ "message" ⌋ then
    (require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "attr target" rawId obj >>=ₑ λ cid →
     inj₂ (ATgtMessage cid))
  else if ⌊ kind ≟ₛ "signal" ⌋ then
    (require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "attr target" rawId obj >>=ₑ λ cid →
     require (MissingField "signal") (lookupString "signal" obj) >>=ₑ λ sig →
     inj₂ (ATgtSignal cid sig))
  else if ⌊ kind ≟ₛ "envVar" ⌋ then
    (require (MissingField "envVar") (lookupString "envVar" obj) >>=ₑ λ ev →
     inj₂ (ATgtEnvVar ev))
  else if ⌊ kind ≟ₛ "nodeMsg" ⌋ then
    (require (MissingField "node") (lookupString "node" obj) >>=ₑ λ n →
     require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "attr target" rawId obj >>=ₑ λ cid →
     inj₂ (ATgtNodeMsg n cid))
  else if ⌊ kind ≟ₛ "nodeSig" ⌋ then
    (require (MissingField "node") (lookupString "node" obj) >>=ₑ λ n →
     require (MissingField "id") (lookupNat "id" obj) >>=ₑ λ rawId →
     parseCANId "attr target" rawId obj >>=ₑ λ cid →
     require (MissingField "signal") (lookupString "signal" obj) >>=ₑ λ sig →
     inj₂ (ATgtNodeSig n cid sig))
  else inj₁ (InvalidKind "attrTarget" kind))

-- BA_DEF_ / BA_DEF_REL_ — carries name, scope, and type declaration.
parseAttrDef : List (String × JSON) → ParseError ⊎ AttrDef
parseAttrDef obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "scope") (lookupString "scope" obj) >>=ₑ λ scopeStr →
  parseAttrScope scopeStr >>=ₑ λ scope →
  require (MissingField "attrType") (lookupObject "attrType" obj) >>=ₑ λ typeObj →
  parseAttrType typeObj >>=ₑ λ ty →
  inj₂ (mkAttrDef name scope ty)

-- BA_DEF_DEF_ — default value for a previously-declared attribute.
parseAttrDefault : List (String × JSON) → ParseError ⊎ AttrDefault
parseAttrDefault obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "value") (lookupObject "value" obj) >>=ₑ λ valObj →
  parseAttrValue valObj >>=ₑ λ val →
  inj₂ (mkAttrDefault name val)

-- BA_ / BA_REL_ — concrete attribute value assigned to a target entity.
parseAttrAssign : List (String × JSON) → ParseError ⊎ AttrAssign
parseAttrAssign obj =
  require (MissingField "name") (lookupString "name" obj) >>=ₑ λ name →
  require (MissingField "target") (lookupObject "target" obj) >>=ₑ λ tgtObj →
  parseAttrTarget tgtObj >>=ₑ λ target →
  require (MissingField "value") (lookupObject "value" obj) >>=ₑ λ valObj →
  parseAttrValue valObj >>=ₑ λ val →
  inj₂ (mkAttrAssign name target val)

-- Discriminated parse for any BA_-family keyword, keyed on "kind":
--   {"kind": "definition", ...}  → DBCAttrDef
--   {"kind": "default",    ...}  → DBCAttrDefault
--   {"kind": "assignment", ...}  → DBCAttrAssign
parseAttribute : List (String × JSON) → ParseError ⊎ DBCAttribute
parseAttribute obj =
  require (MissingField "kind") (lookupString "kind" obj) >>=ₑ λ kind →
  (if ⌊ kind ≟ₛ "definition" ⌋ then
    (parseAttrDef obj >>=ₑ λ d → inj₂ (DBCAttrDef d))
  else if ⌊ kind ≟ₛ "default" ⌋ then
    (parseAttrDefault obj >>=ₑ λ d → inj₂ (DBCAttrDefault d))
  else if ⌊ kind ≟ₛ "assignment" ⌋ then
    (parseAttrAssign obj >>=ₑ λ a → inj₂ (DBCAttrAssign a))
  else inj₁ (InvalidKind "attribute" kind))

parseAttributeList : List JSON → ParseError ⊎ List DBCAttribute
parseAttributeList = parseObjectList "attribute" parseAttribute 0

-- Parse optional array field: returns [] if the field is missing
parseOptionalArray : {A : Set} → (List JSON → ParseError ⊎ List A)
  → Maybe (List JSON) → ParseError ⊎ List A
parseOptionalArray _      nothing   = inj₂ []
parseOptionalArray parser (just xs) = parser xs

-- Parse top-level DBC structure from JSON object (with typed errors)
parseDBCWithErrors : JSON → ParseError ⊎ DBC
parseDBCWithErrors (JObject obj) =
  require (MissingField "version") (lookupString "version" obj) >>=ₑ λ version →
  require (MissingField "messages") (lookupArray "messages" obj) >>=ₑ λ messagesJSON →
  parseMessageList messagesJSON 0 >>=ₑ λ messages →
  parseOptionalArray parseSignalGroupList (lookupArray "signalGroups" obj) >>=ₑ λ groups →
  parseOptionalArray parseEnvironmentVarList (lookupArray "environmentVars" obj) >>=ₑ λ envvars →
  parseOptionalArray parseValueTableList (lookupArray "valueTables" obj) >>=ₑ λ vtables →
  parseOptionalArray parseNodeList (lookupArray "nodes" obj) >>=ₑ λ nodes →
  parseOptionalArray parseCommentList (lookupArray "comments" obj) >>=ₑ λ comments →
  parseOptionalArray parseAttributeList (lookupArray "attributes" obj) >>=ₑ λ attributes →
  inj₂ (record
    { version = version
    ; messages = messages
    ; signalGroups = groups
    ; environmentVars = envvars
    ; valueTables = vtables
    ; nodes = nodes
    ; comments = comments
    ; attributes = attributes
    })
parseDBCWithErrors _ = inj₁ RootNotObject
