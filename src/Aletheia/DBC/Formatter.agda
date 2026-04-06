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
open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JObject; JString; JNumber; JBool; JArray; ℕtoℚ)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When;
  SignalGroup; EnvironmentVar; ValueTable; varTypeToℕ)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId)

-- ============================================================================
-- HELPER: ℕ → JNumber
-- ============================================================================

ℕtoJSON : ℕ → JSON
ℕtoJSON n = JNumber (ℕtoℚ n)

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
formatPresence Always       = ("presence" , JString "always") ∷ []
formatPresence (When mux v) = ("multiplexor" , JString mux) ∷ ("multiplex_value" , ℕtoJSON v) ∷ []

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
    ("factor"    , JNumber (SignalDef.factor def)) ∷
    ("offset"    , JNumber (SignalDef.offset def)) ∷
    ("minimum"   , JNumber (SignalDef.minimum def)) ∷
    ("maximum"   , JNumber (SignalDef.maximum def)) ∷
    ("unit"      , JString (DBCSignal.unit sig)) ∷
    formatPresence (DBCSignal.presence sig))

formatDBCMessage : DBCMessage → JSON
formatDBCMessage msg = JObject (
  formatCANId (DBCMessage.id msg) ++ₗ
  ("name"    , JString (DBCMessage.name msg)) ∷
  ("dlc"     , ℕtoJSON (dlcBytes (DBCMessage.dlc msg))) ∷
  ("sender"  , JString (DBCMessage.sender msg)) ∷
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
  ("initial" , JNumber (EnvironmentVar.initial ev)) ∷
  ("minimum" , JNumber (EnvironmentVar.minimum ev)) ∷
  ("maximum" , JNumber (EnvironmentVar.maximum ev)) ∷
  [])

formatValueTable : ValueTable → JSON
formatValueTable vt = JObject (
  ("name"    , JString (ValueTable.name vt)) ∷
  ("entries" , JArray (map formatValueEntry (ValueTable.entries vt))) ∷
  [])

formatDBC : DBC → JSON
formatDBC dbc = JObject (
  ("version"  , JString (DBC.version dbc)) ∷
  ("messages" , JArray (map formatDBCMessage (DBC.messages dbc))) ∷
  ("signalGroups"    , JArray (map formatSignalGroup (DBC.signalGroups dbc))) ∷
  ("environmentVars" , JArray (map formatEnvironmentVar (DBC.environmentVars dbc))) ∷
  ("valueTables"     , JArray (map formatValueTable (DBC.valueTables dbc))) ∷
  [])
