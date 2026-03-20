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
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; _/_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JObject; JString; JNumber; JBool; JArray)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalPresence; Always; When)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.Frame using (CANId)

-- ============================================================================
-- HELPER: ℕ → JNumber
-- ============================================================================

-- Convert ℕ to JNumber (same pattern as Protocol.Routing)
ℕtoJSON : ℕ → JSON
ℕtoJSON n = JNumber ((+ n) / 1)

-- ============================================================================
-- FIELD FORMATTERS
-- ============================================================================

formatByteOrder : ByteOrder → String
formatByteOrder LittleEndian = "little_endian"
formatByteOrder BigEndian    = "big_endian"

formatCANId : CANId → List (String × JSON)
formatCANId (CANId.Standard n) = ("id" , ℕtoJSON n) ∷ []
formatCANId (CANId.Extended n) = ("id" , ℕtoJSON n) ∷ ("extended" , JBool true) ∷ []

formatPresence : SignalPresence → List (String × JSON)
formatPresence Always       = ("presence" , JString "always") ∷ []
formatPresence (When mux v) = ("multiplexor" , JString mux) ∷ ("multiplex_value" , ℕtoJSON v) ∷ []

-- ============================================================================
-- SIGNAL / MESSAGE / DBC FORMATTERS
-- ============================================================================

formatDBCSignal : DBCSignal → JSON
formatDBCSignal sig =
  let def = DBCSignal.signalDef sig
  in JObject (
    ("name"      , JString (DBCSignal.name sig)) ∷
    ("startBit"  , ℕtoJSON (SignalDef.startBit def)) ∷
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
  ("dlc"     , ℕtoJSON (DBCMessage.dlc msg)) ∷
  ("sender"  , JString (DBCMessage.sender msg)) ∷
  ("signals" , JArray (map formatDBCSignal (DBCMessage.signals msg))) ∷
  [])

formatDBC : DBC → JSON
formatDBC dbc = JObject (
  ("version"  , JString (DBC.version dbc)) ∷
  ("messages" , JArray (map formatDBCMessage (DBC.messages dbc))) ∷
  [])
