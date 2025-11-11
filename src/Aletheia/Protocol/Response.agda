{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Response where

open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.DBC.Types using (DBC)

-- Response payload types
data ResponseData : Set where
  NoData : ResponseData
  EchoData : String → ResponseData
  DBCData : DBC → ResponseData
  SignalValueData : ℚ → ResponseData
  FrameData : Vec Byte 8 → ResponseData

-- Complete response with success/error and optional data
record Response : Set where
  constructor mkResponse
  field
    success : Bool
    message : String
    payload : ResponseData

-- Helper constructors for common response patterns
successResponse : String → ResponseData → Response
successResponse msg dat = mkResponse true msg dat

errorResponse : String → Response
errorResponse msg = mkResponse false msg NoData

-- Format response as YAML for output
formatResponse : Response → String
formatResponse resp =
  "success: " ++ (if Response.success resp then "true" else "false") ++ "\n" ++
  "message: \"" ++ Response.message resp ++ "\"\n" ++
  formatData (Response.payload resp)
  where
    formatData : ResponseData → String
    formatData NoData = ""
    formatData (EchoData s) = "echo: \"" ++ s ++ "\"\n"
    formatData (DBCData dbc) = "dbc: <parsed>\n"  -- TODO: Implement DBC serialization
    formatData (SignalValueData val) = "value: " ++ "<rational>" ++ "\n"  -- TODO: Implement ℚ → String
    formatData (FrameData bytes) = "frame: <bytes>\n"  -- TODO: Implement Vec Byte → String
