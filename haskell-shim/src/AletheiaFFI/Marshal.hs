-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unused-imports #-}

-- | Marshaling helpers between raw C values and MAlonzo-generated Agda types.
--
-- All conversion logic from primitive types (Word8, Word32, Int64) to the
-- corresponding MAlonzo constructors lives here. The FFI shim
-- (AletheiaFFI.hs) imports these and stays purely about the foreign-export
-- surface — no marshaling, no validation, no error formatting.
module AletheiaFFI.Marshal where

import Data.Bits (toIntegralSized)
import Data.Char (ord)
import Data.Int (Int64)
import Data.Word (Word8, Word32)
import Numeric (showHex)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Aletheia.CAN.Constants as AgdaCANConst
import qualified MAlonzo.Code.Aletheia.CAN.DLC as AgdaDLC
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

-- | Encode a String as a JSON string literal (RFC 8259).  Haskell `show` is
-- NOT a JSON encoder: for a non-ASCII or control character it emits a `\NNN`
-- *decimal* escape (e.g. `show "€" == "\"\\8364\""`), which JSON rejects — JSON
-- only allows `\uXXXX` (hex).  A `show`-built envelope carrying user text (the
-- echoed decimal `input`, an error `message`) is therefore invalid JSON the
-- bindings' decoders cannot parse.  This escapes the JSON-mandatory characters
-- and `\u`-escapes everything outside printable ASCII (with surrogate pairs for
-- astral code points), so the result is always valid, ASCII-safe JSON.
jsonString :: String -> String
jsonString s = '"' : concatMap esc s ++ ['"']
  where
    esc '"'  = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc '\b' = "\\b"
    esc '\f' = "\\f"
    esc c
        | c >= ' ' && c < '\DEL' = [c]                    -- printable ASCII
        | n <= 0xFFFF            = uEsc n                 -- BMP code point
        | otherwise             = uEsc hi ++ uEsc lo     -- astral: surrogate pair
      where
        n = ord c
        v = n - 0x10000
        hi = 0xD800 + (v `div` 0x400)
        lo = 0xDC00 + (v `mod` 0x400)
    uEsc x = let h = showHex x "" in "\\u" ++ replicate (4 - length h) '0' ++ h

-- | Format a validation error as a JSON error response string.  The text is
-- carried in `message` — the cross-binding error-envelope convention (Agda
-- `responseToJSON` and all four bindings read `message`; the per-signal
-- extraction object `{name,error}` is a different, narrower shape).
mkErrorJson :: String -> String
mkErrorJson msg =
    "{\"status\":\"error\",\"code\":\"ffi_validation_error\",\"message\":" ++ jsonString msg ++ "}"

-- | Error envelope for `aletheia_parse_decimal`.  A precise `code` for
-- programmatic dispatch (`decimal_parse_failed` / `decimal_overflow`), the
-- human reason in `message` (the convention `mkErrorJson` uses), and the
-- offending `input` echoed back (structured-extra, like the bound-exceeded
-- `observed`/`limit` triple).  Every string field goes through `jsonString`:
-- `input` is user-controlled and may be non-ASCII, which `show` would render as
-- invalid JSON (see `jsonString`).
mkDecimalErrorJson :: String -> String -> String -> String
mkDecimalErrorJson code msg input =
    "{\"status\":\"error\",\"code\":" ++ jsonString code
    ++ ",\"message\":" ++ jsonString msg
    ++ ",\"input\":" ++ jsonString input
    ++ "}"

-- | Render the result of `parseDecimal` as the FFI wire string.  Success is
-- the bare `{"numerator":N,"denominator":D}` shape the bindings'
-- `decode_wire_rational` consumes; the pair is already in lowest terms with a
-- positive denominator (the `DecRat` canonical invariant; `toℚ` gives
-- denominator `2^a·5^b ≥ 1`).  `nothing` → a parse-failure envelope; a
-- numerator/denominator outside the Int64 wire range → an overflow envelope.
-- Int64 is the wire bound; the kernel rational is unbounded, so the bound
-- check lives here at the marshaling boundary (mirrors `mkAgdaRational`).
decimalResultJson :: String -> Maybe AgdaRational.T_ℚ_6 -> String
decimalResultJson input Nothing =
    mkDecimalErrorJson "decimal_parse_failed"
        "not a valid decimal literal: expected -?digits or -?digits.digits+ (at least one digit after '.'; no '+' sign, no leading '.', no exponent)"
        input
decimalResultJson input (Just q) =
    let num = AgdaRational.d_numerator_14 q
        den = AgdaRational.d_denominatorℕ_20 q
    in case (toIntegralSized num :: Maybe Int64, toIntegralSized den :: Maybe Int64) of
        (Just n, Just d) ->
            "{\"numerator\":" ++ show n ++ ",\"denominator\":" ++ show d ++ "}"
        _ -> mkDecimalErrorJson "decimal_overflow"
                "decimal numerator or denominator exceeds the Int64 wire range"
                input

-- | Typed FFI error carrying either a free-form string (legacy validation
-- messages) or a structured adversarial-input bound violation that mirrors
-- Agda's `Error.InputBoundExceeded` wire shape (R20 cluster I — AGDA-D-32.3).
-- The bound-kind discriminator is carried as the canonical wire code
-- (`"frame_byte_count"`, etc.) so the rendered JSON matches the Agda-side
-- `errorExtras` payload byte-for-byte.
data FFIError
    = FFIStringError String
    | FFIBoundExceeded String Int Int  -- bound_kind wire code, observed, limit

-- | CAN-FD maximum frame byte count, mirrored from Agda's
-- `Aletheia.Limits.max-frame-byte-count`.  Constant on both sides; the
-- mirror sidesteps importing the MAlonzo constant into the marshaling
-- layer where it would be a runtime-resolved Integer.
maxFrameByteCount :: Int
maxFrameByteCount = 64

-- | Render an FFIError as the canonical JSON error envelope.  For
-- `FFIBoundExceeded` the shape matches Agda's `responseToJSON` output
-- for `Error.InputBoundExceeded` exactly so binding-side parsers see a
-- single wire contract regardless of which leg of the FFI (JSON
-- protocol vs binary frame) triggered the rejection.
formatFFIError :: FFIError -> String
formatFFIError (FFIStringError msg) = mkErrorJson msg
formatFFIError (FFIBoundExceeded kind observed limit) =
    "{\"status\":\"error\",\"code\":\"input_bound_exceeded\""
    ++ ",\"message\":\"" ++ kind ++ " " ++ show observed
       ++ " exceeds limit " ++ show limit ++ "\""
    ++ ",\"bound_kind\":" ++ show kind
    ++ ",\"observed\":" ++ show observed
    ++ ",\"limit\":" ++ show limit
    ++ "}"

-- | DLC code to payload byte count (delegates to Agda — single source of truth).
dlcToBytes :: Word8 -> Int
dlcToBytes n = fromIntegral (AgdaDLC.d_dlcToBytes_6 (toInteger n))

-- | Decode an optional Bool from two C bytes: a presence flag and a value.
-- present == 0 → Nothing; present /= 0 → Just (value /= 0). Used to lift
-- the CAN-FD BRS/ESI bits from the binary FFI into Agda's `Maybe Bool`.
-- The kernel does not consume BRS/ESI; they are pass-through metadata for
-- bindings (R19 Phase 2 cluster 18 — AGDA-D-10.1 closure).
mkMaybeBool :: Word8 -> Word8 -> Maybe Bool
mkMaybeBool 0 _ = Nothing
mkMaybeBool _ v = Just (v /= 0)

-- | Validate DLC code (must be ≤ 15) and dataLen/DLC consistency.
--
-- R20 cluster I — AGDA-D-32.3.  The dataLen pre-check emits a typed
-- `FFIBoundExceeded "frame_byte_count" observed maxFrameByteCount` so
-- the binary FFI's bound rejection mirrors the JSON-side
-- `Error.InputBoundExceeded FrameByteCount …` emit from
-- `Aletheia.Protocol.Routing.parseBytePayload`.  Both surfaces produce
-- the identical wire envelope ({status, code: "input_bound_exceeded",
-- bound_kind: "frame_byte_count", observed, limit, message}); bindings
-- dispatch uniformly on `bound_kind`.  Order of checks:
--   1. dataLen overshoot (FrameByteCount, typed bound)
--   2. DLC out of range (legacy validation string)
--   3. dataLen / DLC inconsistency (legacy validation string)
validateDLCAndLen :: String -> Word8 -> Word8 -> Either FFIError Int
validateDLCAndLen ctx dlc dataLen
    | fromIntegral dataLen > maxFrameByteCount =
        Left $ FFIBoundExceeded "frame_byte_count"
                                (fromIntegral dataLen)
                                maxFrameByteCount
    | dlc > 15  = Left $ FFIStringError $
        ctx ++ ": DLC " ++ show dlc ++ " exceeds maximum (15)"
    | fromIntegral dataLen /= dlcToBytes dlc =
        Left $ FFIStringError $
            ctx ++ ": dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    | otherwise = Right (dlcToBytes dlc)

-- | Construct MAlonzo DLC from raw Integer. Caller validates ∈ [0,15].
mkAgdaDLC :: Integer -> AgdaDLC.T_DLC_18
mkAgdaDLC = AgdaDLC.C_mkDLC_28

-- | CAN ID exclusive upper bounds (single source of truth from Agda).
standardCanIdMax, extendedCanIdMax :: Integer
standardCanIdMax = AgdaCANConst.d_standard'45'can'45'id'45'max_6
extendedCanIdMax = AgdaCANConst.d_extended'45'can'45'id'45'max_8

-- | Construct MAlonzo CANId from raw C values, validating bounds.
-- The proof field on Standard/Extended is `.(…)` irrelevant in Agda — MAlonzo
-- erases it, so the constructor takes only the numeric ID.
mkAgdaCanId :: Word32 -> Word8 -> Either String AgdaFrame.T_CANId_8
mkAgdaCanId canId extended
    | extended /= 0 =
        if toInteger canId < extendedCanIdMax
        then Right $ AgdaFrame.C_Extended_16 (toInteger canId)
        else Left $ "extended CAN ID " ++ show canId ++ " out of range (max " ++ show (extendedCanIdMax - 1) ++ ")"
    | otherwise =
        if toInteger canId < standardCanIdMax
        then Right $ AgdaFrame.C_Standard_12 (toInteger canId)
        else Left $ "standard CAN ID " ++ show canId ++ " out of range (max " ++ show (standardCanIdMax - 1) ++ ")"

-- | Convert a list of Word8 to MAlonzo Vec Byte n (linked-list shape).
-- Word8 ∈ [0,255] already, so no % 256 needed (mod-identity-byte proof).
bytesToAgdaVec :: [Word8] -> AgdaVec.T_Vec_28
bytesToAgdaVec [] = AgdaVec.C_'91''93'_32
bytesToAgdaVec (b:bs) = AgdaVec.C__'8759'__38
    (unsafeCoerce (toInteger b)) (bytesToAgdaVec bs)

-- | Construct MAlonzo ℚ from (numerator, denominator), normalizing via gcd.
-- The raw constructor C_mkℚ_24 does NOT normalize, but Agda's ℚ comparison
-- assumes coprime numerator/denominator — non-coprime input causes silent bugs.
mkAgdaRational :: Int64 -> Int64 -> Either String AgdaRational.T_ℚ_6
mkAgdaRational num den
    | den <= 0  = Left $ "non-positive denominator " ++ show den
    | otherwise =
        let n = fromIntegral num :: Integer
            d = fromIntegral den :: Integer
            g = gcd (abs n) d
            n' = n `div` g
            d' = d `div` g
        in if gcd (abs n') d' /= 1
           then Left $ "mkAgdaRational: internal invariant violated — gcd not 1 after normalization ("
                    ++ show n' ++ "/" ++ show d' ++ ")"
           else Right $ AgdaRational.C_mkℚ_24 n' (d' - 1)

-- | Build MAlonzo List (ℕ × ℚ) from parallel C arrays.
mkSignalPairs :: [Word32] -> [Int64] -> [Int64] -> Either String [AgdaSigma.T_Σ_14]
mkSignalPairs (i:is) (n:ns) (d:ds) = do
    rat <- mkAgdaRational n d
    rest <- mkSignalPairs is ns ds
    Right $ AgdaSigma.C__'44'__32
        (unsafeCoerce (toInteger i))
        (unsafeCoerce rat)
        : rest
mkSignalPairs _ _ _ = Right []
