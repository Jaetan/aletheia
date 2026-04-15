{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unused-imports #-}

-- | Marshaling helpers between raw C values and MAlonzo-generated Agda types.
--
-- All conversion logic from primitive types (Word8, Word32, Int64) to the
-- corresponding MAlonzo constructors lives here. The FFI shim
-- (AletheiaFFI.hs) imports these and stays purely about the foreign-export
-- surface — no marshaling, no validation, no error formatting.
module AletheiaFFI.Marshal where

import Data.Int (Int64)
import Data.Word (Word8, Word32)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Aletheia.CAN.Constants as AgdaCANConst
import qualified MAlonzo.Code.Aletheia.CAN.DLC as AgdaDLC
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

-- | Format a validation error as a JSON error response string.
mkErrorJson :: String -> String
mkErrorJson msg = "{\"status\":\"error\",\"code\":\"ffi_validation_error\",\"error\":" ++ show msg ++ "}"

-- | DLC code to payload byte count (delegates to Agda — single source of truth).
dlcToBytes :: Word8 -> Int
dlcToBytes n = fromIntegral (AgdaDLC.d_dlcToBytes_6 (toInteger n))

-- | Validate DLC code (must be ≤ 15) and dataLen/DLC consistency.
validateDLCAndLen :: String -> Word8 -> Word8 -> Either String Int
validateDLCAndLen ctx dlc dataLen
    | dlc > 15  = Left $ ctx ++ ": DLC " ++ show dlc ++ " exceeds maximum (15)"
    | fromIntegral dataLen /= dlcToBytes dlc =
        Left $ ctx ++ ": dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    | otherwise = Right (dlcToBytes dlc)

-- | Construct MAlonzo DLC from raw Integer. Caller validates ∈ [0,15].
mkAgdaDLC :: Integer -> AgdaDLC.T_DLC_18
mkAgdaDLC = AgdaDLC.C_mkDLC_28

-- | CAN ID exclusive upper bounds (single source of truth from Agda).
standardCanIdMax, extendedCanIdMax :: Integer
standardCanIdMax = AgdaCANConst.d_standard'45'can'45'id'45'max_6
extendedCanIdMax = AgdaCANConst.d_extended'45'can'45'id'45'max_8

-- | Construct MAlonzo CANId from raw C values, validating bounds.
-- The proof argument (T (n <ᵇ max)) is unsafeCoerce () — valid because we
-- just confirmed the bound and MAlonzo compiles tt to a nullary ctor.
mkAgdaCanId :: Word32 -> Word8 -> Either String AgdaFrame.T_CANId_8
mkAgdaCanId canId extended
    | extended /= 0 =
        if toInteger canId < extendedCanIdMax
        then Right $ AgdaFrame.C_Extended_16 (toInteger canId) (unsafeCoerce ())
        else Left $ "extended CAN ID " ++ show canId ++ " out of range (max " ++ show (extendedCanIdMax - 1) ++ ")"
    | otherwise =
        if toInteger canId < standardCanIdMax
        then Right $ AgdaFrame.C_Standard_12 (toInteger canId) (unsafeCoerce ())
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
