-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unused-imports #-}

-- | Binary output writers for the FFI shim.
--
-- Walks MAlonzo data structures and packs them into raw byte buffers for
-- the *_bin entry points (build_frame_bin, update_frame_bin,
-- extract_signals_bin). Wire formats are documented in Main.agda
-- (canonical source) and mirrored across all language bindings.
module AletheiaFFI.BinaryOutput where

import Foreign.C.String (CString, newCString)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, plusPtr, castPtr)
import Foreign.Storable (poke)
import Data.Bits (toIntegralSized)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word16, Word32)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

-- Stdlib-dependent MAlonzo constructor names used in this module:
--   Vec:  C_'91''93'_32 (nil), C__'8759'__38 (cons)
--   Sum:  C_inj'8321'_38 (inj₁), C_inj'8322'_42 (inj₂)
-- The Shakefile's check-erasure phony verifies these against MAlonzo output.

-- | Walk MAlonzo Vec Byte, writing each byte to a contiguous buffer.
agdaVecToBuffer :: AgdaVec.T_Vec_28 -> Ptr Word8 -> IO ()
agdaVecToBuffer AgdaVec.C_'91''93'_32 _ = return ()
agdaVecToBuffer (AgdaVec.C__'8759'__38 x xs) ptr = do
    poke ptr (fromIntegral (unsafeCoerce x :: Integer) :: Word8)
    agdaVecToBuffer xs (ptr `plusPtr` 1)

-- | Dispatch on MAlonzo String ⊎ Vec Byte: write bytes (success) or set
-- error CString in out_err (failure). Used by build_frame_bin / update_frame_bin.
dispatchSumResult :: AgdaSum.T__'8846'__30 -> Ptr Word8 -> Ptr CString -> IO Int8
dispatchSumResult (AgdaSum.C_inj'8321'_38 errAny) _ outErr = do
    let errText = unsafeCoerce errAny :: T.Text
    errStr <- newCString (T.unpack errText)
    poke outErr errStr
    return 1
dispatchSumResult (AgdaSum.C_inj'8322'_42 vecAny) outBuf _ = do
    let vec = unsafeCoerce vecAny :: AgdaVec.T_Vec_28
    agdaVecToBuffer vec outBuf
    return 0

-- | u8 wire value for the encoder guard's reroute, pulled from the kernel
-- mapping (`extractionErrorCodeToℕ ValueExceedsWireRange`) so the shim never
-- hardcodes a wire constant — the code mints in the kernel enum.
valueExceedsWireRangeCode :: Integer
valueExceedsWireRangeCode =
    AgdaBatch.d_extractionErrorCodeToℕ_150 AgdaBatch.C_ValueExceedsWireRange_148

-- | Split one (index, ℚ) value pair into its wire components.  The kernel
-- rational is unbounded; the wire's rational slots are i64.  `toIntegralSized`
-- decides representability of BOTH components — `Nothing` means the exact
-- value cannot travel the wire and must become a per-signal error entry
-- (the encoder guard below), never a silently wrapping `fromIntegral`.
-- Reduction alone can push a component past the wire range even when every
-- DBC field and frame byte is in range, so this guard is unconditional.
-- Uses stable accessor functions (d_numerator_14, d_denominatorℕ_20) — the
-- C_mkℚ_24 constructor name is stdlib-version-dependent, accessor names aren't.
splitValueEntry :: AgdaSigma.T_Σ_14 -> (Integer, Maybe (Int64, Int64))
splitValueEntry pair =
    let idx = unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
        rat = unsafeCoerce (AgdaSigma.d_snd_30 pair) :: AgdaRational.T_ℚ_6
        num = AgdaRational.d_numerator_14 rat
        den = AgdaRational.d_denominatorℕ_20 rat
    in (idx, (,) <$> toIntegralSized num <*> toIntegralSized den)

-- | Convert one kernel (index, ExtractionErrorCode) error pair to its wire
-- pair via the kernel's u8 mapping.
kernelErrorEntry :: AgdaSigma.T_Σ_14 -> (Integer, Integer)
kernelErrorEntry pair =
    ( unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
    , AgdaBatch.d_extractionErrorCodeToℕ_150 (unsafeCoerce (AgdaSigma.d_snd_30 pair))
    )

-- | Pack a PartitionedResults into a freshly-malloc'd buffer.
-- Wire format: Header(3×u16: nVals,nErrs,nAbs) + Values(×18B) + Errors(×3B) + Absent(×2B).
-- Encoder guard: values whose reduced numerator or denominator does not fit
-- the i64 wire slots are rerouted to the error stream with the kernel-minted
-- ValueExceedsWireRange code (appended after the kernel's own error entries;
-- binding decoders key on signal index, not segment order).  The counts and
-- buffer size are computed AFTER the partition so the header always matches
-- the written segments.
-- Returns (buffer, total size). Caller frees via aletheia_free_buf.
packPartitionedResults :: AgdaBatch.T_PartitionedResults_10 -> IO (Ptr Word8, Int)
packPartitionedResults ier = do
    let vals = unsafeCoerce (AgdaBatch.d_values_22 ier) :: [AgdaSigma.T_Σ_14]
    let errs = unsafeCoerce (AgdaBatch.d_errors_24 ier) :: [AgdaSigma.T_Σ_14]
    let abss = unsafeCoerce (AgdaBatch.d_absent_26 ier) :: [Integer]
    let split    = map splitValueEntry vals
    let okVals   = [ (idx, n, d) | (idx, Just (n, d)) <- split ]
    let overflow = [ (idx, valueExceedsWireRangeCode) | (idx, Nothing) <- split ]
    let errPairs = map kernelErrorEntry errs ++ overflow
    let nvals = length okVals
    let nerrs = length errPairs
    let nabss = length abss
    let bufSize = 6 + nvals * 18 + nerrs * 3 + nabss * 2
    buf <- mallocBytes bufSize
    poke (castPtr buf :: Ptr Word16) (fromIntegral nvals)
    poke (castPtr (buf `plusPtr` 2) :: Ptr Word16) (fromIntegral nerrs)
    poke (castPtr (buf `plusPtr` 4) :: Ptr Word16) (fromIntegral nabss)
    p1 <- writeExtrValues (buf `plusPtr` 6) okVals
    p2 <- writeExtrErrors p1 errPairs
    _  <- writeExtrAbsent p2 abss
    return (buf, bufSize)

-- | Write value entries: signal_index(u16) + numerator(i64) + denominator(i64).
-- Components arrive pre-checked as Int64 (splitValueEntry) — no conversion
-- happens at the poke.
writeExtrValues :: Ptr Word8 -> [(Integer, Int64, Int64)] -> IO (Ptr Word8)
writeExtrValues ptr [] = return ptr
writeExtrValues ptr ((idx, num, den):rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    poke (castPtr (ptr `plusPtr` 2) :: Ptr Int64) num
    poke (castPtr (ptr `plusPtr` 10) :: Ptr Int64) den
    writeExtrValues (ptr `plusPtr` 18) rest

-- | Write error entries: signal_index(u16) + error_code(u8).
writeExtrErrors :: Ptr Word8 -> [(Integer, Integer)] -> IO (Ptr Word8)
writeExtrErrors ptr [] = return ptr
writeExtrErrors ptr ((idx, code):rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    poke (ptr `plusPtr` 2) (fromIntegral code :: Word8)
    writeExtrErrors (ptr `plusPtr` 3) rest

-- | Write absent entries: signal_index(u16).
writeExtrAbsent :: Ptr Word8 -> [Integer] -> IO (Ptr Word8)
writeExtrAbsent ptr [] = return ptr
writeExtrAbsent ptr (idx:rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    writeExtrAbsent (ptr `plusPtr` 2) rest
