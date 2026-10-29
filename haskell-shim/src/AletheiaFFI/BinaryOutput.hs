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

import Foreign.C.String (CString)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Marshal.Array (pokeArray)
import Foreign.Ptr (Ptr, plusPtr, castPtr, nullPtr)
import Foreign.Storable (peek, poke)
import Data.Int (Int8)
import Data.Word (Word8, Word16, Word32, Word64)
import qualified Data.Text as T
import qualified Data.Text.Foreign as TF
import Unsafe.Coerce (unsafeCoerce)

import AletheiaFFI.Marshal (newUtf8, mkErrorJson, wireRational)
import AletheiaFFI.Wire (Buffer, WireRational (..), WireUint128 (..), bufData, pokeBufferErr, pokeBufferSize)
import qualified AletheiaFFI.Wire as Wire

import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.Error as AgdaError
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum

-- Stdlib-dependent MAlonzo constructor names used in this module, only ever
-- matched: Sum's C_inj'8321'_38 (inj₁) and C_inj'8322'_42 (inj₂).  The
-- Shakefile's check-erasure phony verifies them against MAlonzo output.

-- | Set the buffer's error to a JSON error envelope and answer 1.  The shim's
-- own refusals (a NULL pointer, a buffer too small) carry code
-- `ffi_validation_error`; the kernel's are its typed `Error`, rendered by
-- `formatErrorEnvelope`.  Either way a binding reads one shape.
shimErrorOut :: String -> Ptr Buffer -> IO Int8
shimErrorOut msg out = newUtf8 (T.pack (mkErrorJson msg)) >>= pokeBufferErr out >> return 1

kernelErrorText :: AgdaError.T_Error_484 -> IO CString
kernelErrorText err = newUtf8 (unsafeCoerce (AgdaBin.d_formatErrorEnvelope_12 err) :: T.Text)

kernelErrorOut :: AgdaError.T_Error_484 -> Ptr Buffer -> IO Int8
kernelErrorOut err out = kernelErrorText err >>= pokeBufferErr out >> return 1

-- | Dispatch a binary-output entry's `Error ⊎ List Byte`: on success write the
-- bytes into the caller's buffer, which must hold them, and set its size; on
-- refusal set its error to the kernel's envelope.
dispatchBytesResult :: String -> AgdaSum.T__'8846'__30 -> Ptr Buffer -> IO Int8
dispatchBytesResult _ (AgdaSum.C_inj'8321'_38 errAny) out = kernelErrorOut (unsafeCoerce errAny) out
dispatchBytesResult ctx (AgdaSum.C_inj'8322'_42 bytesAny) out = do
    let bytes = unsafeCoerce bytesAny :: [Integer]
        n = length bytes
    buf <- peek out
    if fromIntegral (Wire.bufSize buf) < n
      then shimErrorOut (ctx ++ ": out size " ++ show (Wire.bufSize buf) ++ " < " ++ show n ++ " frame bytes") out
      else if n > 0 && bufData buf == nullPtr
        then shimErrorOut (ctx ++ ": null out buffer") out
        else do
          pokeArray (bufData buf) (map fromIntegral bytes :: [Word8])
          pokeBufferSize out (fromIntegral n)
          return 0

-- | Split one (index, ℚ) value pair into its wire components.  The kernel's
-- categorisers keep a value only when both of its reduced components' magnitudes
-- fit 128 bits (`wireFits`, proven in CAN/Batch/Properties/WireFits.agda), so
-- `wireRational` writes every kept value exactly; a `Nothing` is unreachable
-- and refused by the caller.
-- Uses stable accessor functions (d_numerator_14, d_denominatorℕ_20): the
-- C_mkℚ_24 constructor name is stdlib-version-dependent, accessor names aren't.
splitValueEntry :: AgdaSigma.T_Σ_14 -> (Integer, Maybe WireRational)
splitValueEntry pair =
    let idx = unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
        rat = unsafeCoerce (AgdaSigma.d_snd_30 pair) :: AgdaRational.T_ℚ_6
    in (idx, wireRational (AgdaRational.d_numerator_14 rat) (AgdaRational.d_denominatorℕ_20 rat))

-- | Convert one kernel (index, (code, reason)) error entry to its wire
-- components via the kernel's u8 mapping.  The reason Text travels the wire
-- verbatim (UTF-8, delimited by the offsets table) — kernel-minted, never
-- synthesized here.
kernelErrorEntry :: AgdaSigma.T_Σ_14 -> (Integer, Integer, T.Text)
kernelErrorEntry pair =
    let codeReason = unsafeCoerce (AgdaSigma.d_snd_30 pair) :: AgdaSigma.T_Σ_14
    in ( unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
       , AgdaBatch.d_extractionErrorCodeToℕ_182 (unsafeCoerce (AgdaSigma.d_fst_28 codeReason))
       , unsafeCoerce (AgdaSigma.d_snd_30 codeReason) :: T.Text
       )

-- | Pack a PartitionedResults into a freshly-malloc'd buffer.
-- Wire format (canonical doc: Main.agda processExtractBin):
--   Header(3×u16: nVals,nErrs,nAbs + u32 reasonBytes) + Values(×35B)
--   + Errors(×3B) + Offsets((nErrs+1)×u32, cumulative into Reasons)
--   + Reasons(UTF-8 blob) + Absent(×2B).
-- The kernel refuses a value whose reduced components' magnitudes do not fit
-- 128 bits before it reaches here (its error entry carries code 3), so every
-- value splits; a `Nothing` from the split is unreachable and answered Left
-- rather than poked, keeping the writer total.
-- Fails loudly (Left) if the reason blob would exceed the u32 offset space:
-- unreachable with kernel-bounded reason strings, but total: never truncate,
-- never wrap.
-- Returns (buffer, total size). Caller frees via aletheia_free_buf.
packPartitionedResults :: AgdaBatch.T_PartitionedResults_10 -> IO (Either String (Ptr Word8, Int))
packPartitionedResults ier = do
    let vals = unsafeCoerce (AgdaBatch.d_values_22 ier) :: [AgdaSigma.T_Σ_14]
    let errs = unsafeCoerce (AgdaBatch.d_errors_24 ier) :: [AgdaSigma.T_Σ_14]
    let abss = unsafeCoerce (AgdaBatch.d_absent_26 ier) :: [Integer]
    let split    = map splitValueEntry vals
    let okVals   = [ (idx, r) | (idx, Just r) <- split ]
    let errEntries = map kernelErrorEntry errs
    let offsets  = scanl (+) 0 [ TF.lengthWord8 t | (_, _, t) <- errEntries ]
    let reasonBytes = last offsets
    let nvals = length okVals
    let nerrs = length errEntries
    let nabss = length abss
    if nvals /= length split
      then return (Left "extracted value does not fit the 128-bit wire words")
      else if toInteger reasonBytes > toInteger (maxBound :: Word32)
      then return (Left "extraction reason blob exceeds the u32 offset space")
      else do
        let bufSize = 10 + nvals * 35 + nerrs * 3 + (nerrs + 1) * 4
                         + reasonBytes + nabss * 2
        buf <- mallocBytes bufSize
        poke (castPtr buf :: Ptr Word16) (fromIntegral nvals)
        poke (castPtr (buf `plusPtr` 2) :: Ptr Word16) (fromIntegral nerrs)
        poke (castPtr (buf `plusPtr` 4) :: Ptr Word16) (fromIntegral nabss)
        poke (castPtr (buf `plusPtr` 6) :: Ptr Word32) (fromIntegral reasonBytes)
        p1 <- writeExtrValues (buf `plusPtr` 10) okVals
        p2 <- writeExtrErrors p1 [ (i, c) | (i, c, _) <- errEntries ]
        p3 <- writeExtrOffsets p2 offsets
        p4 <- writeExtrReasons p3 [ t | (_, _, t) <- errEntries ]
        _  <- writeExtrAbsent p4 abss
        return (Right (buf, bufSize))

-- | Write value entries: signal_index(u16) + negative(u8) + numerator(u128)
-- + denominator(u128), each u128 its low then its high u64.  Components
-- arrive as wire words (splitValueEntry); no conversion happens at the poke.
writeExtrValues :: Ptr Word8 -> [(Integer, WireRational)] -> IO (Ptr Word8)
writeExtrValues ptr [] = return ptr
writeExtrValues ptr ((idx, r):rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    poke (ptr `plusPtr` 2) (ratNegative r)
    pokeWords (ptr `plusPtr` 3) (ratNumerator r)
    pokeWords (ptr `plusPtr` 19) (ratDenominator r)
    writeExtrValues (ptr `plusPtr` 35) rest
  where
    pokeWords p (WireUint128 lo hi) = do
        poke (castPtr p :: Ptr Word64) lo
        poke (castPtr (p `plusPtr` 8) :: Ptr Word64) hi

-- | Write error entries: signal_index(u16) + error_code(u8).
writeExtrErrors :: Ptr Word8 -> [(Integer, Integer)] -> IO (Ptr Word8)
writeExtrErrors ptr [] = return ptr
writeExtrErrors ptr ((idx, code):rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    poke (ptr `plusPtr` 2) (fromIntegral code :: Word8)
    writeExtrErrors (ptr `plusPtr` 3) rest

-- | Write the cumulative reason offsets: (nErrors+1) × u32.
writeExtrOffsets :: Ptr Word8 -> [Int] -> IO (Ptr Word8)
writeExtrOffsets ptr [] = return ptr
writeExtrOffsets ptr (o:rest) = do
    poke (castPtr ptr :: Ptr Word32) (fromIntegral o)
    writeExtrOffsets (ptr `plusPtr` 4) rest

-- | Write the reason blob: each reason's UTF-8 bytes back to back — the
-- offsets table written just before delimits them.
writeExtrReasons :: Ptr Word8 -> [T.Text] -> IO (Ptr Word8)
writeExtrReasons ptr [] = return ptr
writeExtrReasons ptr (t:rest) = do
    TF.unsafeCopyToPtr t ptr
    writeExtrReasons (ptr `plusPtr` TF.lengthWord8 t) rest

-- | Write absent entries: signal_index(u16).
writeExtrAbsent :: Ptr Word8 -> [Integer] -> IO (Ptr Word8)
writeExtrAbsent ptr [] = return ptr
writeExtrAbsent ptr (idx:rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    writeExtrAbsent (ptr `plusPtr` 2) rest
