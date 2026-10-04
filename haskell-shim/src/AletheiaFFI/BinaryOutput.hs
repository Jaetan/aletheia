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
import Data.Bits (toIntegralSized)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word16, Word32)
import qualified Data.Text as T
import qualified Data.Text.Foreign as TF
import Unsafe.Coerce (unsafeCoerce)

import AletheiaFFI.Marshal (newUtf8, mkErrorJson)
import AletheiaFFI.Wire (Buffer, bufData, pokeBufferErr, pokeBufferSize)
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

kernelErrorOut :: AgdaError.T_Error_358 -> Ptr Buffer -> IO Int8
kernelErrorOut err out =
    newUtf8 (unsafeCoerce (AgdaBin.d_formatErrorEnvelope_12 err) :: T.Text) >>= pokeBufferErr out >> return 1

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

-- | u8 wire value for the encoder guard's reroute, read from the kernel
-- (`valueExceedsWireRangeCode`) so the shim neither hardcodes a wire constant
-- nor builds a kernel value to look one up.
valueExceedsWireRangeCode :: Integer
valueExceedsWireRangeCode = AgdaBatch.d_valueExceedsWireRangeCode_226

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

-- | Reason string for the encoder guard's reroute, pulled from the kernel
-- (`wireRangeReason` in CAN/BatchExtraction.agda) so the shim never
-- hardcodes reason text — same SSOT discipline as the reroute code above.
wireRangeReasonText :: T.Text
wireRangeReasonText = unsafeCoerce AgdaBatch.d_wireRangeReason_166 :: T.Text

-- | Convert one kernel (index, (code, reason)) error entry to its wire
-- components via the kernel's u8 mapping.  The reason Text travels the wire
-- verbatim (UTF-8, delimited by the offsets table) — kernel-minted, never
-- synthesized here.
kernelErrorEntry :: AgdaSigma.T_Σ_14 -> (Integer, Integer, T.Text)
kernelErrorEntry pair =
    let codeReason = unsafeCoerce (AgdaSigma.d_snd_30 pair) :: AgdaSigma.T_Σ_14
    in ( unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
       , AgdaBatch.d_extractionErrorCodeToℕ_160 (unsafeCoerce (AgdaSigma.d_fst_28 codeReason))
       , unsafeCoerce (AgdaSigma.d_snd_30 codeReason) :: T.Text
       )

-- | Pack a PartitionedResults into a freshly-malloc'd buffer.
-- Wire format (canonical doc: Main.agda processExtractBin):
--   Header(3×u16: nVals,nErrs,nAbs + u32 reasonBytes) + Values(×18B)
--   + Errors(×3B) + Offsets((nErrs+1)×u32, cumulative into Reasons)
--   + Reasons(UTF-8 blob) + Absent(×2B).
-- Encoder guard: values whose reduced numerator or denominator does not fit
-- the i64 wire slots are rerouted to the error stream with the kernel-minted
-- ValueExceedsWireRange code and wireRangeReason string (appended after the
-- kernel's own error entries; binding decoders key on signal index, not
-- segment order).  The counts and buffer size are computed AFTER the
-- partition so the header always matches the written segments.
-- Fails loudly (Left) if the reason blob would exceed the u32 offset space —
-- unreachable with kernel-bounded reason strings, but total: never truncate,
-- never wrap.
-- Returns (buffer, total size). Caller frees via aletheia_free_buf.
packPartitionedResults :: AgdaBatch.T_PartitionedResults_10 -> IO (Either String (Ptr Word8, Int))
packPartitionedResults ier = do
    let vals = unsafeCoerce (AgdaBatch.d_values_22 ier) :: [AgdaSigma.T_Σ_14]
    let errs = unsafeCoerce (AgdaBatch.d_errors_24 ier) :: [AgdaSigma.T_Σ_14]
    let abss = unsafeCoerce (AgdaBatch.d_absent_26 ier) :: [Integer]
    let split    = map splitValueEntry vals
    let okVals   = [ (idx, n, d) | (idx, Just (n, d)) <- split ]
    let overflow = [ (idx, valueExceedsWireRangeCode, wireRangeReasonText)
                   | (idx, Nothing) <- split ]
    let errEntries = map kernelErrorEntry errs ++ overflow
    let offsets  = scanl (+) 0 [ TF.lengthWord8 t | (_, _, t) <- errEntries ]
    let reasonBytes = last offsets
    let nvals = length okVals
    let nerrs = length errEntries
    let nabss = length abss
    if toInteger reasonBytes > toInteger (maxBound :: Word32)
      then return (Left "extraction reason blob exceeds the u32 offset space")
      else do
        let bufSize = 10 + nvals * 18 + nerrs * 3 + (nerrs + 1) * 4
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
