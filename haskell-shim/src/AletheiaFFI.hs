-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unused-imports #-}

-- | FFI surface for the Aletheia shared library.
--
-- Thin wrapper that exposes Agda-generated functions via foreign-export ccall.
-- Marshaling logic lives in AletheiaFFI.Marshal; binary output writers live
-- in AletheiaFFI.BinaryOutput. This file is the entry-point surface only.
--
-- Lifecycle: hs_init → aletheia_init → (process | send_* | start/end_stream)*
-- → aletheia_close → hs_exit.  Strings returned by aletheia_* must be freed
-- via aletheia_free_str; binary buffers via aletheia_free_buf.
module AletheiaFFI where

import Foreign.C.String (CString, newCString, peekCString)
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr, castStablePtrToPtr)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.Storable (Storable, poke)
import Foreign.Marshal.Array (peekArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word32, Word64)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Aletheia.DBC.RationalRenderer as AgdaRR
import qualified MAlonzo.Code.Aletheia.DBC.TextParser.DecimalEntry as AgdaDE
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Aletheia.Main.JSON as AgdaJSON
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.Trace.Time as AgdaTime
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

import AletheiaFFI.Marshal
import AletheiaFFI.BinaryOutput

-- | Opaque state handle exported to C.
type StateHandle = StablePtr (IORef AgdaState.T_StreamState_32)

-- | Run an Agda function (state → Σ (state, JSON)) and write back to the
-- IORef. Centralizes the StablePtr/IORef/unsafeCoerce dance — every JSON
-- entry point uses this helper.
runJSON :: StateHandle -> (AgdaState.T_StreamState_32 -> AgdaSigma.T_Σ_14) -> IO CString
runJSON statePtr f
  | isNullState statePtr = errorJSON "null state handle"
  | otherwise = do
      ref <- deRefStablePtr statePtr
      state <- readIORef ref
      let result = f state
      writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32)
      newCString (T.unpack (unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text))

-- | Return a JSON error response without calling Agda.
errorJSON :: String -> IO CString
errorJSON = newCString . mkErrorJson

-- | Return a JSON error response from a typed FFIError.  Dispatches the
-- legacy free-form `FFIStringError` to `mkErrorJson` and the structured
-- `FFIBoundExceeded` to the bound-payload
-- envelope produced by `formatFFIError`.
errorJSONFor :: FFIError -> IO CString
errorJSONFor = newCString . formatFFIError

-- ============================================================================
-- NULL-POINTER GUARDS (trust-boundary hardening)
-- ============================================================================
-- The bindings hold the state as an opaque handle and construct payload
-- buffers per call; a correct binding never passes NULL.  But the FFI is the
-- shared trust boundary for all four bindings, and a NULL handle/buffer from a
-- buggy caller would `deRefStablePtr`/`peekArray`-deref NULL and SIGSEGV the
-- whole GHC runtime (a process crash, not a recoverable error).  These guards
-- turn NULL into a clean error response instead.  NULL only: an arbitrary
-- non-zero-but-invalid handle is undetectable, so we do not attempt it.

-- | True when the opaque state handle is NULL (e.g. ctypes `c_void_p(None)` →
-- a null pointer).  Dereferencing it would segfault.
isNullState :: StateHandle -> Bool
isNullState statePtr = castStablePtrToPtr statePtr == nullPtr

-- | `peekArray`, but a NULL pointer with a positive length (which would deref
-- NULL) is surfaced as `Left` for the caller to turn into a clean error.  A
-- zero length never dereferences, so `(NULL, 0)` is fine.  No bounds/validity
-- logic here — that stays in `validateDLCAndLen` / `mkSignalPairs`.
peekArrayChecked :: Storable a => String -> Int -> Ptr a -> IO (Either String [a])
peekArrayChecked what n ptr
  | n > 0 && ptr == nullPtr = pure (Left (what ++ ": null buffer pointer"))
  | otherwise               = Right <$> peekArray n ptr

-- ============================================================================
-- INITIALIZATION + JSON ENTRY POINT
-- ============================================================================

foreign export ccall aletheia_init :: IO StateHandle
aletheia_init :: IO StateHandle
aletheia_init = newIORef AgdaState.d_initialState_50 >>= newStablePtr

foreign export ccall aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process statePtr inputCStr
  | inputCStr == nullPtr = errorJSON "null input string"
  | otherwise = do
      inputStr <- peekCString inputCStr
      runJSON statePtr (\s -> AgdaJSON.d_processJSONLine_74 s (T.pack inputStr))

-- ============================================================================
-- BINARY-INPUT JSON ENTRY POINTS (binary in, JSON out)
-- ============================================================================

-- CAN-FD BRS/ESI: each flag is encoded as a pair of Word8 arguments —
-- `*_present` (0 = Nothing, non-zero = Just) and `*_value` (0 = False,
-- non-zero = True). Bindings send (0, 0) for CAN 2.0B frames where the
-- bits do not exist. The kernel does not consume BRS/ESI; they are
-- pass-through metadata exposed to bindings via TimedFrame.
foreign export ccall aletheia_send_frame
    :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Word8 -> Word8 -> Word8 -> Word8
    -> IO CString
aletheia_send_frame :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
                    -> Ptr Word8 -> Word8
                    -> Word8 -> Word8 -> Word8 -> Word8
                    -> IO CString
aletheia_send_frame statePtr ts canId ext dlc dataPtr dataLen
                    brsPres brsVal esiPres esiVal =
    case validateDLCAndLen "aletheia_send_frame" dlc dataLen of
      Left ffiErr -> errorJSONFor ffiErr
      Right _ -> case mkAgdaCanId canId ext of
        Left err -> errorJSON err
        Right agdaCanId -> do
          bytesE <- peekArrayChecked "aletheia_send_frame data" (fromIntegral dataLen) dataPtr
          case bytesE of
            Left err -> errorJSON err
            Right bytes -> do
              let agdaTF = AgdaTrace.C_constructor_32
                      (AgdaTime.C_mkTs_26 (toInteger ts))
                      (toInteger dataLen)
                      (AgdaFrame.C_constructor_36 agdaCanId (mkAgdaDLC (toInteger dlc)) (bytesToAgdaVec bytes))
                      (mkMaybeBool brsPres brsVal)
                      (mkMaybeBool esiPres esiVal)
              runJSON statePtr (\s -> AgdaBin.d_processFrameDirect_12 s (unsafeCoerce agdaTF))

foreign export ccall aletheia_send_error :: StateHandle -> Word64 -> IO CString
aletheia_send_error :: StateHandle -> Word64 -> IO CString
aletheia_send_error statePtr ts =
    runJSON statePtr (\s -> AgdaBin.d_processEventDirect_18 s
        (unsafeCoerce (AgdaTrace.C_Error_38 (AgdaTime.C_mkTs_26 (toInteger ts)))))

foreign export ccall aletheia_send_remote
    :: StateHandle -> Word64 -> Word32 -> Word8 -> IO CString
aletheia_send_remote :: StateHandle -> Word64 -> Word32 -> Word8 -> IO CString
aletheia_send_remote statePtr ts canId ext =
    case mkAgdaCanId canId ext of
      Left err -> errorJSON err
      Right agdaCanId -> runJSON statePtr (\s -> AgdaBin.d_processEventDirect_18 s
        (unsafeCoerce (AgdaTrace.C_Remote_40 (AgdaTime.C_mkTs_26 (toInteger ts)) agdaCanId)))

foreign export ccall aletheia_extract_signals
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8 -> IO CString
aletheia_extract_signals :: StateHandle -> Word32 -> Word8 -> Word8
                        -> Ptr Word8 -> Word8 -> IO CString
aletheia_extract_signals statePtr canId ext dlc dataPtr dataLen =
    case validateDLCAndLen "aletheia_extract_signals" dlc dataLen of
      Left ffiErr -> errorJSONFor ffiErr
      Right _ -> case mkAgdaCanId canId ext of
        Left err -> errorJSON err
        Right agdaCanId -> do
          bytesE <- peekArrayChecked "aletheia_extract_signals data" (fromIntegral dataLen) dataPtr
          case bytesE of
            Left err -> errorJSON err
            Right bytes -> runJSON statePtr (\s -> AgdaBin.d_processExtractDirect_38 s agdaCanId
                (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes)))

foreign export ccall aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream statePtr = runJSON statePtr AgdaBin.d_processStartStreamDirect_24

foreign export ccall aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream statePtr = runJSON statePtr AgdaBin.d_processEndStreamDirect_28

foreign export ccall aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc statePtr = runJSON statePtr AgdaBin.d_processFormatDBCDirect_32

-- ============================================================================
-- BINARY-OUTPUT ENTRY POINTS (no JSON serialization on output)
-- ============================================================================

-- | Run a binary-output Agda function: writes packed bytes to out_buf on
-- success, or sets out_err to a CString on failure. Returns 0/1.
runBinDispatch :: StateHandle
               -> (AgdaState.T_StreamState_32 -> AgdaSigma.T_Σ_14)
               -> Ptr Word8 -> Ptr CString -> IO Int8
runBinDispatch statePtr f outBuf outErr
  | isNullState statePtr = errorOut "null state handle" outErr
  | otherwise = do
      ref <- deRefStablePtr statePtr
      state <- readIORef ref
      let result = f state
      writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32)
      let sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
      dispatchSumResult sumResult outBuf outErr

-- | Set out_err to a freshly-allocated error CString and return 1.
errorOut :: String -> Ptr CString -> IO Int8
errorOut err outErr = newCString err >>= poke outErr >> return 1

foreign export ccall aletheia_build_frame_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_build_frame_bin :: StateHandle -> Word32 -> Word8 -> Word8
                        -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                        -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_build_frame_bin statePtr canId ext dlc numSignals indicesPtr numsPtr densPtr outBuf outErr = do
    let n = fromIntegral numSignals
    indicesE <- peekArrayChecked "aletheia_build_frame_bin indices" n indicesPtr
    numsE <- peekArrayChecked "aletheia_build_frame_bin nums" n numsPtr
    densE <- peekArrayChecked "aletheia_build_frame_bin dens" n densPtr
    case (,,) <$> indicesE <*> numsE <*> densE of
      Left err -> errorOut err outErr
      Right (indices, nums, dens) ->
        case (,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens of
          Left err -> errorOut err outErr
          Right (agdaCanId, pairs) -> runBinDispatch statePtr
            (\s -> AgdaBin.d_processBuildFrameBin_72 s agdaCanId (mkAgdaDLC (toInteger dlc)) pairs)
            outBuf outErr

foreign export ccall aletheia_update_frame_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_update_frame_bin :: StateHandle -> Word32 -> Word8 -> Word8
                         -> Ptr Word8 -> Word8
                         -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                         -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_update_frame_bin statePtr canId ext dlc dataPtr dataLen
                         numSignals indicesPtr numsPtr densPtr outBuf outErr = do
    let n = fromIntegral numSignals
    indicesE <- peekArrayChecked "aletheia_update_frame_bin indices" n indicesPtr
    numsE <- peekArrayChecked "aletheia_update_frame_bin nums" n numsPtr
    densE <- peekArrayChecked "aletheia_update_frame_bin dens" n densPtr
    case validateDLCAndLen "aletheia_update_frame_bin" dlc dataLen of
      Left ffiErr -> errorOut (formatFFIError ffiErr) outErr
      Right _ -> case (,,) <$> indicesE <*> numsE <*> densE of
        Left err -> errorOut err outErr
        Right (indices, nums, dens) -> case (,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens of
          Left err -> errorOut err outErr
          Right (agdaCanId, pairs) -> do
            bytesE <- peekArrayChecked "aletheia_update_frame_bin data" (fromIntegral dataLen) dataPtr
            case bytesE of
              Left err -> errorOut err outErr
              Right bytes -> runBinDispatch statePtr
                  (\s -> AgdaBin.d_processUpdateFrameBin_86 s agdaCanId
                             (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes)) pairs)
                  outBuf outErr

-- | Wire format documented in Main.agda processExtractBin (canonical source).
-- Header(3×u16 + u32 reasonBytes) + Values(×18B) + Errors(×3B)
-- + Offsets((nErrors+1)×u32) + Reasons(UTF-8 blob) + Absent(×2B).
-- Native byte order.
foreign export ccall aletheia_extract_signals_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin :: StateHandle -> Word32 -> Word8 -> Word8
                            -> Ptr Word8 -> Word8
                            -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin statePtr canId ext dlc dataPtr dataLen outBufPtr outSizePtr outErr
  | isNullState statePtr = errorOut "null state handle" outErr
  | otherwise =
    case validateDLCAndLen "aletheia_extract_signals_bin" dlc dataLen of
      Left ffiErr -> errorOut (formatFFIError ffiErr) outErr
      Right _ -> case mkAgdaCanId canId ext of
        Left err -> errorOut err outErr
        Right agdaCanId -> do
          bytesE <- peekArrayChecked "aletheia_extract_signals_bin data" (fromIntegral dataLen) dataPtr
          case bytesE of
            Left err -> errorOut err outErr
            Right bytes -> do
              ref <- deRefStablePtr statePtr
              state <- readIORef ref
              let result = AgdaBin.d_processExtractBin_102 state agdaCanId
                               (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes))
              writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32)
              case unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30 of
                  AgdaSum.C_inj'8321'_38 errAny ->
                      errorOut (T.unpack (unsafeCoerce errAny :: T.Text)) outErr
                  AgdaSum.C_inj'8322'_42 ierAny -> do
                      packedE <- packPartitionedResults
                          (unsafeCoerce ierAny :: AgdaBatch.T_PartitionedResults_10)
                      case packedE of
                          -- Unreachable with kernel-bounded reason strings
                          -- (u32 offset space), but total: fail loudly, never
                          -- truncate or wrap.
                          Left packErr -> errorOut packErr outErr
                          Right (buf, bufSize) -> do
                              poke outBufPtr buf
                              poke outSizePtr (fromIntegral bufSize)
                              return 0

-- ============================================================================
-- MEMORY MANAGEMENT
-- ============================================================================

foreign export ccall aletheia_free_str :: CString -> IO ()
aletheia_free_str :: CString -> IO ()
aletheia_free_str = free

-- ============================================================================
-- CROSS-BINDING-IDENTICAL RATIONAL PRETTY-PRINTER
-- ============================================================================

-- | Render `(numerator, denominator)` as a string identical across all
-- bindings.  Returns the GCD-reduced exact decimal expansion when the
-- value is a terminating decimal with `≤ 18` fractional digits, the
-- reduced `"<num>/<denom>"` literal otherwise (including the `k > 18`
-- pathological case), and the constant `"0"` for `denom = 0`.
--
-- Replaces three independent per-binding implementations (Python
-- `_format_rational`, Go `formatRational`, C++ `format_value(const
-- Rational&)`) with a single Agda kernel function.  Cross-binding
-- parity is proven in `Aletheia.DBC.RationalRenderer.Properties`.
--
-- Sign normalisation: Go and C++ allow `Rational{Numerator:int64,
-- Denominator:int64}` with negative denom (Python `Fraction` rejects
-- it on construction).  When the binding hands us `denom < 0`, move
-- the sign to the numerator before calling Agda — `_/_` requires a
-- positive ℕ denominator.
foreign export ccall aletheia_format_rational :: Int64 -> Int64 -> IO CString
aletheia_format_rational :: Int64 -> Int64 -> IO CString
aletheia_format_rational num denom =
    let (n, d) | denom < 0 = (-num, -denom)
               | otherwise = (num, denom)
        result = AgdaRR.d_formatRational_166 (toInteger n) (toInteger d)
    in newCString (T.unpack (unsafeCoerce result :: T.Text))

-- ============================================================================
-- DECIMAL → EXACT RATIONAL (kernel SSOT for decimal parsing)
-- ============================================================================

-- | Parse a decimal string into the exact rational it denotes, returning the
-- bindings' wire shape: `{"numerator":N,"denominator":D}` on success, or a
-- `{"status":"error",...}` envelope (code `decimal_parse_failed` /
-- `decimal_overflow`, with the offending `input` echoed) on failure.
--
-- This is the cross-binding single source of truth for decimal→rational: every
-- binding routes user decimal input through here rather than re-deriving a
-- float→rational heuristic, so the accepted grammar cannot drift between
-- languages.  The kernel parser (`parseDecimal`) yields an unbounded ℚ; the
-- Int64-wire bound is enforced here at the marshaling boundary (mirrors
-- `mkAgdaRational`).  Caller frees the returned CString via `aletheia_free_str`.
foreign export ccall aletheia_parse_decimal :: CString -> IO CString
aletheia_parse_decimal :: CString -> IO CString
aletheia_parse_decimal inputCStr
  | inputCStr == nullPtr =
      newCString (mkDecimalErrorJson "decimal_parse_failed" "null input string" "")
  | otherwise = do
      s <- peekCString inputCStr
      let result = unsafeCoerce (AgdaDE.d_parseDecimal_16 (T.pack s))
                     :: Maybe AgdaRational.T_ℚ_6
      newCString (decimalResultJson s result)

foreign export ccall aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf = free

foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
