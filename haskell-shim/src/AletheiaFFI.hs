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

import Foreign.C.String (CString)
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr, castStablePtrToPtr)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.Storable (Storable, peek)
import Foreign.Marshal.Array (peekArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word32, Word64)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.DBC.RationalRenderer as AgdaRR
import qualified MAlonzo.Code.Aletheia.DBC.TextParser.DecimalEntry as AgdaDE
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Aletheia.Main.JSON as AgdaJSON
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum

import AletheiaFFI.Marshal
import AletheiaFFI.BinaryOutput
import AletheiaFFI.Wire

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
      newUtf8 (unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text)

-- | Return a JSON error response without calling Agda.
errorJSON :: String -> IO CString
errorJSON = newUtf8 . T.pack . mkErrorJson

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
-- zero length never dereferences, so `(NULL, 0)` is fine.  No bounds or
-- validity logic here: the kernel parses what was read.
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

foreign export ccall aletheia_process :: StateHandle -> Ptr WireText -> IO CString
aletheia_process :: StateHandle -> Ptr WireText -> IO CString
aletheia_process statePtr inputPtr = do
    input <- peekText inputPtr
    case input of
      Left reason -> errorJSON reason
      Right inputStr ->
        runJSON statePtr (\s -> AgdaJSON.d_processJSONLine_74 s (T.pack inputStr))

-- ============================================================================
-- BINARY-INPUT JSON ENTRY POINTS (binary in, JSON out)
-- ============================================================================
-- Each entry reads what the caller's struct holds and hands it to a kernel
-- `*Raw` entry as builtins; the kernel parses the identifier, the DLC, the
-- payload and the signal values, and refuses with its typed error.  The shim
-- refuses only what it cannot read: a NULL pointer where memory is needed.

-- | Read the frame the caller passed, refusing NULL.
peekFrame :: String -> Ptr Frame -> IO (Either String Frame)
peekFrame ctx framePtr
  | framePtr == nullPtr = pure (Left (ctx ++ ": null frame"))
  | otherwise           = Right <$> peek framePtr

-- | Read every byte `data_len` names from `data`, as the kernel takes them.
peekPayload :: String -> Frame -> IO (Either String [Integer])
peekPayload ctx f =
    fmap (map toInteger) <$>
      peekArrayChecked (ctx ++ " data") (fromIntegral (frameDataLen f)) (frameData f)

-- | The identifier, its extended flag and the DLC code, as the kernel takes them.
frameId :: Frame -> (Integer, Bool, Integer)
frameId f = (toInteger (frameCanId f), frameExtended f /= 0, toInteger (frameDlc f))

-- CAN-FD BRS/ESI each cross as a presence byte and a value byte, both zero
-- for a CAN 2.0B frame where the bits do not exist. The kernel does not
-- consume BRS/ESI; they are pass-through metadata exposed to bindings via
-- TimedFrame.
foreign export ccall aletheia_send_frame :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_frame :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_frame statePtr framePtr = do
    frameE <- peekFrame ctx framePtr
    case frameE of
      Left err -> errorJSON err
      Right f -> do
        bytesE <- peekPayload ctx f
        case bytesE of
          Left err -> errorJSON err
          Right bytes ->
            let (canId, extended, dlc) = frameId f
            in runJSON statePtr (\s -> AgdaBin.d_processFrameRaw_116 s
                   (toInteger (frameTimestamp f)) canId extended dlc bytes
                   (mkMaybeBool (frameBrsPresent f) (frameBrsValue f))
                   (mkMaybeBool (frameEsiPresent f) (frameEsiValue f)))
  where
    ctx = "aletheia_send_frame"

foreign export ccall aletheia_send_error :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_error :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_error statePtr framePtr = do
    frameE <- peekFrame "aletheia_send_error" framePtr
    case frameE of
      Left err -> errorJSON err
      Right f -> runJSON statePtr (\s -> AgdaBin.d_processErrorFrameRaw_176 s (toInteger (frameTimestamp f)))

foreign export ccall aletheia_send_remote :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_remote :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_remote statePtr framePtr = do
    frameE <- peekFrame "aletheia_send_remote" framePtr
    case frameE of
      Left err -> errorJSON err
      Right f -> runJSON statePtr (\s -> AgdaBin.d_processRemoteFrameRaw_188 s
                   (toInteger (frameTimestamp f)) (toInteger (frameCanId f)) (frameExtended f /= 0))

foreign export ccall aletheia_extract_signals :: StateHandle -> Ptr Frame -> IO CString
aletheia_extract_signals :: StateHandle -> Ptr Frame -> IO CString
aletheia_extract_signals statePtr framePtr = do
    frameE <- peekFrame ctx framePtr
    case frameE of
      Left err -> errorJSON err
      Right f -> do
        bytesE <- peekPayload ctx f
        case bytesE of
          Left err -> errorJSON err
          Right bytes ->
            let (canId, extended, dlc) = frameId f
            in runJSON statePtr (\s -> AgdaBin.d_processExtractRaw_230 s canId extended dlc bytes)
  where
    ctx = "aletheia_extract_signals"

foreign export ccall aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream statePtr = runJSON statePtr AgdaBin.d_processStartStreamDirect_28

foreign export ccall aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream statePtr = runJSON statePtr AgdaBin.d_processEndStreamDirect_32

foreign export ccall aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc statePtr = runJSON statePtr AgdaBin.d_processFormatDBCDirect_36

-- ============================================================================
-- BINARY-OUTPUT ENTRY POINTS (no JSON serialization on output)
-- ============================================================================

-- | Run a binary-output kernel entry and hand its `Error ⊎ List Byte` to
-- `dispatchBytesResult`, which writes the bytes or the refusal.
runBinDispatch :: String -> StateHandle
               -> (AgdaState.T_StreamState_32 -> AgdaSigma.T_Σ_14)
               -> Ptr Buffer -> IO Int8
runBinDispatch ctx statePtr f out
  | isNullState statePtr = shimErrorOut "null state handle" out
  | otherwise = do
      ref <- deRefStablePtr statePtr
      state <- readIORef ref
      let result = f state
      writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32)
      dispatchBytesResult ctx (unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30) out

-- | Read the signal values the caller passed, refusing NULL, as the three
-- parallel arrays the kernel takes.
peekSignalValues :: String -> Ptr SignalValues
                 -> IO (Either String ([Integer], [Integer], [Integer]))
peekSignalValues ctx valuesPtr
  | valuesPtr == nullPtr = pure (Left (ctx ++ ": null signal values"))
  | otherwise = do
      v <- peek valuesPtr
      let n = fromIntegral (svCount v)
      indicesE <- peekArrayChecked (ctx ++ " indices") n (svIndices v)
      numsE <- peekArrayChecked (ctx ++ " nums") n (svNumerators v)
      densE <- peekArrayChecked (ctx ++ " dens") n (svDenominators v)
      pure ((,,) <$> (map toInteger <$> indicesE) <*> (map toInteger <$> numsE) <*> (map toInteger <$> densE))

foreign export ccall aletheia_build_frame_bin
    :: StateHandle -> Ptr Frame -> Ptr SignalValues -> Ptr Buffer -> IO Int8
aletheia_build_frame_bin :: StateHandle -> Ptr Frame -> Ptr SignalValues -> Ptr Buffer -> IO Int8
aletheia_build_frame_bin statePtr framePtr valuesPtr out
  | out == nullPtr = return 1
  | otherwise = do
    frameE <- peekFrame ctx framePtr
    valuesE <- peekSignalValues ctx valuesPtr
    case (,) <$> frameE <*> valuesE of
      Left err -> shimErrorOut err out
      Right (f, (indices, nums, dens)) ->
        let (canId, extended, dlc) = frameId f
        in runBinDispatch ctx statePtr
             (\s -> AgdaBin.d_processBuildFrameRaw_290 s canId extended dlc indices nums dens) out
  where
    ctx = "aletheia_build_frame_bin"

foreign export ccall aletheia_update_frame_bin
    :: StateHandle -> Ptr Frame -> Ptr SignalValues -> Ptr Buffer -> IO Int8
aletheia_update_frame_bin :: StateHandle -> Ptr Frame -> Ptr SignalValues -> Ptr Buffer -> IO Int8
aletheia_update_frame_bin statePtr framePtr valuesPtr out
  | out == nullPtr = return 1
  | otherwise = do
    frameE <- peekFrame ctx framePtr
    valuesE <- peekSignalValues ctx valuesPtr
    case (,) <$> frameE <*> valuesE of
      Left err -> shimErrorOut err out
      Right (f, (indices, nums, dens)) -> do
        bytesE <- peekPayload ctx f
        case bytesE of
          Left err -> shimErrorOut err out
          Right bytes ->
            let (canId, extended, dlc) = frameId f
            in runBinDispatch ctx statePtr
                 (\s -> AgdaBin.d_processUpdateFrameRaw_440 s canId extended dlc bytes indices nums dens) out
  where
    ctx = "aletheia_update_frame_bin"

-- | Wire format documented in Main/Binary.agda processExtractBinRaw (canonical
-- source).  Header(3×u16 + u32 reasonBytes) + Values(×18B) + Errors(×3B)
-- + Offsets((nErrors+1)×u32) + Reasons(UTF-8 blob) + Absent(×2B).
-- Native byte order.
foreign export ccall aletheia_extract_signals_bin
    :: StateHandle -> Ptr Frame -> Ptr Buffer -> IO Int8
aletheia_extract_signals_bin :: StateHandle -> Ptr Frame -> Ptr Buffer -> IO Int8
aletheia_extract_signals_bin statePtr framePtr out
  | out == nullPtr = return 1
  | isNullState statePtr = shimErrorOut "null state handle" out
  | otherwise = do
    frameE <- peekFrame ctx framePtr
    case frameE of
      Left err -> shimErrorOut err out
      Right f -> do
        bytesE <- peekPayload ctx f
        case bytesE of
          Left err -> shimErrorOut err out
          Right bytes -> do
            ref <- deRefStablePtr statePtr
            state <- readIORef ref
            let (canId, extended, dlc) = frameId f
                result = AgdaBin.d_processExtractBinRaw_550 state canId extended dlc bytes
            writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32)
            case unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30 of
                AgdaSum.C_inj'8321'_38 errAny -> kernelErrorOut (unsafeCoerce errAny) out
                AgdaSum.C_inj'8322'_42 ierAny -> do
                    packedE <- packPartitionedResults
                        (unsafeCoerce ierAny :: AgdaBatch.T_PartitionedResults_10)
                    case packedE of
                        -- Unreachable with kernel-bounded reason strings
                        -- (u32 offset space), but total: fail loudly, never
                        -- truncate or wrap.
                        Left packErr -> shimErrorOut packErr out
                        Right (packed, packedSize) -> do
                            pokeBufferData out packed
                            pokeBufferSize out (fromIntegral packedSize)
                            return 0
  where
    ctx = "aletheia_extract_signals_bin"

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
foreign export ccall aletheia_format_rational :: Ptr WireRational -> IO CString
aletheia_format_rational :: Ptr WireRational -> IO CString
aletheia_format_rational valuePtr
  | valuePtr == nullPtr = pure nullPtr
  | otherwise = do
      WireRational num denom <- peek valuePtr
      let (n, d) | denom < 0 = (-num, -denom)
                 | otherwise = (num, denom)
          result = AgdaRR.d_formatRational_166 (toInteger n) (toInteger d)
      newUtf8 (unsafeCoerce result :: T.Text)

-- ============================================================================
-- DECIMAL → EXACT RATIONAL (kernel SSOT for decimal parsing)
-- ============================================================================

-- | Parse a decimal string into the exact rational it denotes: its numerator
-- and denominator on success, or a `{"status":"error",...}` envelope (code
-- `decimal_parse_failed` / `decimal_overflow`, with the offending `input`
-- echoed) on failure.
--
-- This is the cross-binding single source of truth for decimal→rational: every
-- binding routes user decimal input through here rather than re-deriving a
-- float→rational heuristic, so the accepted grammar cannot drift between
-- languages.  The kernel parser (`parseDecimal`) yields an unbounded ℚ; the
-- Int64-wire bound is enforced here at the marshaling boundary.  The rational
-- is written into `out`; a failure sets its
-- error to a JSON envelope the caller frees via `aletheia_free_str`.
foreign export ccall aletheia_parse_decimal :: Ptr WireText -> Ptr Decimal -> IO Int8
aletheia_parse_decimal :: Ptr WireText -> Ptr Decimal -> IO Int8
aletheia_parse_decimal inputPtr out
  | out == nullPtr = pure 1
  | otherwise = do
      input <- peekText inputPtr
      case input of
        Left reason -> refuse (mkDecimalErrorJson "decimal_parse_failed" reason "")
        Right s -> do
          let result = unsafeCoerce (AgdaDE.d_parseDecimal_16 (T.pack s))
                         :: Maybe AgdaRational.T_ℚ_6
          case decimalResult s result of
            Left envelope -> refuse envelope
            Right (n, d) -> pokeDecimalValue out (WireRational n d) >> pure 0
  where
    refuse envelope = newUtf8 (T.pack envelope) >>= pokeDecimalErr out >> pure 1

foreign export ccall aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf = free

foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
