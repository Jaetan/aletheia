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
import Foreign.Storable (Storable, peek, poke)
import Foreign.Marshal.Array (peekArray)
import Data.Bits (toIntegralSized)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Int (Int8)
import Data.Word (Word8)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.DBC.RationalRenderer as AgdaRR
import qualified MAlonzo.Code.Aletheia.DBC.TextParser.DecimalEntry as AgdaDE
import qualified MAlonzo.Code.Aletheia.LTL.TimeBoundEntry as AgdaTB
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Aletheia.Main.JSON as AgdaJSON
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
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
aletheia_init = newIORef AgdaState.d_initialState_44 >>= newStablePtr

foreign export ccall aletheia_process :: StateHandle -> Ptr WireText -> IO CString
aletheia_process :: StateHandle -> Ptr WireText -> IO CString
aletheia_process statePtr inputPtr = do
    input <- peekText inputPtr
    case input of
      Left reason -> errorJSON reason
      Right inputStr ->
        runJSON statePtr (\s -> AgdaJSON.d_processJSONLine_88 s (T.pack inputStr))

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
      Right f -> runJSON statePtr (\s -> AgdaBin.d_processErrorFrameRaw_178 s (toInteger (frameTimestamp f)))

foreign export ccall aletheia_send_remote :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_remote :: StateHandle -> Ptr Frame -> IO CString
aletheia_send_remote statePtr framePtr = do
    frameE <- peekFrame "aletheia_send_remote" framePtr
    case frameE of
      Left err -> errorJSON err
      Right f -> runJSON statePtr (\s -> AgdaBin.d_processRemoteFrameRaw_208 s
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
            in runJSON statePtr (\s -> AgdaBin.d_processExtractRaw_252 s canId extended dlc bytes)
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
-- parallel lists the kernel takes: the indices, the signed numerators and
-- the denominators.
peekSignalValues :: String -> Ptr SignalValues
                 -> IO (Either String ([Integer], [Integer], [Integer]))
peekSignalValues ctx valuesPtr
  | valuesPtr == nullPtr = pure (Left (ctx ++ ": null signal values"))
  | otherwise = do
      v <- peek valuesPtr
      let n = fromIntegral (svCount v)
      indicesE <- peekArrayChecked (ctx ++ " indices") n (svIndices v)
      ratsE <- peekArrayChecked (ctx ++ " values") n (svValues v)
      pure (do
        indices <- indicesE
        (nums, dens) <- unzip . map rationalParts <$> ratsE
        pure (map toInteger indices, nums, dens))

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
             (\s -> AgdaBin.d_processBuildFrameRaw_312 s canId extended dlc indices nums dens) out
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
                 (\s -> AgdaBin.d_processUpdateFrameRaw_462 s canId extended dlc bytes indices nums dens) out
  where
    ctx = "aletheia_update_frame_bin"

-- | Wire format documented in Main/Binary.agda processExtractBinRaw (canonical
-- source).  Header(3×u16 + u32 reasonBytes) + Values(×35B) + Errors(×3B)
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
                result = AgdaBin.d_processExtractBinRaw_572 state canId extended dlc bytes
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
-- The wire carries the sign apart from the magnitudes, so the denominator
-- is the natural `formatRational` takes and the numerator carries the sign.
foreign export ccall aletheia_format_rational :: Ptr WireRational -> IO CString
aletheia_format_rational :: Ptr WireRational -> IO CString
aletheia_format_rational valuePtr
  | valuePtr == nullPtr = pure nullPtr
  | otherwise = do
      (num, denom) <- rationalParts <$> peek valuePtr
      newUtf8 (unsafeCoerce (AgdaRR.d_formatRational_166 num denom) :: T.Text)

-- ============================================================================
-- DECIMAL → EXACT RATIONAL (kernel SSOT for decimal parsing)
-- ============================================================================

-- | Parse a decimal string into the exact rational it denotes: its numerator
-- and denominator on success, or a `{"status":"error",...}` envelope on
-- failure.
--
-- The kernel is the cross-binding single source of truth for a valid decimal:
-- every binding routes user decimal input through here rather than re-deriving
-- a float→rational heuristic, so neither the grammar nor the bound can drift
-- between languages.  `parseDecimal` answers `Error ⊎ WireRational`: a parse
-- failure, a partial parse and a component past the magnitude bound are each
-- a typed kernel error, rendered by `formatErrorEnvelope` as every kernel
-- refusal is; a `WireRational`'s magnitudes are at most 2^128 - 1 by its
-- erased proof, so `wireRational` writes every one, and its `Nothing` is
-- unreachable and refused rather than written.  The shim's own refusal of the
-- text (a NULL, an unreadable size, bytes that are not UTF-8, a NUL among
-- them) is `ffi_validation_error`, as on `aletheia_process`.  Every call
-- writes both fields of `out`: the rational and a NULL error, or a zero
-- rational and a JSON envelope the caller frees via `aletheia_free_str`.
foreign export ccall aletheia_parse_decimal :: Ptr WireText -> Ptr Decimal -> IO Int8
aletheia_parse_decimal :: Ptr WireText -> Ptr Decimal -> IO Int8
aletheia_parse_decimal inputPtr out
  | out == nullPtr = pure 1
  | otherwise = do
      input <- peekText inputPtr
      case input of
        Left reason -> errorJSON reason >>= refuse
        Right s ->
          case unsafeCoerce (AgdaDE.d_parseDecimal_52 (T.pack s)) :: AgdaSum.T__'8846'__30 of
            AgdaSum.C_inj'8321'_38 errAny -> kernelErrorText (unsafeCoerce errAny) >>= refuse
            AgdaSum.C_inj'8322'_42 ratAny -> do
              let rat = unsafeCoerce ratAny :: AgdaDE.T_WireRational_8
              case wireRational (AgdaDE.d_numerator_16 rat) (AgdaDE.d_denominator_18 rat) of
                Just value -> poke out (Decimal value nullPtr) >> pure 0
                Nothing -> errorJSON "aletheia_parse_decimal: the decimal does not fit the 128-bit wire words"
                             >>= refuse
  where
    refuse envelope = poke out (Decimal (WireRational zero zero 0) envelope) >> pure 1
    zero = WireUint128 0 0

-- ============================================================================
-- TIME BOUND AND PROPERTY CHECKS (the kernel's property parse, at build time)
-- ============================================================================

-- | Parse a microsecond text into the whole number of microseconds it denotes,
-- or the kernel's refusal, as a property's time bound is decided: the text is
-- read as `aletheia_parse_decimal` reads one, then `parseTimeBound` refuses a
-- negative or fractional bound with the property parse's own reason and one
-- past `max-time-bound`, 2^64 - 1, as a bound refusal.  The kernel answers a
-- natural at most that limit, so `toIntegralSized` writes every one and its
-- `Nothing` is unreachable and refused rather than written.  Every call writes
-- both fields of `out`, zero microseconds beside a refusal.
foreign export ccall aletheia_parse_time_bound :: Ptr WireText -> Ptr TimeBound -> IO Int8
aletheia_parse_time_bound :: Ptr WireText -> Ptr TimeBound -> IO Int8
aletheia_parse_time_bound inputPtr out
  | out == nullPtr = pure 1
  | otherwise = do
      input <- peekText inputPtr
      case input of
        Left reason -> errorJSON reason >>= refuse
        Right s ->
          case unsafeCoerce (AgdaTB.d_parseTimeBound_52 (T.pack s)) :: AgdaSum.T__'8846'__30 of
            AgdaSum.C_inj'8321'_38 errAny -> kernelErrorText (unsafeCoerce errAny) >>= refuse
            AgdaSum.C_inj'8322'_42 nAny ->
              case toIntegralSized (unsafeCoerce nAny :: Integer) of
                Just microseconds -> poke out (TimeBound microseconds nullPtr) >> pure 0
                Nothing -> errorJSON "aletheia_parse_time_bound: the time bound does not fit 64 bits"
                             >>= refuse
  where
    refuse envelope = poke out (TimeBound 0 envelope) >> pure 1

-- | Check one property's JSON text as set_properties reads a property, before
-- any session holds it: `checkPropertyText` reads it as a request is read,
-- then decides every field, ordering, denominator and time bound, and each
-- signal name as an identifier, leaving a name's presence in a DBC to
-- set_properties.  Every call writes the error: NULL on success.
foreign export ccall aletheia_check_property :: Ptr WireText -> Ptr PropertyCheck -> IO Int8
aletheia_check_property :: Ptr WireText -> Ptr PropertyCheck -> IO Int8
aletheia_check_property inputPtr out
  | out == nullPtr = pure 1
  | otherwise = do
      input <- peekText inputPtr
      case input of
        Left reason -> errorJSON reason >>= refuse
        Right s ->
          case unsafeCoerce (AgdaJSON.d_checkPropertyText_114 (T.pack s)) :: AgdaSum.T__'8846'__30 of
            AgdaSum.C_inj'8321'_38 errAny -> kernelErrorText (unsafeCoerce errAny) >>= refuse
            AgdaSum.C_inj'8322'_42 _ -> poke out (PropertyCheck nullPtr) >> pure 0
  where
    refuse envelope = poke out (PropertyCheck envelope) >> pure 1

foreign export ccall aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf = free

foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
