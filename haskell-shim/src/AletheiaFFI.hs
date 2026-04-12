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
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr)
import Foreign.Storable (poke)
import Foreign.Marshal.Array (peekArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word32, Word64)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Maybe as AgdaMaybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Aletheia.Main.JSON as AgdaJSON
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.Trace.Time as AgdaTime
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

import AletheiaFFI.Marshal
import AletheiaFFI.BinaryOutput

-- | Opaque state handle exported to C.
type StateHandle = StablePtr (IORef AgdaState.T_StreamState_28)

-- | Run an Agda function (state → Σ (state, JSON)) and write back to the
-- IORef. Centralizes the StablePtr/IORef/unsafeCoerce dance — every JSON
-- entry point uses this helper.
runJSON :: StateHandle -> (AgdaState.T_StreamState_28 -> AgdaSigma.T_Σ_14) -> IO CString
runJSON statePtr f = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let result = f state
    writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28)
    newCString (T.unpack (unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text))

-- | Return a JSON error response without calling Agda.
errorJSON :: String -> IO CString
errorJSON = newCString . mkErrorJson

-- ============================================================================
-- INITIALIZATION + JSON ENTRY POINT
-- ============================================================================

foreign export ccall aletheia_init :: IO StateHandle
aletheia_init :: IO StateHandle
aletheia_init = newIORef AgdaState.d_initialState_42 >>= newStablePtr

foreign export ccall aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process statePtr inputCStr = do
    inputStr <- peekCString inputCStr
    runJSON statePtr (\s -> AgdaJSON.d_processJSONLine_58 s (T.pack inputStr))

-- ============================================================================
-- BINARY-INPUT JSON ENTRY POINTS (binary in, JSON out)
-- ============================================================================

-- CAN-FD note: BRS/ESI flags are not part of the binary FFI protocol —
-- bindings drop them before calling. The Agda core operates on payload
-- bytes + DLC only.
foreign export ccall aletheia_send_frame
    :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8 -> IO CString
aletheia_send_frame :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
                    -> Ptr Word8 -> Word8 -> IO CString
aletheia_send_frame statePtr ts canId ext dlc dataPtr dataLen =
    case validateDLCAndLen "aletheia_send_frame" dlc dataLen >> mkAgdaCanId canId ext of
      Left err -> errorJSON err
      Right agdaCanId -> do
        bytes <- peekArray (fromIntegral dataLen) dataPtr
        let agdaTF = AgdaTrace.C_constructor_32
                (AgdaTime.C_mkTs_26 (toInteger ts))
                (toInteger dataLen)
                (AgdaFrame.C_constructor_36 agdaCanId (mkAgdaDLC (toInteger dlc)) (bytesToAgdaVec bytes))
                AgdaMaybe.C_nothing_18 AgdaMaybe.C_nothing_18
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
    case validateDLCAndLen "aletheia_extract_signals" dlc dataLen >> mkAgdaCanId canId ext of
      Left err -> errorJSON err
      Right agdaCanId -> do
        bytes <- peekArray (fromIntegral dataLen) dataPtr
        runJSON statePtr (\s -> AgdaBin.d_processExtractDirect_38 s agdaCanId
            (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes)))

foreign export ccall aletheia_build_frame
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64 -> IO CString
aletheia_build_frame :: StateHandle -> Word32 -> Word8 -> Word8
                    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64 -> IO CString
aletheia_build_frame statePtr canId ext dlc numSignals indicesPtr numsPtr densPtr = do
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    case (,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens of
      Left err -> errorJSON err
      Right (agdaCanId, pairs) -> runJSON statePtr (\s ->
        AgdaBin.d_processBuildFrameDirect_50 s agdaCanId (mkAgdaDLC (toInteger dlc)) pairs)

foreign export ccall aletheia_update_frame
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64 -> IO CString
aletheia_update_frame :: StateHandle -> Word32 -> Word8 -> Word8
                     -> Ptr Word8 -> Word8
                     -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64 -> IO CString
aletheia_update_frame statePtr canId ext dlc dataPtr dataLen
                     numSignals indicesPtr numsPtr densPtr = do
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    case validateDLCAndLen "aletheia_update_frame" dlc dataLen
         >> ((,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens) of
      Left err -> errorJSON err
      Right (agdaCanId, pairs) -> do
        bytes <- peekArray (fromIntegral dataLen) dataPtr
        runJSON statePtr (\s -> AgdaBin.d_processUpdateFrameDirect_62 s agdaCanId
            (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes)) pairs)

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
               -> (AgdaState.T_StreamState_28 -> AgdaSigma.T_Σ_14)
               -> Ptr Word8 -> Ptr CString -> IO Int8
runBinDispatch statePtr f outBuf outErr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let result = f state
    writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28)
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
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    case (,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens of
      Left err -> errorOut err outErr
      Right (agdaCanId, pairs) -> runBinDispatch statePtr
        (\s -> AgdaBin.d_processBuildFrameBin_98 s agdaCanId (mkAgdaDLC (toInteger dlc)) pairs)
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
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    case validateDLCAndLen "aletheia_update_frame_bin" dlc dataLen
         >> ((,) <$> mkAgdaCanId canId ext <*> mkSignalPairs indices nums dens) of
      Left err -> errorOut err outErr
      Right (agdaCanId, pairs) -> do
        bytes <- peekArray (fromIntegral dataLen) dataPtr
        runBinDispatch statePtr
            (\s -> AgdaBin.d_processUpdateFrameBin_112 s agdaCanId
                       (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes)) pairs)
            outBuf outErr

-- | Wire format documented in Main.agda processExtractBin (canonical source).
-- Header(3×u16) + Values(×18B) + Errors(×3B) + Absent(×2B). Native byte order.
foreign export ccall aletheia_extract_signals_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin :: StateHandle -> Word32 -> Word8 -> Word8
                            -> Ptr Word8 -> Word8
                            -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin statePtr canId ext dlc dataPtr dataLen outBufPtr outSizePtr outErr =
    case validateDLCAndLen "aletheia_extract_signals_bin" dlc dataLen >> mkAgdaCanId canId ext of
      Left err -> errorOut err outErr
      Right agdaCanId -> do
        bytes <- peekArray (fromIntegral dataLen) dataPtr
        ref <- deRefStablePtr statePtr
        state <- readIORef ref
        let result = AgdaBin.d_processExtractBin_128 state agdaCanId
                         (mkAgdaDLC (toInteger dlc)) (unsafeCoerce (bytesToAgdaVec bytes))
        writeIORef ref (unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28)
        case unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30 of
            AgdaSum.C_inj'8321'_38 errAny ->
                errorOut (T.unpack (unsafeCoerce errAny :: T.Text)) outErr
            AgdaSum.C_inj'8322'_42 ierAny -> do
                (buf, bufSize) <- packPartitionedResults
                    (unsafeCoerce ierAny :: AgdaBatch.T_PartitionedResults_10)
                poke outBufPtr buf
                poke outSizePtr (fromIntegral bufSize)
                return 0

-- ============================================================================
-- MEMORY MANAGEMENT
-- ============================================================================

foreign export ccall aletheia_free_str :: CString -> IO ()
aletheia_free_str :: CString -> IO ()
aletheia_free_str = free

foreign export ccall aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf = free

foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
