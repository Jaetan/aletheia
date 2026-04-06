{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

-- | FFI exports for loading Aletheia as a shared library from Python/C++/Go.
--
-- This module wraps Agda-generated functions with C-callable FFI exports.
-- State is managed via StablePtr + IORef.
--
-- Entry points:
--   JSON input:
--     - aletheia_process()          : JSON string in, JSON string out
--   Binary input (no JSON parsing):
--     - aletheia_send_frame()       : Binary CAN data frame → JSON (streaming LTL)
--     - aletheia_send_error()       : CAN error event → JSON (acknowledged)
--     - aletheia_send_remote()      : CAN remote frame event → JSON (acknowledged)
--     - aletheia_extract_signals()  : Binary CAN frame → JSON (signal extraction)
--     - aletheia_build_frame()      : Signal index/value pairs → JSON (frame building)
--     - aletheia_update_frame()     : Frame + signal pairs → JSON (frame update)
--     - aletheia_start_stream()     : No args → JSON (state transition)
--     - aletheia_end_stream()       : No args → JSON (finalize + results)
--     - aletheia_format_dbc()       : No args → JSON (DBC export)
--
-- Lifecycle from language bindings:
--   1. hs_init()                -- Initialize GHC RTS (called once)
--   2. aletheia_init()          -- Create state handle
--   3. aletheia_process()       -- JSON commands (parseDBC, setProperties, validateDBC)
--   4. aletheia_start_stream()  -- Begin streaming
--   5. aletheia_send_frame()    -- Stream binary frames (hot path)
--   6. aletheia_end_stream()    -- Finalize and get results
--   7. aletheia_free_str()      -- Free each returned string
--   8. aletheia_close()         -- Free state handle
--   9. hs_exit()                -- Shutdown GHC RTS (called once)
module AletheiaFFI where

import Foreign.C.String (CString, newCString, peekCString)
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr)
import Foreign.Marshal.Alloc (free, mallocBytes)
import Foreign.Ptr (Ptr, plusPtr, castPtr)
import Foreign.Storable (poke)
import Foreign.Marshal.Array (peekArray)
import Control.Monad (when)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word16, Word32, Word64)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

-- MAlonzo-generated modules
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Agda.Builtin.Maybe as AgdaMaybe

-- | Opaque state handle exported to C/Python
type StateHandle = StablePtr (IORef AgdaState.T_StreamState_28)

-- | Create a new Aletheia state handle with initial state.
-- Returns: StablePtr that must be freed with aletheia_close.
foreign export ccall aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_28))
aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_28))
aletheia_init = do
    ref <- newIORef AgdaState.d_initialState_42
    newStablePtr ref

-- | Process a JSON line. Takes state handle and input CString.
-- Returns: CString that must be freed with aletheia_free_str.
-- The state handle is updated in-place.
foreign export ccall aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process :: StateHandle -> CString -> IO CString
aletheia_process statePtr inputCStr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    inputStr <- peekCString inputCStr
    let agdaInput = T.pack inputStr
    -- Call Agda processJSONLine: StreamState → String → Σ (StreamState × String)
    let result = Agda.d_processJSONLine_62 state agdaInput
    -- Extract pair components (MAlonzo Σ uses AgdaAny, need unsafeCoerce)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Process a binary CAN frame (no JSON parsing on input).
-- This is the hot-path entry point for streaming data frames.
-- Constructs MAlonzo types directly from raw C values, bypassing JSON entirely.
--
-- Arguments:
--   statePtr  : session state handle (from aletheia_init)
--   timestamp : frame timestamp in microseconds
--   canId     : CAN ID value (11-bit or 29-bit)
--   extended  : 0 = standard 11-bit, 1 = extended 29-bit
--   dlc       : DLC code (0-15)
--   dataPtr   : pointer to payload bytes
--   dataLen   : number of payload bytes (must equal dlcToBytes(dlc))
--
-- Returns: JSON response string (must be freed with aletheia_free_str)
foreign export ccall aletheia_send_frame
    :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8 -> IO CString
aletheia_send_frame :: StateHandle -> Word64 -> Word32 -> Word8 -> Word8
                    -> Ptr Word8 -> Word8 -> IO CString
aletheia_send_frame statePtr timestamp canId extended dlc dataPtr dataLen = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    -- Validate DLC/dataLen consistency (erased proof in Agda; must enforce at boundary)
    when (fromIntegral dataLen /= dlcToBytes dlc) $
        error $ "aletheia_send_frame: dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    -- Read raw bytes from C pointer
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    -- Construct MAlonzo types directly (no JSON, no Agda string parsing)
    let agdaCanId = mkAgdaCanId canId extended
    let agdaVec = bytesToAgdaVec bytes
    let agdaFrame = AgdaFrame.C_constructor_36 agdaCanId (toInteger dlc) agdaVec
    -- TimedFrame constructor: timestamp, payloadSize, frame, brs, esi
    -- (.dlcValid proof field is erased by MAlonzo — 5 runtime args)
    -- BRS/ESI are Nothing for CAN 2.0B frames; CAN-FD uses aletheia_send_event
    let agdaTF = AgdaTrace.C_constructor_34
            (toInteger timestamp) (toInteger dataLen) agdaFrame
            AgdaMaybe.C_nothing_18 AgdaMaybe.C_nothing_18
    -- Call Agda processFrameDirect: StreamState → TimedFrame → Σ (StreamState × String)
    let result = Agda.d_processFrameDirect_68 state (unsafeCoerce agdaTF)
    -- Extract pair components
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Send a CAN error event (no ID, no payload).
-- Error frames signal a bus error detected by a CAN controller.
-- The event is acknowledged without LTL evaluation (no payload for signal extraction).
foreign export ccall aletheia_send_error :: StateHandle -> Word64 -> IO CString
aletheia_send_error :: StateHandle -> Word64 -> IO CString
aletheia_send_error statePtr timestamp = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let agdaEvent = AgdaTrace.C_Error_40 (toInteger timestamp)
    let result = Agda.d_processEventDirect_74 state (unsafeCoerce agdaEvent)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Send a CAN remote frame event (ID but no payload).
-- Remote frames request transmission of the data frame with a matching ID.
-- CAN 2.0B only (deprecated in CAN-FD). Acknowledged without LTL evaluation.
foreign export ccall aletheia_send_remote
    :: StateHandle -> Word64 -> Word32 -> Word8 -> IO CString
aletheia_send_remote :: StateHandle -> Word64 -> Word32 -> Word8 -> IO CString
aletheia_send_remote statePtr timestamp canId extended = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let agdaCanId = mkAgdaCanId canId extended
    let agdaEvent = AgdaTrace.C_Remote_42 (toInteger timestamp) agdaCanId
    let result = Agda.d_processEventDirect_74 state (unsafeCoerce agdaEvent)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Convert a list of Word8 to MAlonzo Vec Byte n.
-- Constructs the same linked-list representation that MAlonzo generates for
-- Agda's Vec Byte n. Word8 values are already in [0,255], so no % 256 needed.
-- (Justified by mod-identity-byte proof in Protocol/FrameProcessor/Properties.agda)
bytesToAgdaVec :: [Word8] -> AgdaVec.T_Vec_28
bytesToAgdaVec [] = AgdaVec.C_'91''93'_32
bytesToAgdaVec (b:bs) = AgdaVec.C__'8759'__38
    (unsafeCoerce (toInteger b)) (bytesToAgdaVec bs)

-- ============================================================================
-- BINARY ENTRY POINTS (No JSON parsing on input)
-- ============================================================================

-- | Extract all signals from a binary CAN frame.
-- Same as aletheia_send_frame but for signal extraction (no timestamp needed).
foreign export ccall aletheia_extract_signals
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8 -> IO CString
aletheia_extract_signals :: StateHandle -> Word32 -> Word8 -> Word8
                        -> Ptr Word8 -> Word8 -> IO CString
aletheia_extract_signals statePtr canId extended dlc dataPtr dataLen = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    -- Validate DLC/dataLen consistency (erased proof in Agda; must enforce at boundary)
    when (fromIntegral dataLen /= dlcToBytes dlc) $
        error $ "aletheia_extract_signals: dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    let agdaCanId = mkAgdaCanId canId extended
    let agdaVec = bytesToAgdaVec bytes
    let result = Agda.d_processExtractDirect_94 state agdaCanId (toInteger dlc) (unsafeCoerce agdaVec)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Build a CAN frame from signal index-value pairs (no JSON/string parsing).
--
-- Signal values are passed as parallel arrays of (index, numerator, denominator).
-- Index is the 0-based position in the DBC message's signal list.
-- Value is the rational numerator/denominator (must have denominator > 0).
foreign export ccall aletheia_build_frame
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> IO CString
aletheia_build_frame :: StateHandle -> Word32 -> Word8 -> Word8
                    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                    -> IO CString
aletheia_build_frame statePtr canId extended dlc
    numSignals indicesPtr numsPtr densPtr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    let agdaCanId = mkAgdaCanId canId extended
    let signalPairs = mkSignalPairs indices nums dens
    let result = Agda.d_processBuildFrameDirect_108 state agdaCanId (toInteger dlc) signalPairs
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Update specific signals in a CAN frame by index (no JSON/string parsing).
foreign export ccall aletheia_update_frame
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> IO CString
aletheia_update_frame :: StateHandle -> Word32 -> Word8 -> Word8
                     -> Ptr Word8 -> Word8
                     -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                     -> IO CString
aletheia_update_frame statePtr canId extended dlc
    dataPtr dataLen numSignals indicesPtr numsPtr densPtr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    -- Validate DLC/dataLen consistency (erased proof in Agda; must enforce at boundary)
    when (fromIntegral dataLen /= dlcToBytes dlc) $
        error $ "aletheia_update_frame: dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    let agdaCanId = mkAgdaCanId canId extended
    let agdaVec = bytesToAgdaVec bytes
    let signalPairs = mkSignalPairs indices nums dens
    let result = Agda.d_processUpdateFrameDirect_122 state agdaCanId
                     (toInteger dlc) (unsafeCoerce agdaVec) signalPairs
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Start streaming mode (binary entry point, no JSON parsing).
foreign export ccall aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream :: StateHandle -> IO CString
aletheia_start_stream statePtr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let result = Agda.d_processStartStreamDirect_80 state
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | End streaming and finalize all properties (binary entry point).
foreign export ccall aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream :: StateHandle -> IO CString
aletheia_end_stream statePtr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let result = Agda.d_processEndStreamDirect_84 state
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Format currently-loaded DBC as JSON (binary entry point).
foreign export ccall aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc :: StateHandle -> IO CString
aletheia_format_dbc statePtr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    let result = Agda.d_processFormatDBCDirect_88 state
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- ============================================================================
-- MARSHALING HELPERS
-- ============================================================================

-- | DLC code to payload byte count (mirrors Aletheia.CAN.DLC.dlcToBytes).
dlcToBytes :: Word8 -> Int
dlcToBytes 9  = 12
dlcToBytes 10 = 16
dlcToBytes 11 = 20
dlcToBytes 12 = 24
dlcToBytes 13 = 32
dlcToBytes 14 = 48
dlcToBytes 15 = 64
dlcToBytes n  = fromIntegral n

-- | Construct MAlonzo CANId from raw C values.
-- Validates bounds at runtime: standard < 2048, extended < 536870912.
-- The proof argument (T (n <ᵇ max)) is supplied as unsafeCoerce () — valid
-- because we've just confirmed the bound, and MAlonzo compiles tt to a
-- nullary constructor equivalent to ().
mkAgdaCanId :: Word32 -> Word8 -> AgdaFrame.T_CANId_8
mkAgdaCanId canId extended
    | extended /= 0 =
        if canId < 536870912
        then AgdaFrame.C_Extended_16 (toInteger canId) (unsafeCoerce ())
        else error $ "mkAgdaCanId: extended CAN ID " ++ show canId
                     ++ " out of range (max 536870911)"
    | otherwise =
        if canId < 2048
        then AgdaFrame.C_Standard_12 (toInteger canId) (unsafeCoerce ())
        else error $ "mkAgdaCanId: standard CAN ID " ++ show canId
                     ++ " out of range (max 2047)"

-- | Construct MAlonzo ℚ from (numerator, denominator) integers.
-- GCD normalization is required: MAlonzo's C_mkℚ_24 is a raw data constructor
-- that does NOT normalize. Agda's ℚ equality and comparison assume coprime
-- numerator/denominator, so passing non-coprime values would cause silent bugs.
mkAgdaRational :: Int64 -> Int64 -> AgdaRational.T_ℚ_6
mkAgdaRational num den
    | den <= 0  = error ("mkAgdaRational: non-positive denominator " ++ show den)
    | otherwise =
        let n = fromIntegral num :: Integer
            d = fromIntegral den :: Integer
            g = gcd (abs n) d
        in AgdaRational.C_mkℚ_24 (n `div` g) (d `div` g - 1)

-- | Build MAlonzo List (ℕ × ℚ) from parallel C arrays.
mkSignalPairs :: [Word32] -> [Int64] -> [Int64] -> [AgdaSigma.T_Σ_14]
mkSignalPairs (i:is) (n:ns) (d:ds) =
    AgdaSigma.C__'44'__32
        (unsafeCoerce (toInteger i))
        (unsafeCoerce (mkAgdaRational n d))
    : mkSignalPairs is ns ds
mkSignalPairs _ _ _ = []

-- ============================================================================
-- BINARY OUTPUT ENTRY POINTS (No JSON serialization on output)
-- ============================================================================

-- | Walk MAlonzo Vec Byte, writing each byte to a buffer.
agdaVecToBuffer :: AgdaVec.T_Vec_28 -> Ptr Word8 -> IO ()
agdaVecToBuffer AgdaVec.C_'91''93'_32 _ = return ()
agdaVecToBuffer (AgdaVec.C__'8759'__38 x xs) ptr = do
    poke ptr (fromIntegral (unsafeCoerce x :: Integer) :: Word8)
    agdaVecToBuffer xs (ptr `plusPtr` 1)

-- | Dispatch on MAlonzo String ⊎ Vec Byte: write bytes to buffer (success)
-- or error string to out_err pointer (failure).
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

-- | Build a CAN frame, returning raw payload bytes (no JSON serialization).
-- Returns 0 on success (bytes written to out_buf), 1 on error (CString in out_err).
foreign export ccall aletheia_build_frame_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_build_frame_bin :: StateHandle -> Word32 -> Word8 -> Word8
                        -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                        -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_build_frame_bin statePtr canId extended dlc
    numSignals indicesPtr numsPtr densPtr outBuf outErr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    let agdaCanId = mkAgdaCanId canId extended
    let signalPairs = mkSignalPairs indices nums dens
    let result = Agda.d_processBuildFrameBin_138 state agdaCanId (toInteger dlc) signalPairs
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    writeIORef ref newState
    dispatchSumResult sumResult outBuf outErr

-- | Update a CAN frame, returning raw payload bytes (no JSON serialization).
-- Returns 0 on success (bytes written to out_buf), 1 on error (CString in out_err).
foreign export ccall aletheia_update_frame_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
    -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_update_frame_bin :: StateHandle -> Word32 -> Word8 -> Word8
                         -> Ptr Word8 -> Word8
                         -> Word32 -> Ptr Word32 -> Ptr Int64 -> Ptr Int64
                         -> Ptr Word8 -> Ptr CString -> IO Int8
aletheia_update_frame_bin statePtr canId extended dlc
    dataPtr dataLen numSignals indicesPtr numsPtr densPtr outBuf outErr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    -- Validate DLC/dataLen consistency (erased proof in Agda; must enforce at boundary)
    when (fromIntegral dataLen /= dlcToBytes dlc) $
        error $ "aletheia_update_frame_bin: dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    indices <- peekArray (fromIntegral numSignals) indicesPtr
    nums <- peekArray (fromIntegral numSignals) numsPtr
    dens <- peekArray (fromIntegral numSignals) densPtr
    let agdaCanId = mkAgdaCanId canId extended
    let agdaVec = bytesToAgdaVec bytes
    let signalPairs = mkSignalPairs indices nums dens
    let result = Agda.d_processUpdateFrameBin_172 state agdaCanId
                     (toInteger dlc) (unsafeCoerce agdaVec) signalPairs
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    writeIORef ref newState
    dispatchSumResult sumResult outBuf outErr

-- | Extract all signals returning packed binary (no JSON on output).
-- Returns 0 on success (buffer via out_buf/out_size), 1 on error (CString via out_err).
-- Wire format: see Main.agda processExtractBin documentation (canonical source).
-- Byte order: native (platform-dependent; little-endian on x86_64).
foreign export ccall aletheia_extract_signals_bin
    :: StateHandle -> Word32 -> Word8 -> Word8
    -> Ptr Word8 -> Word8
    -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin :: StateHandle -> Word32 -> Word8 -> Word8
                            -> Ptr Word8 -> Word8
                            -> Ptr (Ptr Word8) -> Ptr Word32 -> Ptr CString -> IO Int8
aletheia_extract_signals_bin statePtr canId extended dlc
    dataPtr dataLen outBufPtr outSizePtr outErr = do
    ref <- deRefStablePtr statePtr
    state <- readIORef ref
    -- Validate DLC/dataLen consistency (erased proof in Agda; must enforce at boundary)
    when (fromIntegral dataLen /= dlcToBytes dlc) $
        error $ "aletheia_extract_signals_bin: dataLen " ++ show dataLen ++ " != dlcToBytes " ++ show dlc
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    let agdaCanId = mkAgdaCanId canId extended
    let agdaVec = bytesToAgdaVec bytes
    let result = Agda.d_processExtractBin_244 state agdaCanId (toInteger dlc) (unsafeCoerce agdaVec)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
    let sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    writeIORef ref newState
    case sumResult of
        AgdaSum.C_inj'8321'_38 errAny -> do
            let errText = unsafeCoerce errAny :: T.Text
            errStr <- newCString (T.unpack errText)
            poke outErr errStr
            return 1
        AgdaSum.C_inj'8322'_42 ierAny -> do
            let ier = unsafeCoerce ierAny :: AgdaBatch.T_IndexedExtractionResults_126
            let vals = unsafeCoerce (AgdaBatch.d_values_134 ier) :: [AgdaSigma.T_Σ_14]
            let errs = unsafeCoerce (AgdaBatch.d_errors_136 ier) :: [AgdaSigma.T_Σ_14]
            let abss = AgdaBatch.d_absent_138 ier
            let nvals = length vals
            let nerrs = length errs
            let nabss = length abss
            let bufSize = 6 + nvals * 18 + nerrs * 3 + nabss * 2
            buf <- mallocBytes bufSize
            -- Header: 3 × u16
            poke (castPtr buf :: Ptr Word16) (fromIntegral nvals)
            poke (castPtr (buf `plusPtr` 2) :: Ptr Word16) (fromIntegral nerrs)
            poke (castPtr (buf `plusPtr` 4) :: Ptr Word16) (fromIntegral nabss)
            -- Values
            p1 <- writeExtrValues (buf `plusPtr` 6) vals
            -- Errors
            p2 <- writeExtrErrors p1 errs
            -- Absent
            _ <- writeExtrAbsent p2 abss
            poke outBufPtr buf
            poke outSizePtr (fromIntegral bufSize)
            return 0

-- | Write value entries: signal_index(u16) + numerator(i64) + denominator(i64).
-- Pattern-matches on MAlonzo constructor C_mkℚ_24 (stdlib 2.3 Data.Rational.Base).
-- FRAGILE: constructor name is MAlonzo-generated and may change with stdlib updates.
-- The denM1 field stores (denominator − 1); we add 1 back for the wire format.
writeExtrValues :: Ptr Word8 -> [AgdaSigma.T_Σ_14] -> IO (Ptr Word8)
writeExtrValues ptr [] = return ptr
writeExtrValues ptr (pair:rest) = do
    let idx = unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
    let rat = unsafeCoerce (AgdaSigma.d_snd_30 pair) :: AgdaRational.T_ℚ_6
    case rat of
        AgdaRational.C_mkℚ_24 num denM1 -> do
            poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
            poke (castPtr (ptr `plusPtr` 2) :: Ptr Int64) (fromIntegral num)
            poke (castPtr (ptr `plusPtr` 10) :: Ptr Int64) (fromIntegral (denM1 + 1))
            writeExtrValues (ptr `plusPtr` 18) rest

-- | Write error entries: signal_index(u16) + error_code(u8)
-- The error code is an ErrorCode ADT; convert to ℕ via errorCodeToℕ.
writeExtrErrors :: Ptr Word8 -> [AgdaSigma.T_Σ_14] -> IO (Ptr Word8)
writeExtrErrors ptr [] = return ptr
writeExtrErrors ptr (pair:rest) = do
    let idx = unsafeCoerce (AgdaSigma.d_fst_28 pair) :: Integer
    let code = AgdaBatch.d_errorCodeToℕ_124
                 (unsafeCoerce (AgdaSigma.d_snd_30 pair))
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    poke (ptr `plusPtr` 2) (fromIntegral code :: Word8)
    writeExtrErrors (ptr `plusPtr` 3) rest

-- | Write absent entries: signal_index(u16)
writeExtrAbsent :: Ptr Word8 -> [Integer] -> IO (Ptr Word8)
writeExtrAbsent ptr [] = return ptr
writeExtrAbsent ptr (idx:rest) = do
    poke (castPtr ptr :: Ptr Word16) (fromIntegral idx)
    writeExtrAbsent (ptr `plusPtr` 2) rest

-- ============================================================================
-- MEMORY MANAGEMENT
-- ============================================================================

-- | Free a string returned by any aletheia_* function.
foreign export ccall aletheia_free_str :: CString -> IO ()
aletheia_free_str :: CString -> IO ()
aletheia_free_str = free

-- | Free a binary buffer returned by aletheia_extract_signals_bin.
foreign export ccall aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf :: Ptr Word8 -> IO ()
aletheia_free_buf ptr = free ptr

-- | Close and free a state handle.
foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
