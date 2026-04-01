{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

-- | FFI exports for loading Aletheia as a shared library from Python/C++/Go.
--
-- This module wraps the Agda-generated processJSONLine and processFrameDirect
-- functions with C-callable FFI exports. State is managed via StablePtr + IORef.
--
-- Two entry points for frame processing:
--   - aletheia_process()    : JSON string in, JSON string out (all commands)
--   - aletheia_send_frame() : Binary frame data in, JSON string out (hot path)
--
-- Lifecycle from language bindings:
--   1. hs_init()           -- Initialize GHC RTS (called once)
--   2. aletheia_init()     -- Create state handle
--   3. aletheia_process()  -- Process JSON lines (commands, non-hot-path)
--   3b. aletheia_send_frame() -- Send binary frame data (hot path)
--   4. aletheia_free_str() -- Free each returned string
--   5. aletheia_close()    -- Free state handle
--   6. hs_exit()           -- Shutdown GHC RTS (called once)
module AletheiaFFI where

import Foreign.C.String (CString, newCString, peekCString)
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr)
import Foreign.Marshal.Array (peekArray)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Word (Word8, Word32, Word64)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

-- MAlonzo-generated modules
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState as AgdaState
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

-- | Opaque state handle exported to C/Python
type StateHandle = StablePtr (IORef AgdaState.T_StreamState_34)

-- | Create a new Aletheia state handle with initial state.
-- Returns: StablePtr that must be freed with aletheia_close.
foreign export ccall aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_34))
aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_34))
aletheia_init = do
    ref <- newIORef AgdaState.d_initialState_58
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
    let result = Agda.d_processJSONLine_4 state agdaInput
    -- Extract pair components (MAlonzo Σ uses AgdaAny, need unsafeCoerce)
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_34
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
    -- Read raw bytes from C pointer
    bytes <- peekArray (fromIntegral dataLen) dataPtr
    -- Construct MAlonzo types directly (no JSON, no Agda string parsing)
    let agdaCanId = if extended /= 0
            then AgdaFrame.C_Extended_12 (toInteger canId)
            else AgdaFrame.C_Standard_10 (toInteger canId)
    let agdaVec = bytesToAgdaVec bytes
    let agdaFrame = AgdaFrame.C_constructor_32 agdaCanId (toInteger dlc) agdaVec
    -- TimedFrame constructor: timestamp, payloadSize, frame
    -- (.dlcValid proof field is erased by MAlonzo — only 3 runtime args)
    let agdaTF = AgdaTrace.C_constructor_26
            (toInteger timestamp) (toInteger dataLen) agdaFrame
    -- Call Agda processFrameDirect: StreamState → TimedFrame → Σ (StreamState × String)
    let result = Agda.d_processFrameDirect_58 state (unsafeCoerce agdaTF)
    -- Extract pair components
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_34
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

-- | Free a string returned by aletheia_process or aletheia_send_frame.
foreign export ccall aletheia_free_str :: CString -> IO ()
aletheia_free_str :: CString -> IO ()
aletheia_free_str = free

-- | Close and free a state handle.
foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
