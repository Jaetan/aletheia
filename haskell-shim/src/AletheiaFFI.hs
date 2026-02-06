{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

-- | FFI exports for loading Aletheia as a shared library from Python.
--
-- This module wraps the Agda-generated processJSONLine function with
-- C-callable FFI exports. State is managed via StablePtr + IORef.
--
-- Lifecycle from Python:
--   1. hs_init()           -- Initialize GHC RTS (called once)
--   2. aletheia_init()     -- Create state handle
--   3. aletheia_process()  -- Process JSON lines (called many times)
--   4. aletheia_free_str() -- Free each returned string
--   5. aletheia_close()    -- Free state handle
--   6. hs_exit()           -- Shutdown GHC RTS (called once)
module AletheiaFFI where

import Foreign.C.String (CString, newCString, peekCString)
import Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr)
import Foreign.Marshal.Alloc (free)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

-- MAlonzo-generated modules
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState as AgdaState
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma

-- | Opaque state handle exported to C/Python
type StateHandle = StablePtr (IORef AgdaState.T_StreamState_30)

-- | Create a new Aletheia state handle with initial state.
-- Returns: StablePtr that must be freed with aletheia_close.
foreign export ccall aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_30))
aletheia_init :: IO (StablePtr (IORef AgdaState.T_StreamState_30))
aletheia_init = do
    ref <- newIORef AgdaState.d_initialState_54
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
    let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_30
    let outputText = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    writeIORef ref newState
    newCString (T.unpack outputText)

-- | Free a string returned by aletheia_process.
foreign export ccall aletheia_free_str :: CString -> IO ()
aletheia_free_str :: CString -> IO ()
aletheia_free_str = free

-- | Close and free a state handle.
foreign export ccall aletheia_close :: StateHandle -> IO ()
aletheia_close :: StateHandle -> IO ()
aletheia_close = freeStablePtr
