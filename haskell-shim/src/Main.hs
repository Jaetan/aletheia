{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..), hFlush, isEOF)
import System.Environment (getArgs)
import Control.Monad (when)
import Unsafe.Coerce (unsafeCoerce)

-- Import Agda-generated code (Phase 2B JSON streaming)
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState as AgdaStreamState
import qualified MAlonzo.Code.Agda.Builtin.String as AgdaString
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma

main :: IO ()
main = do
    -- Disable buffering for interactive use
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering

    -- Check for debug flag
    args <- getArgs
    case args of
        ["--debug"] -> do
            -- Run debug mode (DBC parser trace)
            TIO.putStrLn Agda.d_runDebug_46
        _ -> do
            -- Default: JSON streaming mode (Phase 2B)
            jsonStreamLoop AgdaStreamState.d_initialState_34

-- Convert Text to Agda String (AgdaString.T_String_6 = Data.Text.Text)
textToAgdaString :: T.Text -> AgdaString.T_String_6
textToAgdaString = id

-- JSON streaming loop (Phase 2B)
-- Reads JSON lines from stdin, processes them with Agda, writes JSON responses to stdout
jsonStreamLoop :: AgdaStreamState.T_StreamState_14 -> IO ()
jsonStreamLoop state = do
    eof <- isEOF
    when (not eof) $ do
        -- Read one JSON line
        line <- TIO.getLine

        -- Call Agda processJSONLine
        let result = Agda.d_processJSONLine_48 state (textToAgdaString line)

        -- Extract (newState, responseJSON) from Sigma type
        -- Note: MAlonzo Sigma accessors return AgdaAny, need unsafeCoerce for state
        let newState = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaStreamState.T_StreamState_14
        let responseJSON = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text

        -- Print response
        TIO.putStrLn responseJSON
        hFlush stdout

        -- Continue with new state
        jsonStreamLoop newState
