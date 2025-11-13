{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text.IO as TIO
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..))
import System.Environment (getArgs)

-- Import Agda-generated code
import qualified MAlonzo.Code.Aletheia.Main as Agda

main :: IO ()
main = do
    -- Disable buffering for interactive use
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering

    -- Check for --debug flag
    args <- getArgs
    case args of
        ["--debug"] -> do
            -- Run debug mode (trace both parsers)
            TIO.putStrLn Agda.d_runDebug_40
        _ -> do
            -- Normal mode: read input and process commands
            input <- TIO.getContents
            let output = Agda.d_processCommand_28 input
            TIO.putStrLn output
