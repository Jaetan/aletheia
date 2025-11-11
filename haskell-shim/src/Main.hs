{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text.IO as TIO
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..))

-- Import Agda-generated code
import qualified MAlonzo.Code.Aletheia.Main as Agda

main :: IO ()
main = do
    -- Disable buffering for interactive use
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering

    -- Read input (single line for now)
    input <- TIO.getLine

    -- Call Agda's processCommand function
    -- Agda String is represented as Data.Text.Text in MAlonzo
    let output = Agda.d_processCommand_28 input

    -- Write output
    TIO.putStrLn output
