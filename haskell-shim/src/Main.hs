{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text.IO as TIO
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..))

-- This import will work after Agda compilation
-- import qualified MAlonzo.Code.Aletheia.Main as Agda

main :: IO ()
main = do
    -- Disable buffering for interactive use
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering

    -- Read input
    input <- TIO.getContents

    -- For now, just echo (will be replaced with Agda call)
    let output = "Echo: " <> input
    -- In Phase 2, this will be:
    -- let output = T.pack $ Agda.processCommand (T.unpack input)

    -- Write output
    TIO.putStrLn output
