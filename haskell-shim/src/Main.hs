{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Wcompat -Widentities -Wincomplete-record-updates
                -Wincomplete-uni-patterns -Wpartial-fields -Wredundant-constraints #-}

module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..), hFlush, isEOF)
import System.IO.Unsafe (unsafeInterleaveIO)
import Unsafe.Coerce (unsafeCoerce)

-- Import Agda-generated code (Coinductive streaming interface)
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState as AgdaStreamState
import qualified MAlonzo.Code.Agda.Builtin.String as AgdaString
import qualified MAlonzo.Code.Codata.Sized.Colist as AgdaColist
import qualified MAlonzo.Code.Codata.Sized.Thunk as AgdaThunk

main :: IO ()
main = do
    -- Disable buffering for interactive use
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering

    -- Coinductive streaming mode (O(1) memory)
    coinductiveStreamLoop

-- Convert Text to Agda String (AgdaString.T_String_6 = Data.Text.Text)
textToAgdaString :: T.Text -> AgdaString.T_String_6
textToAgdaString = id

-- Build a lazy colist of input lines from stdin
-- Uses unsafeInterleaveIO for lazy evaluation
buildInputColist :: IO AgdaColist.T_Colist_30
buildInputColist = unsafeInterleaveIO $ do
    eof <- isEOF
    if eof
        then return AgdaColist.C_'91''93'_36  -- Empty colist []
        else do
            line <- TIO.getLine
            rest <- buildInputColist  -- Lazy recursive call
            -- Build colist cons: line ∷ (thunk rest)
            -- Thunk constructor takes a function (Size → Colist)
            let thunk = AgdaThunk.C_constructor_28 (\_ -> unsafeCoerce rest)
            return $ AgdaColist.C__'8759'__38 (unsafeCoerce (textToAgdaString line)) thunk

-- Consume output colist and print each response
-- Uses lazy pattern matching to consume colist on-demand
consumeOutputColist :: AgdaColist.T_Colist_30 -> IO ()
consumeOutputColist colist = case unsafeCoerce colist of
    -- Pattern match on colist constructors
    AgdaColist.C_'91''93'_36 -> return ()  -- Empty, done
    AgdaColist.C__'8759'__38 response restThunk -> do
        -- Print response
        TIO.putStrLn (unsafeCoerce response :: T.Text)
        hFlush stdout
        -- Force the thunk to get the rest of the colist, then recurse
        let restColist = AgdaThunk.d_force_26 (unsafeCoerce restThunk) (unsafeCoerce ())
        consumeOutputColist (unsafeCoerce restColist)

-- Coinductive streaming loop (O(1) memory)
-- Builds lazy input colist, calls processStream, consumes output colist
coinductiveStreamLoop :: IO ()
coinductiveStreamLoop = do
    -- Build lazy input colist
    inputColist <- buildInputColist

    -- Call Agda processStream (initial state + input colist → output colist)
    -- Use du_ version (erased Size parameter)
    let outputColist = Agda.du_processStream_104 AgdaStreamState.d_initialState_54 inputColist

    -- Consume and print output colist
    consumeOutputColist outputColist
