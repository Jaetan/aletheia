-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Pins AletheiaFFI.Wire against the C compiler's layout of aletheia.h.
-- For each structure: the Storable size and alignment equal C's, and a value
-- C fills, read with `peek` and written with `poke` into zeroed memory, is
-- the value C filled, field by field.  A wrong offset on either side moves a
-- field's bytes and the C check names it.
module Main (main) where

import Control.Monad (unless, when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Foreign.C.Types (CSize (..), CUInt (..))
import Foreign.Marshal.Alloc (allocaBytesAligned)
import Foreign.Marshal.Utils (fillBytes)
import Foreign.Ptr (Ptr)
import Foreign.Storable (Storable (..))
import System.Exit (exitFailure)

import AletheiaFFI.Wire (Buffer, Decimal, Frame, SignalValues, WireRational)

foreign import ccall unsafe "abi_frame_size" cFrameSize :: IO CSize
foreign import ccall unsafe "abi_frame_align" cFrameAlign :: IO CSize
foreign import ccall unsafe "abi_values_size" cValuesSize :: IO CSize
foreign import ccall unsafe "abi_values_align" cValuesAlign :: IO CSize
foreign import ccall unsafe "abi_buffer_size" cBufferSize :: IO CSize
foreign import ccall unsafe "abi_buffer_align" cBufferAlign :: IO CSize
foreign import ccall unsafe "abi_rational_size" cRationalSize :: IO CSize
foreign import ccall unsafe "abi_rational_align" cRationalAlign :: IO CSize
foreign import ccall unsafe "abi_decimal_size" cDecimalSize :: IO CSize
foreign import ccall unsafe "abi_decimal_align" cDecimalAlign :: IO CSize
foreign import ccall unsafe "abi_fill_rational" cFillRational :: Ptr WireRational -> IO ()
foreign import ccall unsafe "abi_fill_decimal" cFillDecimal :: Ptr Decimal -> IO ()
foreign import ccall unsafe "abi_check_rational" cCheckRational :: Ptr WireRational -> IO CUInt
foreign import ccall unsafe "abi_check_decimal" cCheckDecimal :: Ptr Decimal -> IO CUInt
foreign import ccall unsafe "abi_fill_frame" cFillFrame :: Ptr Frame -> IO ()
foreign import ccall unsafe "abi_fill_values" cFillValues :: Ptr SignalValues -> IO ()
foreign import ccall unsafe "abi_fill_buffer" cFillBuffer :: Ptr Buffer -> IO ()
foreign import ccall unsafe "abi_check_frame" cCheckFrame :: Ptr Frame -> IO CUInt
foreign import ccall unsafe "abi_check_values" cCheckValues :: Ptr SignalValues -> IO CUInt
foreign import ccall unsafe "abi_check_buffer" cCheckBuffer :: Ptr Buffer -> IO CUInt

-- | Check one structure, recording a failure line per defect.
pin :: forall a. Storable a
    => IORef [String] -> String -> a
    -> IO CSize -> IO CSize -> (Ptr a -> IO ()) -> (Ptr a -> IO CUInt) -> IO ()
pin failures name proxy cSize cAlign cFill cCheck = do
    size <- fromIntegral <$> cSize
    align <- fromIntegral <$> cAlign
    let hsSize = sizeOf proxy
        hsAlign = alignment proxy
        failWith msg = modifyIORef' failures (++ [name ++ ": " ++ msg])
    when (hsSize /= size) $
        failWith ("sizeOf " ++ show hsSize ++ ", C sizeof " ++ show size)
    when (hsAlign /= align) $
        failWith ("alignment " ++ show hsAlign ++ ", C _Alignof " ++ show align)
    allocaBytesAligned size align $ \src ->
        allocaBytesAligned size align $ \dst -> do
            cFill src
            value <- peek src
            fillBytes dst 0 size
            poke dst (value :: a)
            bad <- cCheck dst
            unless (bad == 0) $
                failWith ("peek then poke moved the fields of mask " ++ show bad)

main :: IO ()
main = do
    failures <- newIORef []
    pin failures "aletheia_frame" (undefined :: Frame)
        cFrameSize cFrameAlign cFillFrame cCheckFrame
    pin failures "aletheia_signal_values" (undefined :: SignalValues)
        cValuesSize cValuesAlign cFillValues cCheckValues
    pin failures "aletheia_buffer" (undefined :: Buffer)
        cBufferSize cBufferAlign cFillBuffer cCheckBuffer
    pin failures "aletheia_rational" (undefined :: WireRational)
        cRationalSize cRationalAlign cFillRational cCheckRational
    pin failures "aletheia_decimal" (undefined :: Decimal)
        cDecimalSize cDecimalAlign cFillDecimal cCheckDecimal
    found <- readIORef failures
    mapM_ putStrLn found
    unless (null found) exitFailure
    putStrLn "abi-layout: every structure matches aletheia.h"
