-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS_GHC -Wall -Wcompat #-}

-- | The structures the C entry points take by pointer, read and written where
-- `include/aletheia.h` lays them out.  hsc2hs compiles the header and writes
-- every offset, size and alignment below from the C compiler's own layout, so
-- this module holds no number of its own; the Haskell FFI passes no structure
-- by value, so each crosses as a `Ptr` and is read with `peek`.
module AletheiaFFI.Wire
    ( WireText (..)
    , Frame (..)
    , SignalValues (..)
    , Buffer (..)
    , pokeBufferData
    , pokeBufferErr
    , pokeBufferSize
    , WireUint128 (..)
    , WireRational (..)
    , Decimal (..)
    , pokeDecimalValue
    , pokeDecimalErr
    , TimeBound (..)
    , pokeTimeBoundMicroseconds
    , pokeTimeBoundErr
    , PropertyCheck (..)
    , pokePropertyCheckErr
    ) where

import Foreign.C.String (CString)
import Foreign.C.Types (CSize)
import Foreign.Ptr (Ptr)
import Foreign.Storable (Storable (..))
import Data.Word (Word8, Word32, Word64)

#include "aletheia.h"

-- | `struct aletheia_text`.
data WireText = WireText
    { textData :: !CString
    , textSize :: !CSize
    } deriving (Eq, Show)

instance Storable WireText where
    sizeOf _ = #{size struct aletheia_text}
    alignment _ = #{alignment struct aletheia_text}
    peek p = WireText
        <$> #{peek struct aletheia_text, data} p
        <*> #{peek struct aletheia_text, size} p
    poke p t = do
        #{poke struct aletheia_text, data} p (textData t)
        #{poke struct aletheia_text, size} p (textSize t)

-- | `struct aletheia_frame`.
data Frame = Frame
    { frameTimestamp  :: !Word64
    , frameData       :: !(Ptr Word8)
    , frameCanId      :: !Word32
    , frameExtended   :: !Word8
    , frameDlc        :: !Word8
    , frameDataLen    :: !Word8
    , frameBrsPresent :: !Word8
    , frameBrsValue   :: !Word8
    , frameEsiPresent :: !Word8
    , frameEsiValue   :: !Word8
    } deriving (Eq, Show)

instance Storable Frame where
    sizeOf _ = #{size struct aletheia_frame}
    alignment _ = #{alignment struct aletheia_frame}
    peek p = Frame
        <$> #{peek struct aletheia_frame, timestamp} p
        <*> #{peek struct aletheia_frame, data} p
        <*> #{peek struct aletheia_frame, can_id} p
        <*> #{peek struct aletheia_frame, extended} p
        <*> #{peek struct aletheia_frame, dlc} p
        <*> #{peek struct aletheia_frame, data_len} p
        <*> #{peek struct aletheia_frame, brs_present} p
        <*> #{peek struct aletheia_frame, brs_value} p
        <*> #{peek struct aletheia_frame, esi_present} p
        <*> #{peek struct aletheia_frame, esi_value} p
    poke p f = do
        #{poke struct aletheia_frame, timestamp} p (frameTimestamp f)
        #{poke struct aletheia_frame, data} p (frameData f)
        #{poke struct aletheia_frame, can_id} p (frameCanId f)
        #{poke struct aletheia_frame, extended} p (frameExtended f)
        #{poke struct aletheia_frame, dlc} p (frameDlc f)
        #{poke struct aletheia_frame, data_len} p (frameDataLen f)
        #{poke struct aletheia_frame, brs_present} p (frameBrsPresent f)
        #{poke struct aletheia_frame, brs_value} p (frameBrsValue f)
        #{poke struct aletheia_frame, esi_present} p (frameEsiPresent f)
        #{poke struct aletheia_frame, esi_value} p (frameEsiValue f)

-- | `struct aletheia_uint128`.
data WireUint128 = WireUint128
    { u128Lo :: !Word64
    , u128Hi :: !Word64
    } deriving (Eq, Show)

instance Storable WireUint128 where
    sizeOf _ = #{size struct aletheia_uint128}
    alignment _ = #{alignment struct aletheia_uint128}
    peek p = WireUint128
        <$> #{peek struct aletheia_uint128, lo} p
        <*> #{peek struct aletheia_uint128, hi} p
    poke p u = do
        #{poke struct aletheia_uint128, lo} p (u128Lo u)
        #{poke struct aletheia_uint128, hi} p (u128Hi u)

-- | `struct aletheia_rational`.
data WireRational = WireRational
    { ratNumerator   :: !WireUint128
    , ratDenominator :: !WireUint128
    , ratNegative    :: !Word8
    } deriving (Eq, Show)

instance Storable WireRational where
    sizeOf _ = #{size struct aletheia_rational}
    alignment _ = #{alignment struct aletheia_rational}
    peek p = WireRational
        <$> #{peek struct aletheia_rational, numerator} p
        <*> #{peek struct aletheia_rational, denominator} p
        <*> #{peek struct aletheia_rational, negative} p
    poke p r = do
        #{poke struct aletheia_rational, numerator} p (ratNumerator r)
        #{poke struct aletheia_rational, denominator} p (ratDenominator r)
        #{poke struct aletheia_rational, negative} p (ratNegative r)

-- | `struct aletheia_signal_values`.
data SignalValues = SignalValues
    { svIndices :: !(Ptr Word32)
    , svValues  :: !(Ptr WireRational)
    , svCount   :: !Word32
    } deriving (Eq, Show)

instance Storable SignalValues where
    sizeOf _ = #{size struct aletheia_signal_values}
    alignment _ = #{alignment struct aletheia_signal_values}
    peek p = SignalValues
        <$> #{peek struct aletheia_signal_values, indices} p
        <*> #{peek struct aletheia_signal_values, values} p
        <*> #{peek struct aletheia_signal_values, count} p
    poke p v = do
        #{poke struct aletheia_signal_values, indices} p (svIndices v)
        #{poke struct aletheia_signal_values, values} p (svValues v)
        #{poke struct aletheia_signal_values, count} p (svCount v)

-- | `struct aletheia_buffer`.  The entries write its fields one at a time,
-- since a failure sets `err` and leaves the other two as the caller left them.
data Buffer = Buffer
    { bufData :: !(Ptr Word8)
    , bufErr  :: !CString
    , bufSize :: !Word32
    } deriving (Eq, Show)

instance Storable Buffer where
    sizeOf _ = #{size struct aletheia_buffer}
    alignment _ = #{alignment struct aletheia_buffer}
    peek p = Buffer
        <$> #{peek struct aletheia_buffer, data} p
        <*> #{peek struct aletheia_buffer, err} p
        <*> #{peek struct aletheia_buffer, size} p
    poke p b = do
        pokeBufferData p (bufData b)
        pokeBufferErr p (bufErr b)
        pokeBufferSize p (bufSize b)

pokeBufferData :: Ptr Buffer -> Ptr Word8 -> IO ()
pokeBufferData = #{poke struct aletheia_buffer, data}

pokeBufferErr :: Ptr Buffer -> CString -> IO ()
pokeBufferErr = #{poke struct aletheia_buffer, err}

pokeBufferSize :: Ptr Buffer -> Word32 -> IO ()
pokeBufferSize = #{poke struct aletheia_buffer, size}

-- | `struct aletheia_decimal`.  The entry writes one field or the other: the
-- value on success, the error on failure.
data Decimal = Decimal
    { decValue :: !WireRational
    , decErr   :: !CString
    } deriving (Eq, Show)

instance Storable Decimal where
    sizeOf _ = #{size struct aletheia_decimal}
    alignment _ = #{alignment struct aletheia_decimal}
    peek p = Decimal
        <$> #{peek struct aletheia_decimal, value} p
        <*> #{peek struct aletheia_decimal, err} p
    poke p d = do
        pokeDecimalValue p (decValue d)
        pokeDecimalErr p (decErr d)

pokeDecimalValue :: Ptr Decimal -> WireRational -> IO ()
pokeDecimalValue = #{poke struct aletheia_decimal, value}

pokeDecimalErr :: Ptr Decimal -> CString -> IO ()
pokeDecimalErr = #{poke struct aletheia_decimal, err}

-- | `struct aletheia_time_bound`.  The entry writes one field or the other:
-- the microseconds on success, the error on failure.
data TimeBound = TimeBound
    { tbMicroseconds :: !Word64
    , tbErr          :: !CString
    } deriving (Eq, Show)

instance Storable TimeBound where
    sizeOf _ = #{size struct aletheia_time_bound}
    alignment _ = #{alignment struct aletheia_time_bound}
    peek p = TimeBound
        <$> #{peek struct aletheia_time_bound, microseconds} p
        <*> #{peek struct aletheia_time_bound, err} p
    poke p t = do
        pokeTimeBoundMicroseconds p (tbMicroseconds t)
        pokeTimeBoundErr p (tbErr t)

pokeTimeBoundMicroseconds :: Ptr TimeBound -> Word64 -> IO ()
pokeTimeBoundMicroseconds = #{poke struct aletheia_time_bound, microseconds}

pokeTimeBoundErr :: Ptr TimeBound -> CString -> IO ()
pokeTimeBoundErr = #{poke struct aletheia_time_bound, err}

-- | `struct aletheia_property_check`.  The entry writes the error on failure
-- and nothing on success.
newtype PropertyCheck = PropertyCheck
    { pcErr :: CString
    } deriving (Eq, Show)

instance Storable PropertyCheck where
    sizeOf _ = #{size struct aletheia_property_check}
    alignment _ = #{alignment struct aletheia_property_check}
    peek p = PropertyCheck <$> #{peek struct aletheia_property_check, err} p
    poke p c = pokePropertyCheckErr p (pcErr c)

pokePropertyCheckErr :: Ptr PropertyCheck -> CString -> IO ()
pokePropertyCheckErr = #{poke struct aletheia_property_check, err}
