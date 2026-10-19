-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unused-imports #-}

-- | Marshaling helpers between raw C values and the builtins the kernel
-- entries take (Integer, Bool, lists, Maybe, Text).
--
-- The kernel decides every invariant a value it accepts carries; nothing here
-- builds a kernel value or decides what the kernel accepts.  What stays is
-- reading the caller's memory (text decoded as UTF-8) and formatting the
-- shim's own refusals (a NULL pointer, unreadable text) as the JSON error
-- envelope every entry answers with.
module AletheiaFFI.Marshal where

import Control.Exception (IOException, try)
import Data.Bits (toIntegralSized)
import Data.Char (ord)
import Data.Word (Word8, Word32)
import Foreign.C.String (CString)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, nullPtr)
import Foreign.Storable (peek, pokeByteOff)
import qualified Data.Text as T
import qualified Data.Text.Foreign as TF
import qualified GHC.Foreign as GF
import GHC.IO.Encoding (utf8)
import Numeric (showHex)
import Unsafe.Coerce (unsafeCoerce)

import AletheiaFFI.Wire (WireText (..))


-- | The caller's text decoded as UTF-8, whatever the process locale, or the
-- reason it is refused, in the order `aletheia.h` states for
-- `struct aletheia_text`.  The kernel reads every byte the caller sent or
-- none of them: no byte is dropped, replaced or cut off at a NUL.
peekText :: Ptr WireText -> IO (Either String String)
peekText p
    | p == nullPtr = pure (Left nullInput)
    | otherwise = do
        WireText bytes size <- peek p
        case toIntegralSized size :: Maybe Int of
            Nothing -> pure (Left "input size is out of range")
            Just 0 -> pure (Right "")
            Just n
                | bytes == nullPtr -> pure (Left nullInput)
                | otherwise -> checked <$> decoded (bytes, n)
  where
    nullInput = "null input"
    decoded cs = try (GF.peekCStringLen utf8 cs) :: IO (Either IOException String)
    checked (Left _) = Left "input is not valid UTF-8"
    checked (Right s)
        | '\NUL' `elem` s = Left "input contains a NUL byte"
        | otherwise = Right s

-- | A NUL-terminated UTF-8 copy of the text, whatever the process locale, in
-- memory the caller frees with `aletheia_free_str`.
newUtf8 :: T.Text -> IO CString
newUtf8 t = do
    let n = TF.lengthWord8 t
    p <- mallocBytes (n + 1) :: IO (Ptr Word8)
    TF.unsafeCopyToPtr t p
    pokeByteOff p n (0 :: Word8)
    pure (castPtr p)

-- | Encode a String as a JSON string literal (RFC 8259).  Haskell `show` is
-- NOT a JSON encoder: for a non-ASCII or control character it emits a `\NNN`
-- *decimal* escape (e.g. `show "€" == "\"\\8364\""`), which JSON rejects — JSON
-- only allows `\uXXXX` (hex).  A `show`-built envelope carrying user text (an
-- error `message` quoting the caller's bytes) is therefore invalid JSON the
-- bindings' decoders cannot parse.  This escapes the JSON-mandatory characters
-- and `\u`-escapes everything outside printable ASCII (with surrogate pairs for
-- astral code points), so the result is always valid, ASCII-safe JSON.
jsonString :: String -> String
jsonString s = '"' : concatMap esc s ++ ['"']
  where
    esc '"'  = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc '\b' = "\\b"
    esc '\f' = "\\f"
    esc c
        | c >= ' ' && c < '\DEL' = [c]                    -- printable ASCII
        | n <= 0xFFFF            = uEsc n                 -- BMP code point
        | otherwise             = uEsc hi ++ uEsc lo     -- astral: surrogate pair
      where
        n = ord c
        v = n - 0x10000
        hi = 0xD800 + (v `div` 0x400)
        lo = 0xDC00 + (v `mod` 0x400)
    uEsc x = let h = showHex x "" in "\\u" ++ replicate (4 - length h) '0' ++ h

-- | Format a validation error as a JSON error response string.  The text is
-- carried in `message` — the cross-binding error-envelope convention (Agda
-- `responseToJSON` and all four bindings read `message`; the per-signal
-- extraction object `{name,error}` is a different, narrower shape).
mkErrorJson :: String -> String
mkErrorJson msg =
    "{\"status\":\"error\",\"code\":\"ffi_validation_error\",\"message\":" ++ jsonString msg ++ "}"

-- | Decode an optional Bool from two C bytes: a presence flag and a value.
-- present == 0 → Nothing; present /= 0 → Just (value /= 0). Used to lift
-- the CAN-FD BRS/ESI bits from the binary FFI into the `Maybe Bool` the
-- kernel entries take.
-- The kernel does not consume BRS/ESI; they are pass-through metadata for
-- bindings.
mkMaybeBool :: Word8 -> Word8 -> Maybe Bool
mkMaybeBool 0 _ = Nothing
mkMaybeBool _ v = Just (v /= 0)
