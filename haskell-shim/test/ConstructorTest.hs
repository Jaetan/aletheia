-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS_GHC -Wno-unused-imports -Wno-missing-signatures -Wno-missing-home-modules #-}

-- | Binary FFI Smoke Test (comprehensive unsafeCoerce drift guard)
--
-- End-to-end test of every FFI export, calling each one the way AletheiaFFI.hs
-- does: the raw entries take builtins (Integer, Bool, lists, Maybe), and the
-- results are read back through the same unsafeCoerce targets as
-- AletheiaFFI.hs / AletheiaFFI/BinaryOutput.hs. If a MAlonzo Σ-shape, sum
-- shape or record-field type drifts upstream, the corresponding coerce target
-- mismatches the GHC heap object and crashes here on first call (or on a
-- forced traversal of the result).
--
-- Coverage matches the function entries in haskell-shim/ffi-exports.snapshot
-- (the SSOT the check-ffi-exports gate diffs against): initialState and
-- processJSONLine in setup, then processStartStreamDirect, processFrameRaw,
-- processErrorFrameRaw, processRemoteFrameRaw, processExtractRaw,
-- processFormatDBCDirect, processBuildFrameRaw, processUpdateFrameRaw,
-- processExtractBinRaw, formatErrorEnvelope and processEndStreamDirect, and
-- the kernel's frame refusals through both answer channels.
--
-- This is NOT a substitute for the Agda proofs — handler correctness is proven
-- formally. This test exists solely to catch MAlonzo coerce-target drift at
-- the Haskell FFI trust boundary, which is outside Agda's reach.
--
-- The imports mirror AletheiaFFI.hs exactly (Main.JSON and Main.Binary
-- directly, not via the Main facade — the facade emits no symbols).
module Main where

import Data.List (isInfixOf)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)
import Data.Word (Word8)
import System.Exit (exitFailure, exitSuccess)

-- MAlonzo-generated modules (same imports as AletheiaFFI.hs).
import qualified MAlonzo.Code.Aletheia.Main.JSON as AgdaJSON
import qualified MAlonzo.Code.Aletheia.Main.Binary as AgdaBin
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState.Types as AgdaState
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Aletheia.Error as AgdaError
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational

-- ============================================================================
-- HELPERS — mirror AletheiaFFI.hs / BinaryOutput.hs call and coerce sites
-- ============================================================================

-- | Extract (state, response text) from a JSON-out Σ pair.
-- Mirrors runJSON in AletheiaFFI.hs.
extractResult :: AgdaSigma.T_Σ_14 -> (AgdaState.T_StreamState_32, T.Text)
extractResult result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32
        tx = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    in (st, tx)

-- | The JSON envelope of a binary-output refusal.  Mirrors kernelErrorOut in
-- BinaryOutput.hs.
envelope :: AgdaError.T_Error_358 -> T.Text
envelope err = unsafeCoerce (AgdaBin.d_formatErrorEnvelope_12 err) :: T.Text

-- | Extract (state, Either envelope bytes) from a binary-out Σ pair.
-- Mirrors runBinDispatch + dispatchBytesResult (BinaryOutput.hs).
extractSumBytes :: AgdaSigma.T_Σ_14 -> (AgdaState.T_StreamState_32, Either T.Text [Word8])
extractSumBytes result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32
        sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    in case sumResult of
         AgdaSum.C_inj'8321'_38 errAny -> (st, Left (envelope (unsafeCoerce errAny)))
         AgdaSum.C_inj'8322'_42 bytesAny -> (st, Right (map fromIntegral (unsafeCoerce bytesAny :: [Integer])))

-- | Extract (state, Either envelope PartitionedResults). Highest-risk path:
-- mirrors aletheia_extract_signals_bin in AletheiaFFI.hs.
extractSumIER :: AgdaSigma.T_Σ_14
              -> (AgdaState.T_StreamState_32, Either T.Text AgdaBatch.T_PartitionedResults_10)
extractSumIER result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_32
        sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    in case sumResult of
         AgdaSum.C_inj'8321'_38 errAny -> (st, Left (envelope (unsafeCoerce errAny)))
         AgdaSum.C_inj'8322'_42 ierAny -> (st, Right (unsafeCoerce ierAny :: AgdaBatch.T_PartitionedResults_10))

-- | Process a JSON command (used in setup).
processJSON :: AgdaState.T_StreamState_32 -> String
            -> (AgdaState.T_StreamState_32, T.Text)
processJSON state input = extractResult (AgdaJSON.d_processJSONLine_74 state (T.pack input))

-- | Walk PartitionedResults — forces field dispatch + full list traversals
-- of values / errors / absent. Mirrors packPartitionedResults in
-- BinaryOutput.hs. Returns concrete tuples so `show` can force every
-- embedded coerce.  An error entry is a nested Σ: (index, (code, reason)) —
-- forcing the reason Text is the drift guard for the reason-string slot the
-- binary wire's offsets segment transports.
walkPartitionedResults :: AgdaBatch.T_PartitionedResults_10
                       -> ([(Integer, Integer, Integer)], [(Integer, Integer, T.Text)], [Integer])
walkPartitionedResults ier =
    let vals = unsafeCoerce (AgdaBatch.d_values_22 ier) :: [AgdaSigma.T_Σ_14]
        errs = unsafeCoerce (AgdaBatch.d_errors_24 ier) :: [AgdaSigma.T_Σ_14]
        abss = unsafeCoerce (AgdaBatch.d_absent_26 ier) :: [Integer]
    in (map walkValuePair vals, map walkErrorPair errs, abss)
  where
    walkValuePair p =
        let idx = unsafeCoerce (AgdaSigma.d_fst_28 p) :: Integer
            rat = unsafeCoerce (AgdaSigma.d_snd_30 p) :: AgdaRational.T_ℚ_6
            num = AgdaRational.d_numerator_14 rat
            den = AgdaRational.d_denominatorℕ_20 rat
        in (idx, num, den)
    walkErrorPair p =
        let idx  = unsafeCoerce (AgdaSigma.d_fst_28 p) :: Integer
            codeReason = unsafeCoerce (AgdaSigma.d_snd_30 p) :: AgdaSigma.T_Σ_14
            code = AgdaBatch.d_extractionErrorCodeToℕ_160
                     (unsafeCoerce (AgdaSigma.d_fst_28 codeReason))
            reason = unsafeCoerce (AgdaSigma.d_snd_30 codeReason) :: T.Text
        in (idx, code, reason)

-- | A data frame through processFrameRaw: timestamp, identifier, extended
-- flag, DLC code, payload, and the CAN-FD BRS / ESI bits (`Nothing` for a
-- CAN 2.0B frame).  Mirrors aletheia_send_frame.
sendFrame :: AgdaState.T_StreamState_32 -> Integer -> Integer -> Bool -> Integer -> [Word8]
          -> Maybe Bool -> Maybe Bool -> (AgdaState.T_StreamState_32, T.Text)
sendFrame state ts canIdVal isExt dlc bytes brs esi =
    extractResult (AgdaBin.d_processFrameRaw_116 state ts canIdVal isExt dlc (map toInteger bytes) brs esi)

sendErrorEvent :: AgdaState.T_StreamState_32 -> Integer -> (AgdaState.T_StreamState_32, T.Text)
sendErrorEvent state ts = extractResult (AgdaBin.d_processErrorFrameRaw_176 state ts)

sendRemoteEvent :: AgdaState.T_StreamState_32 -> Integer -> Integer -> Bool
                -> (AgdaState.T_StreamState_32, T.Text)
sendRemoteEvent state ts canIdVal isExt =
    extractResult (AgdaBin.d_processRemoteFrameRaw_188 state ts canIdVal isExt)

extractDirect :: AgdaState.T_StreamState_32 -> Integer -> Bool -> Integer -> [Word8]
              -> (AgdaState.T_StreamState_32, T.Text)
extractDirect state canIdVal isExt dlc bytes =
    extractResult (AgdaBin.d_processExtractRaw_230 state canIdVal isExt dlc (map toInteger bytes))

-- | Zero-arg JSON-out paths.
startStream, endStream, formatDBC
    :: AgdaState.T_StreamState_32 -> (AgdaState.T_StreamState_32, T.Text)
startStream st = extractResult (AgdaBin.d_processStartStreamDirect_28 st)
endStream   st = extractResult (AgdaBin.d_processEndStreamDirect_32   st)
formatDBC   st = extractResult (AgdaBin.d_processFormatDBCDirect_36   st)

-- | Signal values as the three parallel arrays the raw entries take.
type Values = ([Integer], [Integer], [Integer])

buildFrameBin :: AgdaState.T_StreamState_32 -> Integer -> Bool -> Integer -> Values
              -> (AgdaState.T_StreamState_32, Either T.Text [Word8])
buildFrameBin state canIdVal isExt dlc (is, ns, ds) =
    extractSumBytes (AgdaBin.d_processBuildFrameRaw_290 state canIdVal isExt dlc is ns ds)

updateFrameBin :: AgdaState.T_StreamState_32 -> Integer -> Bool -> Integer -> [Word8] -> Values
               -> (AgdaState.T_StreamState_32, Either T.Text [Word8])
updateFrameBin state canIdVal isExt dlc bytes (is, ns, ds) =
    extractSumBytes (AgdaBin.d_processUpdateFrameRaw_440 state canIdVal isExt dlc (map toInteger bytes) is ns ds)

extractBin :: AgdaState.T_StreamState_32 -> Integer -> Bool -> Integer -> [Word8]
           -> (AgdaState.T_StreamState_32, Either T.Text AgdaBatch.T_PartitionedResults_10)
extractBin state canIdVal isExt dlc bytes =
    extractSumIER (AgdaBin.d_processExtractBinRaw_550 state canIdVal isExt dlc (map toInteger bytes))

-- ============================================================================
-- ASSERTIONS
-- ============================================================================

-- | Pass if `expected` appears as a substring of `actual`.
assertContains :: String -> String -> String -> IO Bool
assertContains label expected actual
    | expected `isInfixOf` actual = do
        putStrLn $ "  " ++ label ++ ": PASS"
        return True
    | otherwise = do
        putStrLn $ "  " ++ label ++ ": FAIL"
        putStrLn $ "    expected substring: " ++ expected
        putStrLn $ "    actual response:    " ++ actual
        return False

-- | Pass if `cond` is True; emit `detail` on failure.
assertTrue :: String -> String -> Bool -> IO Bool
assertTrue label _      True  = do
    putStrLn $ "  " ++ label ++ ": PASS"
    return True
assertTrue label detail False = do
    putStrLn $ "  " ++ label ++ ": FAIL"
    putStrLn $ "    " ++ detail
    return False

-- ============================================================================
-- MAIN
-- ============================================================================

main :: IO ()
main = do
    putStrLn "Binary FFI Smoke Test (comprehensive unsafeCoerce drift guard)"
    putStrLn "=========================================================================="
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Setup: load DBC + properties + start stream.
    --   exercises: d_initialState_50, d_processJSONLine_74,
    --              d_processStartStreamDirect_28
    -- ------------------------------------------------------------------------
    let state0 = AgdaState.d_initialState_50

    let dbcJSON = concat
            [ "{\"type\":\"command\",\"command\":\"parseDBC\",\"dbc\":"
            , "{\"version\":\"\",\"messages\":[{"
            , "\"name\":\"TestMsg\",\"id\":256,\"dlc\":8,\"sender\":\"ECU\","
            , "\"signals\":[{\"name\":\"Speed\",\"startBit\":0,\"length\":16,"
            , "\"byteOrder\":\"little_endian\",\"signed\":false,"
            , "\"factor\":1,\"offset\":0,\"minimum\":0,\"maximum\":65535,"
            , "\"unit\":\"kph\"},"
            -- Temp's narrow [0, 100] bound exists so an extraction can produce
            -- an ERROR entry (ValueOutOfBounds) — test 12b walks its nested
            -- (code, reason) pair, the reason-Text drift guard.
            , "{\"name\":\"Temp\",\"startBit\":16,\"length\":8,"
            , "\"byteOrder\":\"little_endian\",\"signed\":false,"
            , "\"factor\":1,\"offset\":0,\"minimum\":0,\"maximum\":100,"
            , "\"unit\":\"C\"}]}]}}"
            ]
    let (state1, resp1) = processJSON state0 dbcJSON
    putStrLn $ "Setup: Load DBC → " ++ T.unpack resp1

    let propsJSON = concat
            [ "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":["
            , "{\"operator\":\"always\",\"formula\":"
            , "{\"operator\":\"atomic\",\"predicate\":"
            , "{\"predicate\":\"lessThan\",\"signal\":\"Speed\",\"value\":1000}}}]}"
            ]
    let (state2, resp2) = processJSON state1 propsJSON
    putStrLn $ "Setup: Set properties → " ++ T.unpack resp2

    let (state3, resp3) = startStream state2
    putStrLn $ "Setup: Start stream → " ++ T.unpack resp3
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 1-4: d_processFrameRaw_12
    -- ------------------------------------------------------------------------
    putStrLn "Test 1: processFrameRaw — Speed=100, expect ack (100 < 1000)"
    let (state4, r1) = sendFrame state3 1000 256 False 8 [100, 0, 0, 0, 0, 0, 0, 0] Nothing Nothing
    let r1s = T.unpack r1
    putStrLn $ "  Response: " ++ r1s
    pass1 <- assertContains "Ack response" "\"status\": \"ack\"" r1s

    putStrLn "Test 2: processFrameRaw — Speed=1500, expect violation (1500 ≥ 1000)"
    let (_, r2) = sendFrame state4 2000 256 False 8 [220, 5, 0, 0, 0, 0, 0, 0] Nothing Nothing
    let r2s = T.unpack r2
    putStrLn $ "  Response: " ++ r2s
    pass2 <- assertContains "Violation response" "\"status\": \"fails\"" r2s

    putStrLn "Test 3: processFrameRaw — non-matching standard ID, expect ack"
    let (_, r3) = sendFrame state3 3000 512 False 8 [255, 255, 0, 0, 0, 0, 0, 0] Nothing Nothing
    let r3s = T.unpack r3
    putStrLn $ "  Response: " ++ r3s
    pass3 <- assertContains "Ack for non-matching ID" "\"status\": \"ack\"" r3s

    putStrLn "Test 4: processFrameRaw — extended CAN ID, expect ack"
    let (_, r4) = sendFrame state3 4000 256 True 8 [0, 0, 0, 0, 0, 0, 0, 0] Nothing Nothing
    let r4s = T.unpack r4
    putStrLn $ "  Response: " ++ r4s
    pass4 <- assertContains "Ack for extended ID" "\"status\": \"ack\"" r4s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 5-6: d_processErrorFrameRaw_176 / d_processRemoteFrameRaw_188
    -- ------------------------------------------------------------------------
    putStrLn "Test 5: processErrorFrameRaw — expect ack"
    let (_, r5) = sendErrorEvent state3 5000
    let r5s = T.unpack r5
    putStrLn $ "  Response: " ++ r5s
    pass5 <- assertContains "Error event ack" "\"status\": \"ack\"" r5s

    putStrLn "Test 6: processRemoteFrameRaw — expect ack"
    let (_, r6) = sendRemoteEvent state3 6000 256 False
    let r6s = T.unpack r6
    putStrLn $ "  Response: " ++ r6s
    pass6 <- assertContains "Remote event ack" "\"status\": \"ack\"" r6s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 7: d_processExtractRaw_38 (JSON-out)
    -- ------------------------------------------------------------------------
    putStrLn "Test 7: processExtractRaw — Speed=200, expect signal value in response"
    let (_, r7) = extractDirect state3 256 False 8 [200, 0, 0, 0, 0, 0, 0, 0]
    let r7s = T.unpack r7
    putStrLn $ "  Response: " ++ r7s
    pass7 <- assertContains "Extract response contains Speed" "Speed" r7s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 8: d_processFormatDBCDirect_36
    -- ------------------------------------------------------------------------
    putStrLn "Test 8: processFormatDBCDirect — expect formatted DBC containing TestMsg"
    let (_, r8) = formatDBC state3
    let r8s = T.unpack r8
    putStrLn $ "  Response: " ++ take 200 r8s ++ (if length r8s > 200 then "..." else "")
    pass8 <- assertContains "DBC format contains TestMsg" "TestMsg" r8s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 9-10: d_processBuildFrameRaw_72 (success + error)
    -- ------------------------------------------------------------------------
    putStrLn "Test 9: processBuildFrameRaw — Speed=300 at idx 0, expect inj₂ Vec"
    let (_, r9) = buildFrameBin state3 256 False 8 ([0], [300], [1])
    pass9 <- case r9 of
        Right bytes9 -> do
            putStrLn $ "  Bytes: " ++ show bytes9
            -- 300 = 0x012C; LE 16-bit → [0x2C, 0x01] in low bytes; rest zero.
            assertTrue "Build success — 8 bytes, low pair = (44, 1)"
                       ("got " ++ show bytes9)
                       (length bytes9 == 8 && take 2 bytes9 == [44, 1])
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False

    putStrLn "Test 10: processBuildFrameRaw — CAN ID 999 not in the DBC, expect inj₁ Error"
    let (_, r10) = buildFrameBin state3 999 False 8 ([0], [100], [1])
    pass10 <- case r10 of
        Left errText -> do
            -- T.unpack forces traversal; coerce-target mismatch crashes here.
            let errStr = T.unpack errText
            putStrLn $ "  Error envelope: " ++ errStr
            assertContains "Build error envelope carries frame_can_id_not_found"
                           "\"code\": \"frame_can_id_not_found\"" errStr
        Right bs -> do
            putStrLn $ "  Unexpected bytes: " ++ show bs
            return False
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 11: d_processUpdateFrameRaw_86
    -- ------------------------------------------------------------------------
    putStrLn "Test 11: processUpdateFrameRaw — Speed=500 over zeroed payload, expect inj₂ Vec"
    let baseBytes = [0, 0, 0, 0, 0, 0, 0, 0]
    let (_, r11) = updateFrameBin state3 256 False 8 baseBytes ([0], [500], [1])
    pass11 <- case r11 of
        Right bytes11 -> do
            putStrLn $ "  Bytes: " ++ show bytes11
            -- 500 = 0x01F4; LE → [0xF4, 0x01].
            assertTrue "Update success — 8 bytes, low pair = (244, 1)"
                       ("got " ++ show bytes11)
                       (length bytes11 == 8 && take 2 bytes11 == [244, 1])
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 12: d_processExtractBinRaw_550 (highest-risk: PartitionedResults coerce)
    -- ------------------------------------------------------------------------
    putStrLn "Test 12: processExtractBinRaw — Speed=400, Temp=0, expect inj₂ PartitionedResults with 2 values"
    let bytes12 = [144, 1, 0, 0, 0, 0, 0, 0]  -- 400 = 0x0190; LE → [0x90, 0x01].
    let (_, r12) = extractBin state3 256 False 8 bytes12
    pass12 <- case r12 of
        Right ier -> do
            let (vals, errs, abss) = walkPartitionedResults ier
            putStrLn $ "  values:  " ++ show vals
            putStrLn $ "  errors:  " ++ show errs
            putStrLn $ "  absent:  " ++ show abss
            -- Speed at signal index 0, raw=400, factor=1, offset=0 → 400/1;
            -- Temp at signal index 1, raw=0 → 0/1 (in bounds).
            -- d_denominatorℕ_20 returns the actual denominator (the record's
            -- denominator-1 field plus one), so 400/1 reads as (0, 400, 1).
            assertTrue "Extract success — values (0,400,1) and (1,0,1), 0 errors"
                       ("got vals=" ++ show vals ++ ", errs=" ++ show errs)
                       (vals == [(0, 400, 1), (1, 0, 1)] && null errs)
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False

    putStrLn "Test 12b: processExtractBinRaw — Temp=200 out of [0, 100], expect error entry with kernel reason"
    let bytes12b = [144, 1, 200, 0, 0, 0, 0, 0]  -- Temp raw byte = 200.
    let (_, r12b) = extractBin state3 256 False 8 bytes12b
    pass12b <- case r12b of
        Right ier -> do
            let (vals, errs, abss) = walkPartitionedResults ier
            putStrLn $ "  values:  " ++ show vals
            putStrLn $ "  errors:  " ++ show errs
            putStrLn $ "  absent:  " ++ show abss
            -- Forcing the reason Text is the drift guard for the nested
            -- (code, reason) Σ; the exact string pins the shared
            -- resultToString formatting (OutOfBounds wire code = 1).
            assertTrue "Extract error — (1, 1, \"value out of bounds: 200 not in [0, 100]\")"
                       ("got errs=" ++ show errs)
                       (errs == [(1, 1, T.pack "value out of bounds: 200 not in [0, 100]")]
                        && vals == [(0, 400, 1)])
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 13-15: CAN-FD BRS/ESI metadata pass-through
    -- BRS/ESI are stored on TimedFrame and never read by the kernel; the
    -- constructor path must accept Just True / Just False / Nothing for both
    -- bits without distorting downstream JSON output.
    -- ------------------------------------------------------------------------
    putStrLn "Test 13: processFrameRaw — CAN-FD frame with brs=Just True, esi=Just False"
    let (_, r13a) = sendFrame state3 7000 256 False 8 [200, 0, 0, 0, 0, 0, 0, 0] (Just True) (Just False)
    let r13as = T.unpack r13a
    putStrLn $ "  Response: " ++ r13as
    pass13 <- assertContains "Ack with brs=Just True / esi=Just False"
                             "\"status\": \"ack\"" r13as

    putStrLn "Test 14: processFrameRaw — CAN-FD frame with brs=Just False, esi=Just True"
    let (_, r14) = sendFrame state3 7001 256 False 8 [200, 0, 0, 0, 0, 0, 0, 0] (Just False) (Just True)
    let r14s = T.unpack r14
    putStrLn $ "  Response: " ++ r14s
    pass14 <- assertContains "Ack with brs=Just False / esi=Just True"
                             "\"status\": \"ack\"" r14s

    -- ------------------------------------------------------------------------
    -- Tests 16-19: the kernel's frame and value refusals, through both answer
    -- channels (a JSON-out entry and a binary-out entry's envelope).
    -- ------------------------------------------------------------------------
    putStrLn "Test 16: processFrameRaw — 7 bytes against DLC 8, expect parse_payload_length_mismatch"
    let (_, r16) = sendFrame state3 7100 256 False 8 [0, 0, 0, 0, 0, 0, 0] Nothing Nothing
    pass16 <- assertContains "Length refusal" "\"code\": \"parse_payload_length_mismatch\"" (T.unpack r16)

    putStrLn "Test 17: processExtractRaw — DLC 16, expect parse_dlc_code_out_of_range"
    let (_, r17) = extractDirect state3 256 False 16 []
    pass17 <- assertContains "DLC refusal" "\"code\": \"parse_dlc_code_out_of_range\"" (T.unpack r17)

    putStrLn "Test 18: processRemoteFrameRaw — standard ID 2048, expect parse_std_can_id_out_of_range"
    let (_, r18) = sendRemoteEvent state3 7200 2048 False
    pass18 <- assertContains "Identifier refusal" "\"code\": \"parse_std_can_id_out_of_range\"" (T.unpack r18)

    putStrLn "Test 19: processBuildFrameRaw — denominator 0, expect parse_non_positive_denominator envelope"
    let (_, r19) = buildFrameBin state3 256 False 8 ([0], [5], [0])
    pass19 <- case r19 of
        Left errText -> assertContains "Denominator refusal envelope"
                                       "\"code\": \"parse_non_positive_denominator\"" (T.unpack errText)
        Right bs -> do
            putStrLn $ "  Unexpected bytes: " ++ show bs
            return False
    putStrLn ""

    putStrLn "Test 15: processEndStreamDirect — expect summary response"
    let (_, r15) = endStream state3
    let r15s = T.unpack r15
    putStrLn $ "  Response: " ++ r15s
    pass15 <- assertContains "End stream response is JSON" "\"status\":" r15s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Summary
    -- ------------------------------------------------------------------------
    let checks = [pass1, pass2, pass3, pass4, pass5, pass6, pass7, pass8,
                  pass9, pass10, pass11, pass12, pass12b, pass13, pass14, pass15,
                  pass16, pass17, pass18, pass19]
    if and checks
        then putStrLn ("All " ++ show (length checks) ++ " checks passed.") >> exitSuccess
        else putStrLn "SOME CHECKS FAILED." >> exitFailure
