{-# OPTIONS_GHC -Wno-unused-imports -Wno-missing-signatures -Wno-missing-home-modules #-}

-- | Binary FFI Smoke Test (R17-DEF-1: comprehensive unsafeCoerce drift guard)
--
-- End-to-end test of every FFI export, mirroring the unsafeCoerce dance from
-- AletheiaFFI.hs / AletheiaFFI/Marshal.hs / AletheiaFFI/BinaryOutput.hs. If a
-- MAlonzo Σ-shape, record-field type, or constructor arity drifts upstream,
-- the corresponding coerce target type mismatches the GHC heap object and
-- crashes here on first call (or on a forced traversal of the result).
--
-- Coverage matches the 11 entries in haskell-shim/ffi-exports.snapshot:
--   1. d_initialState_42         — exercised in setup
--   2. d_processJSONLine_58      — exercised in setup (DBC load + setProps)
--   3. d_processStartStreamDirect_24  — exercised in setup
--   4. d_processFrameDirect_12   — tests 1-4
--   5. d_processEventDirect_18   — tests 5-6
--   6. d_processExtractDirect_38 — test 7
--   7. d_processFormatDBCDirect_32 — test 8
--   8. d_processBuildFrameBin_72 — tests 9-10 (success + error)
--   9. d_processUpdateFrameBin_86 — test 11
--  10. d_processExtractBin_102   — test 12
--  11. d_processEndStreamDirect_28 — test 13
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
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.Trace.Time as AgdaTime
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Aletheia.CAN.DLC as AgdaDLC
import qualified MAlonzo.Code.Aletheia.CAN.BatchExtraction as AgdaBatch
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec
import qualified MAlonzo.Code.Data.Sum.Base as AgdaSum
import qualified MAlonzo.Code.Data.Rational.Base as AgdaRational

-- ============================================================================
-- HELPERS — mirror AletheiaFFI.hs / Marshal.hs / BinaryOutput.hs coerce sites
-- ============================================================================

-- | Extract (state, response text) from a JSON-out Σ pair.
-- Mirrors runJSON in AletheiaFFI.hs (lines 53-54).
extractResult :: AgdaSigma.T_Σ_14 -> (AgdaState.T_StreamState_28, T.Text)
extractResult result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
        tx = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    in (st, tx)

-- | Extract (state, Either Text Vec) from a binary-out Σ pair.
-- Mirrors runBinDispatch + dispatchSumResult (BinaryOutput.hs lines 41-50).
extractSumVec :: AgdaSigma.T_Σ_14
              -> (AgdaState.T_StreamState_28, Either T.Text AgdaVec.T_Vec_28)
extractSumVec result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
        sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    in case sumResult of
         AgdaSum.C_inj'8321'_38 errAny -> (st, Left  (unsafeCoerce errAny :: T.Text))
         AgdaSum.C_inj'8322'_42 vecAny -> (st, Right (unsafeCoerce vecAny :: AgdaVec.T_Vec_28))

-- | Extract (state, Either Text PartitionedResults). Highest-risk path:
-- mirrors aletheia_extract_signals_bin (AletheiaFFI.hs lines 218-224).
extractSumIER :: AgdaSigma.T_Σ_14
              -> (AgdaState.T_StreamState_28, Either T.Text AgdaBatch.T_PartitionedResults_10)
extractSumIER result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_28
        sumResult = unsafeCoerce (AgdaSigma.d_snd_30 result) :: AgdaSum.T__'8846'__30
    in case sumResult of
         AgdaSum.C_inj'8321'_38 errAny -> (st, Left  (unsafeCoerce errAny :: T.Text))
         AgdaSum.C_inj'8322'_42 ierAny -> (st, Right (unsafeCoerce ierAny :: AgdaBatch.T_PartitionedResults_10))

-- | Process a JSON command (used in setup).
processJSON :: AgdaState.T_StreamState_28 -> String
            -> (AgdaState.T_StreamState_28, T.Text)
processJSON state input = extractResult (AgdaJSON.d_processJSONLine_58 state (T.pack input))

-- | Convert [Word8] to MAlonzo Vec Byte n (linked-list shape).
-- Identical to bytesToAgdaVec in AletheiaFFI/Marshal.hs — must stay in sync.
bytesToAgdaVec :: [Word8] -> AgdaVec.T_Vec_28
bytesToAgdaVec [] = AgdaVec.C_'91''93'_32
bytesToAgdaVec (b:bs) = AgdaVec.C__'8759'__38
    (unsafeCoerce (toInteger b)) (bytesToAgdaVec bs)

-- | Walk MAlonzo Vec Byte to a Word8 list. Forces the full constructor
-- traversal so a Vec-shape drift crashes the test rather than slipping
-- through unforced thunks.
walkVec :: AgdaVec.T_Vec_28 -> [Word8]
walkVec AgdaVec.C_'91''93'_32 = []
walkVec (AgdaVec.C__'8759'__38 x xs) = fromIntegral (unsafeCoerce x :: Integer) : walkVec xs

-- | MAlonzo CANId from raw value + extended flag. The proof slot is
-- unsafeCoerce () — same pattern as Marshal.mkAgdaCanId. Caller validates
-- canId < standardMax / extendedMax.
mkAgdaCanId :: Integer -> Bool -> AgdaFrame.T_CANId_8
mkAgdaCanId canIdVal isExtended =
    if isExtended
        then AgdaFrame.C_Extended_16 canIdVal (unsafeCoerce ())
        else AgdaFrame.C_Standard_12 canIdVal (unsafeCoerce ())

-- | Construct MAlonzo (signalIndex, ℚ) Σ pair — mirrors mkSignalPairs in
-- AletheiaFFI/Marshal.hs (lines 87-94). Caller validates den > 0.
mkSignalPair :: Integer -> Integer -> Integer -> AgdaSigma.T_Σ_14
mkSignalPair idx num den =
    AgdaSigma.C__'44'__32
        (unsafeCoerce idx)
        (unsafeCoerce (AgdaRational.C_mkℚ_24 num (den - 1)))

-- | Walk PartitionedResults — forces field dispatch + full list traversals
-- of values / errors / absent. Mirrors packPartitionedResults
-- (BinaryOutput.hs lines 55-71). Returns concrete tuples so `show` can
-- force every embedded coerce.
walkPartitionedResults :: AgdaBatch.T_PartitionedResults_10
                       -> ([(Integer, Integer, Integer)], [(Integer, Integer)], [Integer])
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
            code = AgdaBatch.d_extractionErrorCodeToℕ_148
                     (unsafeCoerce (AgdaSigma.d_snd_30 p))
        in (idx, code)

-- | Construct a TimedFrame via binary MAlonzo constructors.
-- Mirrors aletheia_send_frame's construction in AletheiaFFI.hs.
mkTimedFrame :: Integer -> Integer -> Bool -> Integer -> [Word8]
             -> AgdaTrace.T_TimedFrame_6
mkTimedFrame timestamp canIdVal isExtended _dlc bytes =
    let agdaCanId = mkAgdaCanId canIdVal isExtended
        agdaVec = bytesToAgdaVec bytes
        -- CAN 2.0B: C_constructor_36 CANId DLC Vec. DLC erased at runtime
        -- via Fin; the helper dlc argument is unused at this layer.
        agdaFrame = AgdaFrame.C_constructor_36 agdaCanId (unsafeCoerce ()) agdaVec
        agdaTs = AgdaTime.C_mkTs_26 timestamp
        dataLen = toInteger (length bytes)
    -- TimedFrame: timestamp, payloadSize, frame, brs, esi. Non-FD: Nothing/Nothing.
    in AgdaTrace.C_constructor_32 agdaTs dataLen agdaFrame Nothing Nothing

-- | Process a frame via the binary path (processFrameDirect).
sendFrame :: AgdaState.T_StreamState_28 -> AgdaTrace.T_TimedFrame_6
          -> (AgdaState.T_StreamState_28, T.Text)
sendFrame state tf =
    extractResult (AgdaBin.d_processFrameDirect_12 state (unsafeCoerce tf))

-- | Send Error event via processEventDirect.
sendErrorEvent :: AgdaState.T_StreamState_28 -> Integer
               -> (AgdaState.T_StreamState_28, T.Text)
sendErrorEvent state ts =
    extractResult (AgdaBin.d_processEventDirect_18 state
        (unsafeCoerce (AgdaTrace.C_Error_38 (AgdaTime.C_mkTs_26 ts))))

-- | Send Remote event via processEventDirect.
sendRemoteEvent :: AgdaState.T_StreamState_28 -> Integer -> Integer -> Bool
                -> (AgdaState.T_StreamState_28, T.Text)
sendRemoteEvent state ts canIdVal isExtended =
    extractResult (AgdaBin.d_processEventDirect_18 state
        (unsafeCoerce (AgdaTrace.C_Remote_40 (AgdaTime.C_mkTs_26 ts)
                                              (mkAgdaCanId canIdVal isExtended))))

-- | Process extract (JSON-out) via processExtractDirect.
extractDirect :: AgdaState.T_StreamState_28 -> Integer -> Bool -> Integer -> [Word8]
              -> (AgdaState.T_StreamState_28, T.Text)
extractDirect state canIdVal isExt dlc bytes =
    extractResult (AgdaBin.d_processExtractDirect_38 state
        (mkAgdaCanId canIdVal isExt)
        (AgdaDLC.C_mkDLC_28 dlc)
        (unsafeCoerce (bytesToAgdaVec bytes)))

-- | Zero-arg JSON-out paths.
startStream, endStream, formatDBC
    :: AgdaState.T_StreamState_28 -> (AgdaState.T_StreamState_28, T.Text)
startStream st = extractResult (AgdaBin.d_processStartStreamDirect_24 st)
endStream   st = extractResult (AgdaBin.d_processEndStreamDirect_28   st)
formatDBC   st = extractResult (AgdaBin.d_processFormatDBCDirect_32   st)

-- | Build frame (binary out) via processBuildFrameBin.
buildFrameBin :: AgdaState.T_StreamState_28 -> Integer -> Bool -> Integer
              -> [AgdaSigma.T_Σ_14]
              -> (AgdaState.T_StreamState_28, Either T.Text AgdaVec.T_Vec_28)
buildFrameBin state canIdVal isExt dlc pairs =
    extractSumVec (AgdaBin.d_processBuildFrameBin_72 state
        (mkAgdaCanId canIdVal isExt)
        (AgdaDLC.C_mkDLC_28 dlc)
        pairs)

-- | Update frame (binary out) via processUpdateFrameBin.
updateFrameBin :: AgdaState.T_StreamState_28 -> Integer -> Bool -> Integer
               -> [Word8] -> [AgdaSigma.T_Σ_14]
               -> (AgdaState.T_StreamState_28, Either T.Text AgdaVec.T_Vec_28)
updateFrameBin state canIdVal isExt dlc bytes pairs =
    extractSumVec (AgdaBin.d_processUpdateFrameBin_86 state
        (mkAgdaCanId canIdVal isExt)
        (AgdaDLC.C_mkDLC_28 dlc)
        (unsafeCoerce (bytesToAgdaVec bytes))
        pairs)

-- | Extract signals (binary out) via processExtractBin.
extractBin :: AgdaState.T_StreamState_28 -> Integer -> Bool -> Integer -> [Word8]
           -> (AgdaState.T_StreamState_28, Either T.Text AgdaBatch.T_PartitionedResults_10)
extractBin state canIdVal isExt dlc bytes =
    extractSumIER (AgdaBin.d_processExtractBin_102 state
        (mkAgdaCanId canIdVal isExt)
        (AgdaDLC.C_mkDLC_28 dlc)
        (unsafeCoerce (bytesToAgdaVec bytes)))

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
    putStrLn "Binary FFI Smoke Test (R17-DEF-1: comprehensive unsafeCoerce drift guard)"
    putStrLn "=========================================================================="
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Setup: load DBC + properties + start stream.
    --   exercises: d_initialState_42, d_processJSONLine_58,
    --              d_processStartStreamDirect_24
    -- ------------------------------------------------------------------------
    let state0 = AgdaState.d_initialState_42

    let dbcJSON = concat
            [ "{\"type\":\"command\",\"command\":\"parseDBC\",\"dbc\":"
            , "{\"version\":\"\",\"messages\":[{"
            , "\"name\":\"TestMsg\",\"id\":256,\"dlc\":8,\"sender\":\"ECU\","
            , "\"signals\":[{\"name\":\"Speed\",\"startBit\":0,\"length\":16,"
            , "\"byteOrder\":\"little_endian\",\"signed\":false,"
            , "\"factor\":1,\"offset\":0,\"minimum\":0,\"maximum\":65535,"
            , "\"unit\":\"kph\"}]}]}}"
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
    -- Tests 1-4: d_processFrameDirect_12
    -- ------------------------------------------------------------------------
    putStrLn "Test 1: processFrameDirect — Speed=100, expect ack (100 < 1000)"
    let tf1 = mkTimedFrame 1000 256 False 8 [100, 0, 0, 0, 0, 0, 0, 0]
    let (state4, r1) = sendFrame state3 tf1
    let r1s = T.unpack r1
    putStrLn $ "  Response: " ++ r1s
    pass1 <- assertContains "Ack response" "\"status\": \"ack\"" r1s

    putStrLn "Test 2: processFrameDirect — Speed=1500, expect violation (1500 ≥ 1000)"
    let tf2 = mkTimedFrame 2000 256 False 8 [220, 5, 0, 0, 0, 0, 0, 0]
    let (_, r2) = sendFrame state4 tf2
    let r2s = T.unpack r2
    putStrLn $ "  Response: " ++ r2s
    pass2 <- assertContains "Violation response" "\"status\": \"fails\"" r2s

    putStrLn "Test 3: processFrameDirect — non-matching standard ID, expect ack"
    let tf3 = mkTimedFrame 3000 512 False 8 [255, 255, 0, 0, 0, 0, 0, 0]
    let (_, r3) = sendFrame state3 tf3
    let r3s = T.unpack r3
    putStrLn $ "  Response: " ++ r3s
    pass3 <- assertContains "Ack for non-matching ID" "\"status\": \"ack\"" r3s

    putStrLn "Test 4: processFrameDirect — extended CAN ID, expect ack"
    let tf4 = mkTimedFrame 4000 256 True 8 [0, 0, 0, 0, 0, 0, 0, 0]
    let (_, r4) = sendFrame state3 tf4
    let r4s = T.unpack r4
    putStrLn $ "  Response: " ++ r4s
    pass4 <- assertContains "Ack for extended ID" "\"status\": \"ack\"" r4s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 5-6: d_processEventDirect_18
    -- ------------------------------------------------------------------------
    putStrLn "Test 5: processEventDirect (Error) — expect ack"
    let (_, r5) = sendErrorEvent state3 5000
    let r5s = T.unpack r5
    putStrLn $ "  Response: " ++ r5s
    pass5 <- assertContains "Error event ack" "\"status\": \"ack\"" r5s

    putStrLn "Test 6: processEventDirect (Remote) — expect ack"
    let (_, r6) = sendRemoteEvent state3 6000 256 False
    let r6s = T.unpack r6
    putStrLn $ "  Response: " ++ r6s
    pass6 <- assertContains "Remote event ack" "\"status\": \"ack\"" r6s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 7: d_processExtractDirect_38 (JSON-out)
    -- ------------------------------------------------------------------------
    putStrLn "Test 7: processExtractDirect — Speed=200, expect signal value in response"
    let (_, r7) = extractDirect state3 256 False 8 [200, 0, 0, 0, 0, 0, 0, 0]
    let r7s = T.unpack r7
    putStrLn $ "  Response: " ++ r7s
    pass7 <- assertContains "Extract response contains Speed" "Speed" r7s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 8: d_processFormatDBCDirect_32
    -- ------------------------------------------------------------------------
    putStrLn "Test 8: processFormatDBCDirect — expect formatted DBC containing TestMsg"
    let (_, r8) = formatDBC state3
    let r8s = T.unpack r8
    putStrLn $ "  Response: " ++ take 200 r8s ++ (if length r8s > 200 then "..." else "")
    pass8 <- assertContains "DBC format contains TestMsg" "TestMsg" r8s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Tests 9-10: d_processBuildFrameBin_72 (success + error)
    -- ------------------------------------------------------------------------
    putStrLn "Test 9: processBuildFrameBin — Speed=300 at idx 0, expect inj₂ Vec"
    let pairs9 = [mkSignalPair 0 300 1]
    let (_, r9) = buildFrameBin state3 256 False 8 pairs9
    pass9 <- case r9 of
        Right vec -> do
            let bytes9 = walkVec vec
            putStrLn $ "  Bytes: " ++ show bytes9
            -- 300 = 0x012C; LE 16-bit → [0x2C, 0x01] in low bytes; rest zero.
            assertTrue "Build success — 8 bytes, low pair = (44, 1)"
                       ("got " ++ show bytes9)
                       (length bytes9 == 8 && take 2 bytes9 == [44, 1])
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False

    putStrLn "Test 10: processBuildFrameBin — bad CAN ID 999, expect inj₁ Text"
    let pairs10 = [mkSignalPair 0 100 1]
    let (_, r10) = buildFrameBin state3 999 False 8 pairs10
    pass10 <- case r10 of
        Left errText -> do
            -- T.unpack forces traversal; coerce-target mismatch crashes here.
            let errStr = T.unpack errText
            putStrLn $ "  Error text: " ++ errStr
            assertTrue "Build error — non-empty Text from inj₁"
                       ("got length=" ++ show (T.length errText))
                       (T.length errText > 0)
        Right vec -> do
            let bs = walkVec vec
            putStrLn $ "  Unexpected Vec: " ++ show bs
            return False
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 11: d_processUpdateFrameBin_86
    -- ------------------------------------------------------------------------
    putStrLn "Test 11: processUpdateFrameBin — Speed=500 over zeroed payload, expect inj₂ Vec"
    let baseBytes = [0, 0, 0, 0, 0, 0, 0, 0]
    let pairs11 = [mkSignalPair 0 500 1]
    let (_, r11) = updateFrameBin state3 256 False 8 baseBytes pairs11
    pass11 <- case r11 of
        Right vec -> do
            let bytes11 = walkVec vec
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
    -- Test 12: d_processExtractBin_102 (highest-risk: PartitionedResults coerce)
    -- ------------------------------------------------------------------------
    putStrLn "Test 12: processExtractBin — Speed=400, expect inj₂ PartitionedResults with 1 value"
    let bytes12 = [144, 1, 0, 0, 0, 0, 0, 0]  -- 400 = 0x0190; LE → [0x90, 0x01].
    let (_, r12) = extractBin state3 256 False 8 bytes12
    pass12 <- case r12 of
        Right ier -> do
            let (vals, errs, abss) = walkPartitionedResults ier
            putStrLn $ "  values:  " ++ show vals
            putStrLn $ "  errors:  " ++ show errs
            putStrLn $ "  absent:  " ++ show abss
            -- Speed at signal index 0, raw=400, factor=1, offset=0 → 400/1.
            -- d_denominatorℕ_20 returns the actual denominator (the record's
            -- denominator-1 field plus one), so 400/1 reads as (0, 400, 1).
            assertTrue "Extract success — 1 value (idx=0, num=400, den=1), 0 errors"
                       ("got vals=" ++ show vals ++ ", errs=" ++ show errs)
                       (vals == [(0, 400, 1)] && null errs)
        Left err -> do
            putStrLn $ "  Unexpected error: " ++ T.unpack err
            return False
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Test 13: d_processEndStreamDirect_28
    -- ------------------------------------------------------------------------
    putStrLn "Test 13: processEndStreamDirect — expect summary response"
    let (_, r13) = endStream state3
    let r13s = T.unpack r13
    putStrLn $ "  Response: " ++ r13s
    pass13 <- assertContains "End stream response is JSON" "\"status\":" r13s
    putStrLn ""

    -- ------------------------------------------------------------------------
    -- Summary
    -- ------------------------------------------------------------------------
    let allPass = and [pass1, pass2, pass3, pass4, pass5, pass6, pass7, pass8,
                       pass9, pass10, pass11, pass12, pass13]
    if allPass
        then putStrLn "All 13 checks passed (11/11 FFI exports exercised)." >> exitSuccess
        else putStrLn "SOME CHECKS FAILED." >> exitFailure
