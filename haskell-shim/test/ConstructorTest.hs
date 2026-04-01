{-# OPTIONS_GHC -Wno-unused-imports -Wno-missing-signatures -Wno-missing-home-modules #-}

-- | Binary FFI Smoke Test
--
-- End-to-end test of the binary frame path (processFrameDirect). Verifies
-- that MAlonzo constructor calls in AletheiaFFI.hs (bytesToAgdaVec,
-- C_constructor_26, C_Standard_10, etc.) produce well-formed types that
-- survive signal extraction and LTL evaluation.
--
-- This is NOT a substitute for the Agda proofs — handleDataFrame's
-- correctness is proven formally. This test exists solely to catch
-- MAlonzo constructor layout drift at the Haskell FFI trust boundary,
-- which is outside Agda's reach.
--
-- Test strategy:
--   1. Set up a Streaming session via JSON commands (load DBC, set properties)
--   2. Send frames via binary constructors (the production path)
--   3. Assert responses match expected values
module Main where

import Data.List (isInfixOf)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)
import Data.Word (Word8)
import System.Exit (exitFailure, exitSuccess)

-- MAlonzo-generated modules (same imports as AletheiaFFI.hs)
import qualified MAlonzo.Code.Aletheia.Main as Agda
import qualified MAlonzo.Code.Aletheia.Protocol.StreamState as AgdaState
import qualified MAlonzo.Code.Agda.Builtin.Sigma as AgdaSigma
import qualified MAlonzo.Code.Aletheia.Trace.CANTrace as AgdaTrace
import qualified MAlonzo.Code.Aletheia.CAN.Frame as AgdaFrame
import qualified MAlonzo.Code.Data.Vec.Base as AgdaVec

-- | Extract (state, response text) from MAlonzo Σ pair.
extractResult :: AgdaSigma.T_Σ_14 -> (AgdaState.T_StreamState_34, T.Text)
extractResult result =
    let st = unsafeCoerce (AgdaSigma.d_fst_28 result) :: AgdaState.T_StreamState_34
        tx = unsafeCoerce (AgdaSigma.d_snd_30 result) :: T.Text
    in (st, tx)

-- | Process a JSON command (used only for session setup, not data frames).
processJSON :: AgdaState.T_StreamState_34 -> String -> (AgdaState.T_StreamState_34, T.Text)
processJSON state input = extractResult (Agda.d_processJSONLine_4 state (T.pack input))

-- | Convert [Word8] to MAlonzo Vec Byte n.
-- Identical to bytesToAgdaVec in AletheiaFFI.hs — must stay in sync.
bytesToAgdaVec :: [Word8] -> AgdaVec.T_Vec_28
bytesToAgdaVec [] = AgdaVec.C_'91''93'_32
bytesToAgdaVec (b:bs) = AgdaVec.C__'8759'__38
    (unsafeCoerce (toInteger b)) (bytesToAgdaVec bs)

-- | Construct a TimedFrame via binary MAlonzo constructors.
-- Identical to the construction in aletheia_send_frame — must stay in sync.
mkTimedFrame :: Integer -> Integer -> Bool -> Integer -> [Word8]
             -> AgdaTrace.T_TimedFrame_8
mkTimedFrame timestamp canIdVal isExtended dlc bytes =
    let agdaCanId = if isExtended
            then AgdaFrame.C_Extended_12 canIdVal
            else AgdaFrame.C_Standard_10 canIdVal
        agdaVec = bytesToAgdaVec bytes
        agdaFrame = AgdaFrame.C_constructor_32 agdaCanId dlc agdaVec
        dataLen = toInteger (length bytes)
    in AgdaTrace.C_constructor_26 timestamp dataLen agdaFrame

-- | Process a frame via the binary path (processFrameDirect).
sendFrame :: AgdaState.T_StreamState_34 -> AgdaTrace.T_TimedFrame_8
          -> (AgdaState.T_StreamState_34, T.Text)
sendFrame state tf =
    extractResult (Agda.d_processFrameDirect_58 state (unsafeCoerce tf))

-- | Assert a response contains an expected substring.
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

main :: IO ()
main = do
    putStrLn "Binary FFI Smoke Test"
    putStrLn "====================="
    putStrLn ""

    -- Setup: Load DBC with one message (ID=256, 8 bytes) containing one signal
    -- Signal "Speed": startBit=0, length=16, LE, unsigned, factor=1, offset=0
    let state0 = AgdaState.d_initialState_58

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

    -- Set property: always(Speed < 1000)
    let propsJSON = concat
            [ "{\"type\":\"command\",\"command\":\"setProperties\",\"properties\":["
            , "{\"operator\":\"always\",\"formula\":"
            , "{\"operator\":\"atomic\",\"predicate\":"
            , "{\"predicate\":\"lessThan\",\"signal\":\"Speed\",\"value\":1000}}}]}"
            ]
    let (state2, resp2) = processJSON state1 propsJSON
    putStrLn $ "Setup: Set properties → " ++ T.unpack resp2

    -- Start streaming
    let (state3, resp3) = processJSON state2 "{\"type\":\"command\",\"command\":\"startStream\"}"
    putStrLn $ "Setup: Start stream → " ++ T.unpack resp3
    putStrLn ""

    -- Test 1: Speed=100, standard CAN ID matching DBC → Ack (100 < 1000)
    putStrLn "Test 1: Speed=100, expect ack (100 < 1000)"
    let tf1 = mkTimedFrame 1000 256 False 8 [100, 0, 0, 0, 0, 0, 0, 0]
    let (state4, r1) = sendFrame state3 tf1
    let r1s = T.unpack r1
    putStrLn $ "  Response: " ++ r1s
    pass1 <- assertContains "Ack response" "\"status\": \"ack\"" r1s

    -- Test 2: Speed=1500, same message → Violation (1500 ≥ 1000)
    -- Use state4 (after test 1) so LTL state is properly advanced
    putStrLn "Test 2: Speed=1500, expect violation (1500 >= 1000)"
    let tf2 = mkTimedFrame 2000 256 False 8 [220, 5, 0, 0, 0, 0, 0, 0]
    let (_, r2) = sendFrame state4 tf2
    let r2s = T.unpack r2
    putStrLn $ "  Response: " ++ r2s
    pass2 <- assertContains "Violation response" "\"status\": \"fails\"" r2s

    -- Test 3: Non-matching CAN ID → Ack (no signal extraction)
    putStrLn "Test 3: CAN ID 0x200, no DBC match, expect ack"
    let tf3 = mkTimedFrame 3000 512 False 8 [255, 255, 0, 0, 0, 0, 0, 0]
    let (_, r3) = sendFrame state3 tf3
    let r3s = T.unpack r3
    putStrLn $ "  Response: " ++ r3s
    pass3 <- assertContains "Ack for non-matching ID" "\"status\": \"ack\"" r3s

    -- Test 4: Extended CAN ID → Ack (DBC has standard 256, extended 256 doesn't match)
    putStrLn "Test 4: Extended CAN ID, no DBC match, expect ack"
    let tf4 = mkTimedFrame 4000 256 True 8 [0, 0, 0, 0, 0, 0, 0, 0]
    let (_, r4) = sendFrame state3 tf4
    let r4s = T.unpack r4
    putStrLn $ "  Response: " ++ r4s
    pass4 <- assertContains "Ack for extended ID" "\"status\": \"ack\"" r4s

    -- Summary
    putStrLn ""
    let allPass = and [pass1, pass2, pass3, pass4]
    if allPass
        then putStrLn "All 4 checks passed." >> exitSuccess
        else putStrLn "SOME CHECKS FAILED." >> exitFailure
