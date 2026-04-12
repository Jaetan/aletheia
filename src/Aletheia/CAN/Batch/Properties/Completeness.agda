{-# OPTIONS --safe --without-K #-}

-- Completeness of extractAllSignalsFromMessage.
--
-- Purpose: Prove that batch extraction produces exactly one entry per signal
--   in the message's signal list, partitioned across values/errors/absent.
-- Key result: extractAll-complete.
module Aletheia.CAN.Batch.Properties.Completeness where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.Error using (MuxValueMismatch; MuxSignalNotFound; MuxChainCycle; MuxExtractionFailed; BitExtractionFailed)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.BatchExtraction using (PartitionedResults; mkPartitionedResults; ExtractionResults; categorizeResult; combinePartitioned; emptyPartitioned; extractAllSignalsFromMessage)
open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)

open import Data.List using (List; []; _∷_; length; map; foldr)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

-- ============================================================================
-- EXTRACTALLSIGNALS COMPLETENESS
-- ============================================================================

-- Total entries across all three partitions
totalEntries : ExtractionResults → ℕ
totalEntries r = length (PartitionedResults.values r)
               + length (PartitionedResults.errors r)
               + length (PartitionedResults.absent r)

private
  shift-mid : ∀ a b c → a + suc b + c ≡ suc (a + b + c)
  shift-mid a b c = cong (_+ c) (+-suc a b)

  shift-last : ∀ a b c → a + b + suc c ≡ suc (a + b + c)
  shift-last a b c = +-suc (a + b) c

-- Completeness: extractAllSignalsFromMessage produces exactly one entry per signal.
extractAll-complete : ∀ {n} (frame : CANFrame n) msg
  → totalEntries (extractAllSignalsFromMessage frame msg)
    ≡ length (DBCMessage.signals msg)
extractAll-complete frame msg = go (DBCMessage.signals msg)
  where
    f : DBCSignal → ExtractionResults
    f sig = categorizeResult (DBCSignal.name sig)
              (extractSignalDirect msg frame sig)

    go : ∀ sigs → totalEntries (foldr combinePartitioned emptyPartitioned (map f sigs))
                  ≡ length sigs
    go [] = refl
    go (sig ∷ sigs)
      with extractSignalDirect msg frame sig
         | foldr combinePartitioned emptyPartitioned (map f sigs) | go sigs
    ... | Success _              | mkPartitionedResults vs es as | ih =
      cong suc ih
    ... | SignalNotInDBC         | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent MuxValueMismatch        | mkPartitionedResults vs es as | ih =
      trans (shift-last (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent (MuxSignalNotFound _)   | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent MuxChainCycle           | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent (MuxExtractionFailed _) | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | SignalNotPresent (BitExtractionFailed _) | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | ValueOutOfBounds _ _ _ | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
    ... | ExtractionFailed _     | mkPartitionedResults vs es as | ih =
      trans (shift-mid (length vs) (length es) (length as)) (cong suc ih)
