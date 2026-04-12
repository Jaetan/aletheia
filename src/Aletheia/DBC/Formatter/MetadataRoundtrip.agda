{-# OPTIONS --safe --without-K #-}

-- Metadata-level roundtrip proofs for the DBC formatter.
--
-- Purpose: Prove roundtrip for signal groups, environment variables, and value
-- tables. These metadata types have no bounds constraints (unlike signals/messages
-- which need WellFormed/PhysicallyValid), so the proofs are unconditional.
-- Role: Middle layer — used by Properties.agda for the top-level roundtrip.
module Aletheia.DBC.Formatter.MetadataRoundtrip where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (SignalGroup; EnvironmentVar; ValueTable;
  VarType; IntVar; FloatVar; StringVar; varTypeToℕ)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatSignalGroup;
  formatEnvironmentVar; formatValueTable; formatValueEntry)
open import Aletheia.DBC.JSONParser using (parseStringList; parseVarType;
  parseSignalGroup; parseSignalGroupList;
  parseEnvironmentVar; parseEnvironmentVarList;
  parseValueEntry; parseValueEntryList;
  parseValueTable; parseValueTableList;
  parseObjectList)
open import Aletheia.JSON using (JSON; JObject; JString; JNumber; JArray)
open import Aletheia.DBC.Formatter.WellFormed using (getNat-ℕtoJSON)

-- ============================================================================
-- STRING LIST ROUNDTRIP
-- ============================================================================

parseStringList-roundtrip : ∀ ss → parseStringList (map JString ss) ≡ inj₂ ss
parseStringList-roundtrip [] = refl
parseStringList-roundtrip (s ∷ ss)
  rewrite parseStringList-roundtrip ss = refl

-- ============================================================================
-- VARTYPE ROUNDTRIP
-- ============================================================================

parseVarType-roundtrip : ∀ vt → parseVarType (varTypeToℕ vt) ≡ inj₂ vt
parseVarType-roundtrip IntVar    = refl
parseVarType-roundtrip FloatVar  = refl
parseVarType-roundtrip StringVar = refl

-- ============================================================================
-- SIGNAL GROUP ROUNDTRIP
-- ============================================================================

private
  signalGroupFields : SignalGroup → List (String × JSON)
  signalGroupFields sg =
    ("name"    , JString (SignalGroup.name sg)) ∷
    ("signals" , JArray (map JString (SignalGroup.signals sg))) ∷
    []

signalGroup-roundtrip : ∀ sg
  → parseSignalGroup (signalGroupFields sg) ≡ inj₂ sg
signalGroup-roundtrip sg
  rewrite parseStringList-roundtrip (SignalGroup.signals sg) = refl

private
  signalGroup-list-go : ∀ n gs
    → parseObjectList "signalGroup" parseSignalGroup n (map formatSignalGroup gs) ≡ inj₂ gs
  signalGroup-list-go _ [] = refl
  signalGroup-list-go n (sg ∷ gs)
    rewrite signalGroup-roundtrip sg
          | signalGroup-list-go (suc n) gs = refl

signalGroup-list-roundtrip : ∀ gs
  → parseSignalGroupList (map formatSignalGroup gs) ≡ inj₂ gs
signalGroup-list-roundtrip = signalGroup-list-go 0

-- ============================================================================
-- ENVIRONMENT VARIABLE ROUNDTRIP
-- ============================================================================

private
  environmentVarFields : EnvironmentVar → List (String × JSON)
  environmentVarFields ev =
    ("name"    , JString (EnvironmentVar.name ev)) ∷
    ("varType" , ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))) ∷
    ("initial" , JNumber (EnvironmentVar.initial ev)) ∷
    ("minimum" , JNumber (EnvironmentVar.minimum ev)) ∷
    ("maximum" , JNumber (EnvironmentVar.maximum ev)) ∷
    []

environmentVar-roundtrip : ∀ ev
  → parseEnvironmentVar (environmentVarFields ev) ≡ inj₂ ev
environmentVar-roundtrip ev
  rewrite getNat-ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))
        | parseVarType-roundtrip (EnvironmentVar.varType ev) = refl

private
  environmentVar-list-go : ∀ n evs
    → parseObjectList "environmentVar" parseEnvironmentVar n (map formatEnvironmentVar evs) ≡ inj₂ evs
  environmentVar-list-go _ [] = refl
  environmentVar-list-go n (ev ∷ evs)
    rewrite environmentVar-roundtrip ev
          | environmentVar-list-go (suc n) evs = refl

environmentVar-list-roundtrip : ∀ evs
  → parseEnvironmentVarList (map formatEnvironmentVar evs) ≡ inj₂ evs
environmentVar-list-roundtrip = environmentVar-list-go 0

-- ============================================================================
-- VALUE TABLE ROUNDTRIP
-- ============================================================================

private
  valueEntryFields : ℕ × String → List (String × JSON)
  valueEntryFields (n , s) =
    ("value"       , ℕtoJSON n) ∷
    ("description" , JString s) ∷
    []

valueEntry-roundtrip : ∀ e
  → parseValueEntry (valueEntryFields e) ≡ inj₂ e
valueEntry-roundtrip (n , s)
  rewrite getNat-ℕtoJSON n = refl

private
  valueEntryList-go : ∀ n es
    → parseObjectList "valueEntry" parseValueEntry n (map formatValueEntry es) ≡ inj₂ es
  valueEntryList-go _ [] = refl
  valueEntryList-go n (e ∷ es)
    rewrite valueEntry-roundtrip e
          | valueEntryList-go (suc n) es = refl

valueEntryList-roundtrip : ∀ es
  → parseValueEntryList (map formatValueEntry es) ≡ inj₂ es
valueEntryList-roundtrip = valueEntryList-go 0

private
  valueTableFields : ValueTable → List (String × JSON)
  valueTableFields vt =
    ("name"    , JString (ValueTable.name vt)) ∷
    ("entries" , JArray (map formatValueEntry (ValueTable.entries vt))) ∷
    []

valueTable-roundtrip : ∀ vt
  → parseValueTable (valueTableFields vt) ≡ inj₂ vt
valueTable-roundtrip vt
  rewrite valueEntryList-roundtrip (ValueTable.entries vt) = refl

private
  valueTable-list-go : ∀ n vts
    → parseObjectList "valueTable" parseValueTable n (map formatValueTable vts) ≡ inj₂ vts
  valueTable-list-go _ [] = refl
  valueTable-list-go n (vt ∷ vts)
    rewrite valueTable-roundtrip vt
          | valueTable-list-go (suc n) vts = refl

valueTable-list-roundtrip : ∀ vts
  → parseValueTableList (map formatValueTable vts) ≡ inj₂ vts
valueTable-list-roundtrip = valueTable-list-go 0
