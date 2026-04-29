{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — slim `parseEnvVar-roundtrip` derived from the
-- universal Format DSL roundtrip.
--
-- Pre-3d.5.d (3b): hand-written 1,581-line bind-chain proof through 14
-- parser primitives (every wire-level token + line terminator).
--
-- Post-3d.5.d: `parseEnvVar = parse envVarFmt >>= many parseNewline >>=
-- pure` (in `TextParser.EnvVars`), and the roundtrip reduces to:
--
--   1. A bridge `emit-envVarFmt-eq-emitEnvVar-chars` proving DSL emit on
--      `ev` equals existing `emitEnvVar-chars ev`.  Case-splits on
--      `varType ev` (3 cases) to bridge `emit varTypeFmt vt ≡
--      emitVarType-chars vt`; every other slot is definitional.
--   2. The universal `parseEnvVar-format-roundtrip` (from `Format.EnvVar`).
--   3. The trailing `many parseNewline` consuming zero from the user's
--      `suffix` (via `manyHelper-parseNewline-exhaust` + the existing
--      `SuffixStops isNewlineStart suffix` precondition).
--
-- The `EnvVarNameStop` precondition migrates upstream to `Format.EnvVar`;
-- this module re-exports it for source compatibility with the section
-- facade `Properties/EnvVars.agda`.
--
-- Load-bearing canary: ensures `validIdentifierᵇ (toList
-- "DUMMY_NODE_VECTOR0")` and `validIdentifierᵇ (toList "Vector__XXX")`
-- reduce to `true` on the closed-Char path.  Imported below so a stdlib
-- `Data.Char.Base` regression flags before this file does.
module Aletheia.DBC.TextParser.Properties.EnvVars.EnvVar where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Types
  using (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.EnvVars using (parseEnvVar)
open import Aletheia.DBC.TextFormatter.EnvVars using (emitEnvVar-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
open import Aletheia.DBC.TextParser.Format.EnvVar as FmtEV using
  (envVarFmt; parseEnvVar-format-roundtrip)

-- Load-bearing canary.
import Aletheia.DBC.TextParser.Properties.EnvVars._Scratch

-- ============================================================================
-- RE-EXPORT — `EnvVarNameStop` migrated to `Format.EnvVar`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.EnvVar public
  using (EnvVarNameStop)

-- ============================================================================
-- BRIDGE: DSL emit ≡ existing emitEnvVar-chars
-- ============================================================================

-- `emit envVarFmt ev` reduces (through nested isos / withPrefix / withWS
-- / wsOpt / discardFmt / pair / iso) to a flat concatenation matching
-- `emitEnvVar-chars ev` slot-for-slot, modulo `emit varTypeFmt vt` vs
-- `emitVarType-chars vt`.  Case-splitting on `EnvironmentVar.varType ev`
-- specialises both sides: `emit varTypeFmt IntVar = '0' ∷ []` etc., and
-- `emitVarType-chars IntVar = '0' ∷ []`, both reducing to the same
-- closed-char list.  The remainder is definitional `_++_` reduction
-- through closed cons-list cells.
emit-envVarFmt-eq-emitEnvVar-chars : ∀ (ev : EnvironmentVar)
  → emit envVarFmt ev ≡ emitEnvVar-chars ev
emit-envVarFmt-eq-emitEnvVar-chars ev with EnvironmentVar.varType ev
... | IntVar    = refl
... | FloatVar  = refl
... | StringVar = refl

-- ============================================================================
-- SLIM `parseEnvVar-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseEnvVar = parse envVarFmt >>= λ ev → many parseNewline
-- >>= λ _ → pure ev`.  Composition decomposes into:
--
--   1. `parse envVarFmt pos (emit envVarFmt ev ++ suffix)` via
--      `parseEnvVar-format-roundtrip`.
--   2. `many parseNewline pos' suffix` returning `[]`-no-consume via
--      `manyHelper-parseNewline-exhaust` + `nl-stop` precondition.
--   3. `pure ev` returns the input value at the resulting position.
--
-- `subst` on input/output positions converts between `emit envVarFmt ev`
-- and `emitEnvVar-chars ev` via the bridge.
parseEnvVar-roundtrip :
    ∀ (pos : Position) (ev : EnvironmentVar) (suffix : List Char)
  → EnvVarNameStop ev
  → SuffixStops isNewlineStart suffix
  → parseEnvVar pos (emitEnvVar-chars ev ++ₗ suffix)
    ≡ just (mkResult ev
             (advancePositions pos (emitEnvVar-chars ev))
             suffix)
parseEnvVar-roundtrip pos ev suffix nameStop nl-stop =
  trans (cong (λ inp → parseEnvVar pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-pure))
  where
    bridge : emit envVarFmt ev ≡ emitEnvVar-chars ev
    bridge = emit-envVarFmt-eq-emitEnvVar-chars ev

    pos-line : Position
    pos-line = advancePositions pos (emit envVarFmt ev)

    cont-line : EnvironmentVar → Parser EnvironmentVar
    cont-line v = many parseNewline >>= λ _ → pure v

    cont-blanks : List Char → Parser EnvironmentVar
    cont-blanks _ = pure ev

    -- Step 1: parse envVarFmt succeeds via the universal roundtrip.
    step-format :
      parseEnvVar pos (emit envVarFmt ev ++ₗ suffix)
      ≡ cont-line ev pos-line suffix
    step-format =
      bind-just-step (parse envVarFmt)
                     cont-line
                     pos (emit envVarFmt ev ++ₗ suffix)
                     ev pos-line suffix
                     (parseEnvVar-format-roundtrip pos ev suffix nameStop)

    -- Step 2: many parseNewline consumes zero from `suffix`.
    step-many-newline :
      cont-line ev pos-line suffix
      ≡ cont-blanks [] pos-line suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: pure ev returns just (mkResult ev pos-line suffix); convert
    -- pos-line back to `advancePositions pos (emitEnvVar-chars ev)` via
    -- the bridge.
    step-pure :
      cont-blanks [] pos-line suffix
      ≡ just (mkResult ev
               (advancePositions pos (emitEnvVar-chars ev))
               suffix)
    step-pure =
      cong (λ p → just (mkResult ev p suffix))
           (cong (advancePositions pos) bridge)
