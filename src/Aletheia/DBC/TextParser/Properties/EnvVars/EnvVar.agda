{-# OPTIONS --safe --without-K #-}

-- `parseEnvVar-roundtrip` — per-line-construct roundtrip for the DBC
-- `EV_ <name>: <type> [<min>|<max>] "<unit>" <initial> <env_id>
--   <access_type> <access_node>;` line (B.3.d Layer 3 Commit 3b).
--
-- Bind chain (matches `Aletheia.DBC.TextParser.EnvVars.parseEnvVar`):
--
--   string "EV_" *> parseWS *> parseIdentifier >>= λ nm →
--   parseWSOpt *> char ':' *> parseWS *> parseVarType >>= λ vt →
--   parseWS *> char '[' *> parseDecRat >>= λ mn →
--   char '|' *> parseDecRat >>= λ mx →
--   char ']' *> parseWS *> parseStringLit *>
--   parseWS *> parseDecRat >>= λ ini →
--   parseWS *> parseNatural *>                       -- env_id, discarded
--   parseWS *> parseIdentifier *>                    -- access_type, discarded
--   parseWS *> parseIdentifier *>                    -- access_node, discarded
--   parseWSOpt *> char ';' *> parseNewline *>
--   many parseNewline *>
--   pure (record { name = nm; varType = vt; initial = ini;
--                  minimum = mn; maximum = mx })
--
-- Synthesized drop-field defaults (the wire grammar requires 14 tokens
-- but the Agda `EnvironmentVar` record only carries 5):
--   * unit         — `""` (empty quoted string)
--   * env_id       — `0`
--   * access_type  — `DUMMY_NODE_VECTOR0`
--   * access_node  — `Vector__XXX`
--
-- The two synthesized identifiers (`DUMMY_NODE_VECTOR0` / `Vector__XXX`)
-- demand `T (validIdentifierᵇ (toList name))` witnesses for the
-- `Identifier` record.  Both reduce to `tt` definitionally on the
-- closed-Char `validIdentifierᵇ` definition; the load-bearing canary
-- in `_Scratch.agda` (imported below) verifies the reduction so any
-- stdlib `Data.Char.Base` regression flags before this file does.
module Aletheia.DBC.TextParser.Properties.EnvVars.EnvVar where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_; map; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n; m≤m+n; m≤n+m)
open import Data.List.Properties using (length-++; ++-identityʳ) renaming (++-assoc to ++ₗ-assoc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   sameLengthᵇ; pure; _>>=_; _*>_; _<|>_; string; char; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseNatural;
   parseWS; parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.EnvVars using
  (parseEnvVar; parseVarType)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextFormatter.EnvVars using
  (emitEnvVar-chars; emitVarType-chars)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showNat-chars; showDecRat-dec-chars; quoteStringLit-chars; digitChar)
open import Aletheia.DBC.Types using
  (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; []-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; advancePositions-++;
   parseNatural-showNat-chars; showNat-chars-head;
   parseDecRat-roundtrip-suffix;
   showDecRat-chars-head-dash; showDecRat-chars-head-digit)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Data.Integer using (ℤ) renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; char-matches; parseWS-one-space;
   parseIdentifier-roundtrip; parseStringLit-roundtrip;
   quoteStringLit-chars-shape)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF;
   manyHelper-parseNewline-exhaust)

-- Load-bearing canary: ensures `validIdentifierᵇ (toList "DUMMY_NODE_VECTOR0")`
-- and `validIdentifierᵇ (toList "Vector__XXX")` reduce to `true` on the
-- closed-Char path.  If a stdlib regression breaks the reduction, that
-- file fails to typecheck before this one does.
import Aletheia.DBC.TextParser.Properties.EnvVars._Scratch

-- ============================================================================
-- Per-name precondition
-- ============================================================================

-- Each EV_ entry's `name` decomposes as `c ∷ cs` with `isHSpace c ≡
-- false`, so `parseWS` between `EV_` and the name stops cleanly after
-- consuming the single separator space.  Layer 4 will discharge this
-- universally from `validIdentifierᵇ` via the `isIdentStart→¬isHSpace`
-- bridge (see `project_b3d_layer4_owed_lemmas.md`).
EnvVarNameStop : EnvironmentVar → Set
EnvVarNameStop ev =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (EnvironmentVar.name ev) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- Synthesized drop-field identifier values
-- ============================================================================

-- The wire grammar requires `access_type` and `access_node` identifiers
-- but the `EnvironmentVar` record drops them.  The emitter writes
-- placeholders; the parser reads them as `Identifier` values that the
-- bind-chain `_` discards.  Both placeholders' validity reduces to
-- `tt` on the closed `validIdentifierᵇ` definition (canary verified
-- above).
ident-DummyNode : Identifier
ident-DummyNode = mkIdent (toList "DUMMY_NODE_VECTOR0") tt

ident-VectorXXX : Identifier
ident-VectorXXX = mkIdent (toList "Vector__XXX") tt

-- ============================================================================
-- parseVarType-roundtrip
-- ============================================================================
--
-- Three cases — one per VarType — each closes by `refl` because the
-- emitted `vt-chars` is a single concrete digit and the `_<|>_` chain
-- in `parseVarType` reduces definitionally on the matching prefix.

parseVarType-roundtrip : ∀ (vt : VarType) (pos : Position) (rest : List Char) →
  parseVarType pos (emitVarType-chars vt ++ₗ rest)
    ≡ just (mkResult vt
              (advancePositions pos (emitVarType-chars vt))
              rest)
parseVarType-roundtrip IntVar    _ _ = refl
parseVarType-roundtrip FloatVar  _ _ = refl
parseVarType-roundtrip StringVar _ _ = refl

-- ============================================================================
-- Char-class disjointness — emitted shape stops on each parser-class boundary
-- ============================================================================

private
  -- `digitChar d ≡ '0' .. '9'` for `d < 10`; the fallthrough `digitChar
  -- _ = '0'` covers `d ≥ 10`.  All ten possible outputs are non-hspace
  -- closed-Char terms.  Used to stop `parseWS` cleanly after `parseNatural`.
  digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
  digitChar-not-isHSpace 0 = refl
  digitChar-not-isHSpace 1 = refl
  digitChar-not-isHSpace 2 = refl
  digitChar-not-isHSpace 3 = refl
  digitChar-not-isHSpace 4 = refl
  digitChar-not-isHSpace 5 = refl
  digitChar-not-isHSpace 6 = refl
  digitChar-not-isHSpace 7 = refl
  digitChar-not-isHSpace 8 = refl
  digitChar-not-isHSpace 9 = refl
  digitChar-not-isHSpace
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

-- ============================================================================
-- Shape rewrite: emitEnvVar-chars-shape
-- ============================================================================
--
-- `emitEnvVar-chars ev ++ suffix` reassociates as the parser consumes
-- it.  Five `++-assoc` applications push `suffix` past the five
-- abstract segments (name, vt-chars, min-chars, max-chars, ini-chars);
-- concrete `toList "..."` chunks ride through via `(c ∷ cs) ++ ys =
-- c ∷ (cs ++ ys)` definitional reduction, so they don't need explicit
-- ++-assoc steps.
private
  emitEnvVar-chars-shape :
      ∀ (ev : EnvironmentVar) (suffix : List Char)
    → emitEnvVar-chars ev ++ₗ suffix
      ≡ toList "EV_ "
          ++ₗ (Identifier.name (EnvironmentVar.name ev)
                ++ₗ ':' ∷ ' ' ∷
                     (emitVarType-chars (EnvironmentVar.varType ev)
                       ++ₗ ' ' ∷ '[' ∷
                            (showDecRat-dec-chars (EnvironmentVar.minimum ev)
                              ++ₗ '|' ∷
                                   (showDecRat-dec-chars (EnvironmentVar.maximum ev)
                                     ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                                          (showDecRat-dec-chars (EnvironmentVar.initial ev)
                                            ++ₗ ' ' ∷ '0' ∷
                                                 toList " DUMMY_NODE_VECTOR0"
                                                   ++ₗ toList " Vector__XXX"
                                                         ++ₗ ';' ∷ '\n' ∷ suffix)))))
  emitEnvVar-chars-shape ev suffix =
    let nm-chars  = Identifier.name (EnvironmentVar.name ev)
        vt-chars  = emitVarType-chars (EnvironmentVar.varType ev)
        min-chars = showDecRat-dec-chars (EnvironmentVar.minimum ev)
        max-chars = showDecRat-dec-chars (EnvironmentVar.maximum ev)
        ini-chars = showDecRat-dec-chars (EnvironmentVar.initial ev)
        tail-fixed : List Char
        tail-fixed = toList " 0"
                       ++ₗ toList " DUMMY_NODE_VECTOR0"
                             ++ₗ toList " Vector__XXX"
                                   ++ₗ toList ";\n"
        S5 : List Char
        S5 = ini-chars ++ₗ tail-fixed
    in
    -- Outer push: (toList "EV_ " ++ X) ++ suffix = toList "EV_ " ++ (X ++ suffix)
    -- by ++-assoc.  X = nm-chars ++ rest.
    trans
      (++ₗ-assoc (toList "EV_ ")
                 (nm-chars
                    ++ₗ toList ": "
                          ++ₗ vt-chars
                                ++ₗ toList " ["
                                      ++ₗ min-chars
                                            ++ₗ '|' ∷ max-chars
                                                  ++ₗ toList "]"
                                                        ++ₗ toList " \"\" "
                                                              ++ₗ S5)
                 suffix)
    -- Push suffix through nm-chars.
    (trans
      (cong (toList "EV_ " ++ₗ_)
            (++ₗ-assoc nm-chars
                       (toList ": "
                          ++ₗ vt-chars
                                ++ₗ toList " ["
                                      ++ₗ min-chars
                                            ++ₗ '|' ∷ max-chars
                                                  ++ₗ toList "]"
                                                        ++ₗ toList " \"\" "
                                                              ++ₗ S5)
                       suffix))
    -- Push suffix through vt-chars.  After cons-absorb of toList ": ",
    -- the next abstract segment is vt-chars.
    (trans
      (cong (λ x → toList "EV_ " ++ₗ (nm-chars ++ₗ ':' ∷ ' ' ∷ x))
            (++ₗ-assoc vt-chars
                       (toList " ["
                          ++ₗ min-chars
                                ++ₗ '|' ∷ max-chars
                                      ++ₗ toList "]"
                                            ++ₗ toList " \"\" "
                                                  ++ₗ S5)
                       suffix))
    -- Push suffix through min-chars.
    (trans
      (cong (λ x → toList "EV_ " ++ₗ
                     (nm-chars ++ₗ
                        ':' ∷ ' ' ∷
                          (vt-chars ++ₗ
                             ' ' ∷ '[' ∷ x)))
            (++ₗ-assoc min-chars
                       ('|' ∷ max-chars
                          ++ₗ toList "]"
                                ++ₗ toList " \"\" "
                                      ++ₗ S5)
                       suffix))
    -- Push suffix through max-chars.
    (trans
      (cong (λ x → toList "EV_ " ++ₗ
                     (nm-chars ++ₗ
                        ':' ∷ ' ' ∷
                          (vt-chars ++ₗ
                             ' ' ∷ '[' ∷
                               (min-chars ++ₗ '|' ∷ x))))
            (++ₗ-assoc max-chars
                       (toList "]"
                          ++ₗ toList " \"\" "
                                ++ₗ S5)
                       suffix))
    -- Push suffix through ini-chars (last abstract segment).
    (cong (λ x → toList "EV_ " ++ₗ
                   (nm-chars ++ₗ
                      ':' ∷ ' ' ∷
                        (vt-chars ++ₗ
                           ' ' ∷ '[' ∷
                             (min-chars ++ₗ
                                '|' ∷
                                  (max-chars ++ₗ
                                     ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷ x)))))
          (++ₗ-assoc ini-chars tail-fixed suffix))))))

-- ============================================================================
-- Main theorem
-- ============================================================================

parseEnvVar-roundtrip :
    ∀ (pos : Position) (ev : EnvironmentVar) (suffix : List Char)
  → EnvVarNameStop ev
  → SuffixStops isNewlineStart suffix
  → parseEnvVar pos (emitEnvVar-chars ev ++ₗ suffix)
    ≡ just (mkResult ev
             (advancePositions pos (emitEnvVar-chars ev))
             suffix)
parseEnvVar-roundtrip pos ev suffix
    (c , cs , name-eq , c-non-hspace) nl-stop =
  trans (cong (parseEnvVar pos) (emitEnvVar-chars-shape ev suffix))
    (trans step-EV
      (trans step-WS-1
        (trans step-name
          (trans step-WSOpt-1
            (trans step-colon
              (trans step-WS-2
                (trans step-vt
                  (trans step-WS-3
                    (trans step-lbrack
                      (trans step-min
                        (trans step-pipe
                          (trans step-max
                            (trans step-rbrack
                              (trans step-WS-4
                                (trans step-unit
                                  (trans step-WS-5
                                    (trans step-ini
                                      (trans step-WS-6
                                        (trans step-envid
                                          (trans step-WS-7
                                            (trans step-atype
                                              (trans step-WS-8
                                                (trans step-anode
                                                  (trans step-WSOpt-2
                                                    (trans step-semi
                                                      (trans step-LF
                                                        (trans step-manyLF
                                                          step-pure)))))))))))))))))))))))))))
  where
    nm-chars : List Char
    nm-chars = Identifier.name (EnvironmentVar.name ev)

    nm-id : Identifier
    nm-id = EnvironmentVar.name ev

    vt : VarType
    vt = EnvironmentVar.varType ev

    vt-chars : List Char
    vt-chars = emitVarType-chars vt

    min : _
    min = EnvironmentVar.minimum ev

    max : _
    max = EnvironmentVar.maximum ev

    ini : _
    ini = EnvironmentVar.initial ev

    min-chars : List Char
    min-chars = showDecRat-dec-chars min

    max-chars : List Char
    max-chars = showDecRat-dec-chars max

    ini-chars : List Char
    ini-chars = showDecRat-dec-chars ini

    -- Intermediate positions (one per parser step).
    p-EV       = advancePositions pos (toList "EV_")
    p-ws1      = advancePosition p-EV ' '
    p-name     = advancePositions p-ws1 nm-chars
    p-wsopt-1  = p-name           -- parseWSOpt reads 0 hspaces
    p-colon    = advancePosition p-wsopt-1 ':'
    p-ws2      = advancePosition p-colon ' '
    p-vt       = advancePositions p-ws2 vt-chars
    p-ws3      = advancePosition p-vt ' '
    p-lbrack   = advancePosition p-ws3 '['
    p-min      = advancePositions p-lbrack min-chars
    p-pipe     = advancePosition p-min '|'
    p-max      = advancePositions p-pipe max-chars
    p-rbrack   = advancePosition p-max ']'
    p-ws4      = advancePosition p-rbrack ' '
    p-unit     = advancePositions p-ws4 (quoteStringLit-chars [])
    p-ws5      = advancePosition p-unit ' '
    p-ini      = advancePositions p-ws5 ini-chars
    p-ws6      = advancePosition p-ini ' '
    p-envid    = advancePositions p-ws6 (showNat-chars 0)
    p-ws7      = advancePosition p-envid ' '
    p-atype    = advancePositions p-ws7 (toList "DUMMY_NODE_VECTOR0")
    p-ws8      = advancePosition p-atype ' '
    p-anode    = advancePositions p-ws8 (toList "Vector__XXX")
    p-wsopt-2  = p-anode          -- parseWSOpt reads 0 hspaces
    p-semi     = advancePosition p-wsopt-2 ';'
    p-lf       = advancePosition p-semi '\n'

    -- Intermediate inputs (one per parser step).
    in-name    : List Char
    in-name    =
      nm-chars ++ₗ ':' ∷ ' ' ∷
        (vt-chars ++ₗ ' ' ∷ '[' ∷
          (min-chars ++ₗ '|' ∷
            (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
              (ini-chars ++ₗ ' ' ∷ '0' ∷
                toList " DUMMY_NODE_VECTOR0"
                  ++ₗ toList " Vector__XXX"
                        ++ₗ ';' ∷ '\n' ∷ suffix))))

    in-EV      : List Char
    in-EV      = ' ' ∷ in-name

    in-wsopt-1 : List Char
    in-wsopt-1 =
      ':' ∷ ' ' ∷
        (vt-chars ++ₗ ' ' ∷ '[' ∷
          (min-chars ++ₗ '|' ∷
            (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
              (ini-chars ++ₗ ' ' ∷ '0' ∷
                toList " DUMMY_NODE_VECTOR0"
                  ++ₗ toList " Vector__XXX"
                        ++ₗ ';' ∷ '\n' ∷ suffix))))

    in-colon   : List Char
    in-colon   = in-wsopt-1                     -- same: colon expected at head

    in-ws2     : List Char
    in-ws2     =
      ' ' ∷
        (vt-chars ++ₗ ' ' ∷ '[' ∷
          (min-chars ++ₗ '|' ∷
            (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
              (ini-chars ++ₗ ' ' ∷ '0' ∷
                toList " DUMMY_NODE_VECTOR0"
                  ++ₗ toList " Vector__XXX"
                        ++ₗ ';' ∷ '\n' ∷ suffix))))

    in-vt      : List Char
    in-vt      =
      vt-chars ++ₗ ' ' ∷ '[' ∷
        (min-chars ++ₗ '|' ∷
          (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
            (ini-chars ++ₗ ' ' ∷ '0' ∷
              toList " DUMMY_NODE_VECTOR0"
                ++ₗ toList " Vector__XXX"
                      ++ₗ ';' ∷ '\n' ∷ suffix)))

    in-ws3     : List Char
    in-ws3     =
      ' ' ∷ '[' ∷
        (min-chars ++ₗ '|' ∷
          (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
            (ini-chars ++ₗ ' ' ∷ '0' ∷
              toList " DUMMY_NODE_VECTOR0"
                ++ₗ toList " Vector__XXX"
                      ++ₗ ';' ∷ '\n' ∷ suffix)))

    in-lbrack  : List Char
    in-lbrack  =
      '[' ∷
        (min-chars ++ₗ '|' ∷
          (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
            (ini-chars ++ₗ ' ' ∷ '0' ∷
              toList " DUMMY_NODE_VECTOR0"
                ++ₗ toList " Vector__XXX"
                      ++ₗ ';' ∷ '\n' ∷ suffix)))

    in-min     : List Char
    in-min     =
      min-chars ++ₗ '|' ∷
        (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
          (ini-chars ++ₗ ' ' ∷ '0' ∷
            toList " DUMMY_NODE_VECTOR0"
              ++ₗ toList " Vector__XXX"
                    ++ₗ ';' ∷ '\n' ∷ suffix))

    in-pipe    : List Char
    in-pipe    =
      '|' ∷
        (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
          (ini-chars ++ₗ ' ' ∷ '0' ∷
            toList " DUMMY_NODE_VECTOR0"
              ++ₗ toList " Vector__XXX"
                    ++ₗ ';' ∷ '\n' ∷ suffix))

    in-max     : List Char
    in-max     =
      max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
        (ini-chars ++ₗ ' ' ∷ '0' ∷
          toList " DUMMY_NODE_VECTOR0"
            ++ₗ toList " Vector__XXX"
                  ++ₗ ';' ∷ '\n' ∷ suffix)

    in-rbrack  : List Char
    in-rbrack  =
      ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
        (ini-chars ++ₗ ' ' ∷ '0' ∷
          toList " DUMMY_NODE_VECTOR0"
            ++ₗ toList " Vector__XXX"
                  ++ₗ ';' ∷ '\n' ∷ suffix)

    in-ws4     : List Char
    in-ws4     =
      ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
        (ini-chars ++ₗ ' ' ∷ '0' ∷
          toList " DUMMY_NODE_VECTOR0"
            ++ₗ toList " Vector__XXX"
                  ++ₗ ';' ∷ '\n' ∷ suffix)

    in-unit    : List Char
    in-unit    =
      '"' ∷ '"' ∷ ' ' ∷
        (ini-chars ++ₗ ' ' ∷ '0' ∷
          toList " DUMMY_NODE_VECTOR0"
            ++ₗ toList " Vector__XXX"
                  ++ₗ ';' ∷ '\n' ∷ suffix)

    in-ws5     : List Char
    in-ws5     =
      ' ' ∷
        (ini-chars ++ₗ ' ' ∷ '0' ∷
          toList " DUMMY_NODE_VECTOR0"
            ++ₗ toList " Vector__XXX"
                  ++ₗ ';' ∷ '\n' ∷ suffix)

    in-ini     : List Char
    in-ini     =
      ini-chars ++ₗ ' ' ∷ '0' ∷
        toList " DUMMY_NODE_VECTOR0"
          ++ₗ toList " Vector__XXX"
                ++ₗ ';' ∷ '\n' ∷ suffix

    in-ws6     : List Char
    in-ws6     =
      ' ' ∷ '0' ∷
        toList " DUMMY_NODE_VECTOR0"
          ++ₗ toList " Vector__XXX"
                ++ₗ ';' ∷ '\n' ∷ suffix

    in-envid   : List Char
    in-envid   =
      '0' ∷
        toList " DUMMY_NODE_VECTOR0"
          ++ₗ toList " Vector__XXX"
                ++ₗ ';' ∷ '\n' ∷ suffix

    in-ws7     : List Char
    in-ws7     =
      toList " DUMMY_NODE_VECTOR0"
        ++ₗ toList " Vector__XXX"
              ++ₗ ';' ∷ '\n' ∷ suffix

    in-atype   : List Char
    in-atype   =
      toList "DUMMY_NODE_VECTOR0"
        ++ₗ toList " Vector__XXX"
              ++ₗ ';' ∷ '\n' ∷ suffix

    in-ws8     : List Char
    in-ws8     =
      toList " Vector__XXX" ++ₗ ';' ∷ '\n' ∷ suffix

    in-anode   : List Char
    in-anode   =
      toList "Vector__XXX" ++ₗ ';' ∷ '\n' ∷ suffix

    in-wsopt-2 : List Char
    in-wsopt-2 = ';' ∷ '\n' ∷ suffix

    in-semi    : List Char
    in-semi    = in-wsopt-2

    in-lf      : List Char
    in-lf      = '\n' ∷ suffix

    in-manyLF  : List Char
    in-manyLF  = suffix

    -- ----------------------------------------------------------------------
    -- Continuations (mirror parseEnvVar's do-block desugaring).  Match
    -- the source which uses `_>>=_ λ _ → ...` for discarded binds (cont
    -- shapes must use `>>= λ _ →`, not `_*>_`, since the elaborator
    -- doesn't equate them).
    -- ----------------------------------------------------------------------

    cont-EV : String → Parser EnvironmentVar
    cont-EV _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ nm →
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      parseWS >>= λ _ →
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-WS-1 : List Char → Parser EnvironmentVar
    cont-WS-1 _ =
      parseIdentifier >>= λ nm →
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      parseWS >>= λ _ →
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-name : Identifier → Parser EnvironmentVar
    cont-name nm =
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      parseWS >>= λ _ →
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-WSOpt-1 : List Char → Parser EnvironmentVar
    cont-WSOpt-1 _ =
      char ':' >>= λ _ →
      parseWS >>= λ _ →
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-colon : Char → Parser EnvironmentVar
    cont-colon _ =
      parseWS >>= λ _ →
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-WS-2 : List Char → Parser EnvironmentVar
    cont-WS-2 _ =
      parseVarType >>= λ vt' →
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-vt : VarType → Parser EnvironmentVar
    cont-vt vt' =
      parseWS >>= λ _ →
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt'; initial = ini'; minimum = mn; maximum = mx })

    cont-WS-3 : List Char → Parser EnvironmentVar
    cont-WS-3 _ =
      char '[' >>= λ _ →
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = mn; maximum = mx })

    cont-lbrack : Char → Parser EnvironmentVar
    cont-lbrack _ =
      parseDecRat >>= λ mn →
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = mn; maximum = mx })

    cont-min : _ → Parser EnvironmentVar
    cont-min mn =
      char '|' >>= λ _ →
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = mn; maximum = mx })

    cont-pipe : Char → Parser EnvironmentVar
    cont-pipe _ =
      parseDecRat >>= λ mx →
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = mx })

    cont-max : _ → Parser EnvironmentVar
    cont-max mx =
      char ']' >>= λ _ →
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = mx })

    cont-rbrack : Char → Parser EnvironmentVar
    cont-rbrack _ =
      parseWS >>= λ _ →
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = max })

    cont-WS-4 : List Char → Parser EnvironmentVar
    cont-WS-4 _ =
      parseStringLit >>= λ _ →
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = max })

    cont-unit : List Char → Parser EnvironmentVar
    cont-unit _ =
      parseWS >>= λ _ →
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = max })

    cont-WS-5 : List Char → Parser EnvironmentVar
    cont-WS-5 _ =
      parseDecRat >>= λ ini' →
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = max })

    cont-ini : _ → Parser EnvironmentVar
    cont-ini ini' =
      parseWS >>= λ _ →
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini'; minimum = min; maximum = max })

    cont-WS-6 : List Char → Parser EnvironmentVar
    cont-WS-6 _ =
      parseNatural >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-envid : ℕ → Parser EnvironmentVar
    cont-envid _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-WS-7 : List Char → Parser EnvironmentVar
    cont-WS-7 _ =
      parseIdentifier >>= λ _ →
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-atype : Identifier → Parser EnvironmentVar
    cont-atype _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-WS-8 : List Char → Parser EnvironmentVar
    cont-WS-8 _ =
      parseIdentifier >>= λ _ →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-anode : Identifier → Parser EnvironmentVar
    cont-anode _ =
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-WSOpt-2 : List Char → Parser EnvironmentVar
    cont-WSOpt-2 _ =
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-semi : Char → Parser EnvironmentVar
    cont-semi _ =
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-LF : Char → Parser EnvironmentVar
    cont-LF _ =
      many parseNewline >>= λ _ →
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    cont-manyLF : List Char → Parser EnvironmentVar
    cont-manyLF _ =
      pure (record { name = nm-id; varType = vt; initial = ini; minimum = min; maximum = max })

    -- ----------------------------------------------------------------------
    -- Steps
    -- ----------------------------------------------------------------------

    -- Step 1: string "EV_" matches.
    step-EV :
      parseEnvVar pos (toList "EV_ " ++ₗ in-name)
      ≡ cont-EV "EV_" p-EV in-EV
    step-EV =
      bind-just-step (string "EV_")
                     cont-EV
                     pos (toList "EV_ " ++ₗ in-name)
                     "EV_" p-EV in-EV
                     (string-success pos "EV_" in-EV)

    -- Step 2: parseWS consumes the single ` ` separator.
    --   `SuffixStops isHSpace in-name` — head of in-name is the first
    --   char of nm-chars, which is `c` (non-hspace via EnvVarNameStop).
    name-ss : SuffixStops isHSpace in-name
    name-ss =
      subst (λ xs → SuffixStops isHSpace
                      (xs ++ₗ ':' ∷ ' ' ∷
                                (vt-chars ++ₗ ' ' ∷ '[' ∷
                                  (min-chars ++ₗ '|' ∷
                                    (max-chars ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                                      (ini-chars ++ₗ ' ' ∷ '0' ∷
                                        toList " DUMMY_NODE_VECTOR0"
                                          ++ₗ toList " Vector__XXX"
                                                ++ₗ ';' ∷ '\n' ∷ suffix))))))
            (sym name-eq)
            (∷-stop c-non-hspace)

    step-WS-1 :
      cont-EV "EV_" p-EV in-EV
      ≡ cont-WS-1 (' ' ∷ []) p-ws1 in-name
    step-WS-1 =
      bind-just-step parseWS
                     cont-WS-1
                     p-EV in-EV
                     (' ' ∷ []) p-ws1 in-name
                     (parseWS-one-space p-EV in-name name-ss)

    -- Step 3: parseIdentifier reads nm-chars.  SuffixStops isIdentCont
    -- on rest is `':' ∷ ...`, isIdentCont ':' = false.
    ident-stop-name : SuffixStops isIdentCont in-wsopt-1
    ident-stop-name = ∷-stop refl

    step-name :
      cont-WS-1 (' ' ∷ []) p-ws1 in-name
      ≡ cont-name nm-id p-name in-wsopt-1
    step-name =
      bind-just-step parseIdentifier
                     cont-name
                     p-ws1 in-name
                     nm-id p-name in-wsopt-1
                     (parseIdentifier-roundtrip
                        p-ws1 nm-id in-wsopt-1 ident-stop-name)

    -- Step 4: parseWSOpt reads 0 hspaces (head of in-wsopt-1 is `':'`).
    wsopt-1-ss : SuffixStops isHSpace in-wsopt-1
    wsopt-1-ss = ∷-stop refl

    step-WSOpt-1 :
      cont-name nm-id p-name in-wsopt-1
      ≡ cont-WSOpt-1 [] p-wsopt-1 in-wsopt-1
    step-WSOpt-1 =
      bind-just-step parseWSOpt
                     cont-WSOpt-1
                     p-name in-wsopt-1
                     [] p-wsopt-1 in-wsopt-1
                     (manyHelper-satisfy-exhaust-many isHSpace p-name
                        [] in-wsopt-1
                        All.[] wsopt-1-ss)

    -- Step 5: char ':' matches.
    step-colon :
      cont-WSOpt-1 [] p-wsopt-1 in-wsopt-1
      ≡ cont-colon ':' p-colon in-ws2
    step-colon =
      bind-just-step (char ':')
                     cont-colon
                     p-wsopt-1 in-wsopt-1
                     ':' p-colon in-ws2
                     (char-matches ':' p-wsopt-1 in-ws2)

    -- Step 6: parseWS consumes the ` ` after `:`.  Head of in-vt is
    -- the first char of vt-chars; vt-chars is one of `'0'∷[]`,
    -- `'1'∷[]`, `'2'∷[]` (case-split below).
    ws-2-ss : SuffixStops isHSpace in-vt
    ws-2-ss with vt
    ... | IntVar    = ∷-stop refl
    ... | FloatVar  = ∷-stop refl
    ... | StringVar = ∷-stop refl

    step-WS-2 :
      cont-colon ':' p-colon in-ws2
      ≡ cont-WS-2 (' ' ∷ []) p-ws2 in-vt
    step-WS-2 =
      bind-just-step parseWS
                     cont-WS-2
                     p-colon in-ws2
                     (' ' ∷ []) p-ws2 in-vt
                     (parseWS-one-space p-colon in-vt ws-2-ss)

    -- Step 7: parseVarType reads the digit.
    step-vt :
      cont-WS-2 (' ' ∷ []) p-ws2 in-vt
      ≡ cont-vt vt p-vt in-ws3
    step-vt =
      bind-just-step parseVarType
                     cont-vt
                     p-ws2 in-vt
                     vt p-vt in-ws3
                     (parseVarType-roundtrip vt p-ws2 in-ws3)

    -- Step 8: parseWS consumes ` ` before `[`.
    ws-3-ss : SuffixStops isHSpace in-lbrack
    ws-3-ss = ∷-stop refl

    step-WS-3 :
      cont-vt vt p-vt in-ws3
      ≡ cont-WS-3 (' ' ∷ []) p-ws3 in-lbrack
    step-WS-3 =
      bind-just-step parseWS
                     cont-WS-3
                     p-vt in-ws3
                     (' ' ∷ []) p-ws3 in-lbrack
                     (parseWS-one-space p-vt in-lbrack ws-3-ss)

    -- Step 9: char '[' matches.
    step-lbrack :
      cont-WS-3 (' ' ∷ []) p-ws3 in-lbrack
      ≡ cont-lbrack '[' p-lbrack in-min
    step-lbrack =
      bind-just-step (char '[')
                     cont-lbrack
                     p-ws3 in-lbrack
                     '[' p-lbrack in-min
                     (char-matches '[' p-ws3 in-min)

    -- Step 10: parseDecRat reads min-chars.  Suffix = '|' ∷ ...,
    -- isDigit '|' = false.
    step-min :
      cont-lbrack '[' p-lbrack in-min
      ≡ cont-min min p-min in-pipe
    step-min =
      bind-just-step parseDecRat
                     cont-min
                     p-lbrack in-min
                     min p-min in-pipe
                     (parseDecRat-roundtrip-suffix min p-lbrack in-pipe
                        (∷-stop refl))

    -- Step 11: char '|' matches.
    step-pipe :
      cont-min min p-min in-pipe
      ≡ cont-pipe '|' p-pipe in-max
    step-pipe =
      bind-just-step (char '|')
                     cont-pipe
                     p-min in-pipe
                     '|' p-pipe in-max
                     (char-matches '|' p-min in-max)

    -- Step 12: parseDecRat reads max-chars.  Suffix = ']' ∷ ...,
    -- isDigit ']' = false.
    step-max :
      cont-pipe '|' p-pipe in-max
      ≡ cont-max max p-max in-rbrack
    step-max =
      bind-just-step parseDecRat
                     cont-max
                     p-pipe in-max
                     max p-max in-rbrack
                     (parseDecRat-roundtrip-suffix max p-pipe in-rbrack
                        (∷-stop refl))

    -- Step 13: char ']' matches.
    step-rbrack :
      cont-max max p-max in-rbrack
      ≡ cont-rbrack ']' p-rbrack in-ws4
    step-rbrack =
      bind-just-step (char ']')
                     cont-rbrack
                     p-max in-rbrack
                     ']' p-rbrack in-ws4
                     (char-matches ']' p-max in-ws4)

    -- Step 14: parseWS consumes ` ` before `""`.
    ws-4-ss : SuffixStops isHSpace in-unit
    ws-4-ss = ∷-stop refl

    step-WS-4 :
      cont-rbrack ']' p-rbrack in-ws4
      ≡ cont-WS-4 (' ' ∷ []) p-ws4 in-unit
    step-WS-4 =
      bind-just-step parseWS
                     cont-WS-4
                     p-rbrack in-ws4
                     (' ' ∷ []) p-ws4 in-unit
                     (parseWS-one-space p-rbrack in-unit ws-4-ss)

    -- Step 15: parseStringLit reads `""` (empty string lit).
    -- `quoteStringLit-chars "" = '"' ∷ '"' ∷ []`.  Suffix = ' ' ∷ ...,
    -- which is NOT a `'"' ∷ ...` boundary — but the stop predicate is
    -- on `_≈ᵇ '"'`, and `' ' ≈ᵇ '"' = false`.
    unit-quote-ss : SuffixStops (λ ch → ch ≈ᵇ '"') in-ws5
    unit-quote-ss = ∷-stop refl

    step-unit :
      cont-WS-4 (' ' ∷ []) p-ws4 in-unit
      ≡ cont-unit [] p-unit in-ws5
    step-unit =
      bind-just-step parseStringLit
                     cont-unit
                     p-ws4 in-unit
                     [] p-unit in-ws5
                     (parseStringLit-roundtrip p-ws4 [] in-ws5 unit-quote-ss)

    -- Step 16: parseWS consumes ` ` before ini-chars.  Head of in-ini
    -- is the first char of ini-chars (showDecRat-dec-chars d).  All
    -- DecRat emissions begin with either `-` or a digit, neither of
    -- which is hspace.
    ws-5-ss : SuffixStops isHSpace in-ini
    ws-5-ss = decrat-suffix-stop ini
      (' ' ∷ '0' ∷
        toList " DUMMY_NODE_VECTOR0"
          ++ₗ toList " Vector__XXX"
                ++ₗ ';' ∷ '\n' ∷ suffix)
      where
        decrat-suffix-stop : ∀ (d : DecRat) (rest : List Char)
          → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ rest)
        decrat-suffix-stop (mkDecRat ℤ-[1+ n ] a b cx) rest
          with showDecRat-chars-head-dash n a b cx
        ... | tail , eq =
              subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
                    (sym eq) (∷-stop refl)
        decrat-suffix-stop (mkDecRat (ℤ+ absNum) a b cx) rest
          with showDecRat-chars-head-digit absNum a b cx
        ... | k , tail , k<10 , eq =
              subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
                    (sym eq) (∷-stop (digitChar-not-isHSpace k))

    step-WS-5 :
      cont-unit [] p-unit in-ws5
      ≡ cont-WS-5 (' ' ∷ []) p-ws5 in-ini
    step-WS-5 =
      bind-just-step parseWS
                     cont-WS-5
                     p-unit in-ws5
                     (' ' ∷ []) p-ws5 in-ini
                     (parseWS-one-space p-unit in-ini ws-5-ss)

    -- Step 17: parseDecRat reads ini-chars.  Suffix = ' ' ∷ '0' ∷ ...,
    -- isDigit ' ' = false.
    step-ini :
      cont-WS-5 (' ' ∷ []) p-ws5 in-ini
      ≡ cont-ini ini p-ini in-ws6
    step-ini =
      bind-just-step parseDecRat
                     cont-ini
                     p-ws5 in-ini
                     ini p-ini in-ws6
                     (parseDecRat-roundtrip-suffix ini p-ws5 in-ws6
                        (∷-stop refl))

    -- Step 18: parseWS consumes ' ' before env_id digit.
    ws-6-ss : SuffixStops isHSpace in-envid
    ws-6-ss = ∷-stop refl

    step-WS-6 :
      cont-ini ini p-ini in-ws6
      ≡ cont-WS-6 (' ' ∷ []) p-ws6 in-envid
    step-WS-6 =
      bind-just-step parseWS
                     cont-WS-6
                     p-ini in-ws6
                     (' ' ∷ []) p-ws6 in-envid
                     (parseWS-one-space p-ini in-envid ws-6-ss)

    -- Step 19: parseNatural reads "0" (the env_id placeholder).
    -- showNat-chars 0 = '0' ∷ [], so the input form `0' ∷ rest` aligns
    -- with `parseNatural-showNat-chars` after rewriting `'0' ∷ rest` as
    -- `showNat-chars 0 ++ rest` (definitional).
    step-envid :
      cont-WS-6 (' ' ∷ []) p-ws6 in-envid
      ≡ cont-envid 0 p-envid in-ws7
    step-envid =
      bind-just-step parseNatural
                     cont-envid
                     p-ws6 in-envid
                     0 p-envid in-ws7
                     (parseNatural-showNat-chars p-ws6 0 in-ws7
                        (∷-stop refl))

    -- Step 20: parseWS consumes ' ' before access_type identifier.
    ws-7-ss : SuffixStops isHSpace in-atype
    ws-7-ss = ∷-stop refl

    step-WS-7 :
      cont-envid 0 p-envid in-ws7
      ≡ cont-WS-7 (' ' ∷ []) p-ws7 in-atype
    step-WS-7 =
      bind-just-step parseWS
                     cont-WS-7
                     p-envid in-ws7
                     (' ' ∷ []) p-ws7 in-atype
                     (parseWS-one-space p-envid in-atype ws-7-ss)

    -- Step 21: parseIdentifier reads DUMMY_NODE_VECTOR0.
    --   Suffix is ' ' ∷ ... (in-ws8); isIdentCont ' ' = false.
    ident-stop-atype : SuffixStops isIdentCont in-ws8
    ident-stop-atype = ∷-stop refl

    step-atype :
      cont-WS-7 (' ' ∷ []) p-ws7 in-atype
      ≡ cont-atype ident-DummyNode p-atype in-ws8
    step-atype =
      bind-just-step parseIdentifier
                     cont-atype
                     p-ws7 in-atype
                     ident-DummyNode p-atype in-ws8
                     (parseIdentifier-roundtrip
                        p-ws7 ident-DummyNode in-ws8 ident-stop-atype)

    -- Step 22: parseWS consumes ' ' before access_node identifier.
    ws-8-ss : SuffixStops isHSpace in-anode
    ws-8-ss = ∷-stop refl

    step-WS-8 :
      cont-atype ident-DummyNode p-atype in-ws8
      ≡ cont-WS-8 (' ' ∷ []) p-ws8 in-anode
    step-WS-8 =
      bind-just-step parseWS
                     cont-WS-8
                     p-atype in-ws8
                     (' ' ∷ []) p-ws8 in-anode
                     (parseWS-one-space p-atype in-anode ws-8-ss)

    -- Step 23: parseIdentifier reads Vector__XXX.
    ident-stop-anode : SuffixStops isIdentCont in-wsopt-2
    ident-stop-anode = ∷-stop refl

    step-anode :
      cont-WS-8 (' ' ∷ []) p-ws8 in-anode
      ≡ cont-anode ident-VectorXXX p-anode in-wsopt-2
    step-anode =
      bind-just-step parseIdentifier
                     cont-anode
                     p-ws8 in-anode
                     ident-VectorXXX p-anode in-wsopt-2
                     (parseIdentifier-roundtrip
                        p-ws8 ident-VectorXXX in-wsopt-2 ident-stop-anode)

    -- Step 24: parseWSOpt reads 0 hspaces (head of in-wsopt-2 is ';').
    wsopt-2-ss : SuffixStops isHSpace in-wsopt-2
    wsopt-2-ss = ∷-stop refl

    step-WSOpt-2 :
      cont-anode ident-VectorXXX p-anode in-wsopt-2
      ≡ cont-WSOpt-2 [] p-wsopt-2 in-wsopt-2
    step-WSOpt-2 =
      bind-just-step parseWSOpt
                     cont-WSOpt-2
                     p-anode in-wsopt-2
                     [] p-wsopt-2 in-wsopt-2
                     (manyHelper-satisfy-exhaust-many isHSpace p-anode
                        [] in-wsopt-2
                        All.[] wsopt-2-ss)

    -- Step 25: char ';' matches.
    step-semi :
      cont-WSOpt-2 [] p-wsopt-2 in-wsopt-2
      ≡ cont-semi ';' p-semi in-lf
    step-semi =
      bind-just-step (char ';')
                     cont-semi
                     p-wsopt-2 in-wsopt-2
                     ';' p-semi in-lf
                     (char-matches ';' p-wsopt-2 in-lf)

    -- Step 26: parseNewline matches '\n'.
    step-LF :
      cont-semi ';' p-semi in-lf
      ≡ cont-LF '\n' p-lf in-manyLF
    step-LF =
      bind-just-step parseNewline
                     cont-LF
                     p-semi in-lf
                     '\n' p-lf in-manyLF
                     (parseNewline-match-LF p-semi suffix)

    -- Step 27: many parseNewline reads 0 (suffix is at NewlineStart-stop).
    step-manyLF :
      cont-LF '\n' p-lf in-manyLF
      ≡ cont-manyLF [] p-lf in-manyLF
    step-manyLF =
      bind-just-step (many parseNewline)
                     cont-manyLF
                     p-lf in-manyLF
                     [] p-lf in-manyLF
                     (manyHelper-parseNewline-exhaust p-lf suffix
                        (length suffix) nl-stop)

    -- Step 28: pure-step.  Build `p-lf ≡ advancePositions pos
    -- (emitEnvVar-chars ev)` via the parsed-shape `full-list` (the [] -
    -- suffix of `emitEnvVar-chars-shape`) plus a chain of
    -- `advancePositions-++` splits at each abstract-segment boundary.
    pos-final-eq : p-lf ≡ advancePositions pos (emitEnvVar-chars ev)
    pos-final-eq = pos-final-helper
      where
        full-list : List Char
        full-list =
          toList "EV_ "
            ++ₗ (nm-chars
                  ++ₗ ':' ∷ ' ' ∷
                       (vt-chars
                         ++ₗ ' ' ∷ '[' ∷
                              (min-chars
                                ++ₗ '|' ∷
                                     (max-chars
                                       ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                                            (ini-chars
                                              ++ₗ ' ' ∷ '0' ∷
                                                   toList " DUMMY_NODE_VECTOR0"
                                                     ++ₗ toList " Vector__XXX"
                                                           ++ₗ ';' ∷ '\n' ∷ [])))))

        -- Tails after each abstract-segment boundary, used in the
        -- `advancePositions-++` chain below.
        T-name : List Char
        T-name =
          ':' ∷ ' ' ∷
            (vt-chars
              ++ₗ ' ' ∷ '[' ∷
                   (min-chars
                     ++ₗ '|' ∷
                          (max-chars
                            ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                                 (ini-chars
                                   ++ₗ ' ' ∷ '0' ∷
                                        toList " DUMMY_NODE_VECTOR0"
                                          ++ₗ toList " Vector__XXX"
                                                ++ₗ ';' ∷ '\n' ∷ []))))

        T-vt : List Char
        T-vt =
          ' ' ∷ '[' ∷
            (min-chars
              ++ₗ '|' ∷
                   (max-chars
                     ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                          (ini-chars
                            ++ₗ ' ' ∷ '0' ∷
                                 toList " DUMMY_NODE_VECTOR0"
                                   ++ₗ toList " Vector__XXX"
                                         ++ₗ ';' ∷ '\n' ∷ [])))

        T-min : List Char
        T-min =
          '|' ∷
            (max-chars
              ++ₗ ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
                   (ini-chars
                     ++ₗ ' ' ∷ '0' ∷
                          toList " DUMMY_NODE_VECTOR0"
                            ++ₗ toList " Vector__XXX"
                                  ++ₗ ';' ∷ '\n' ∷ []))

        T-max : List Char
        T-max =
          ']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷
            (ini-chars
              ++ₗ ' ' ∷ '0' ∷
                   toList " DUMMY_NODE_VECTOR0"
                     ++ₗ toList " Vector__XXX"
                           ++ₗ ';' ∷ '\n' ∷ [])

        T-ini : List Char
        T-ini =
          ' ' ∷ '0' ∷
            toList " DUMMY_NODE_VECTOR0"
              ++ₗ toList " Vector__XXX"
                    ++ₗ ';' ∷ '\n' ∷ []

        -- Chain of `advancePositions-++` splits.  Each `trans` step
        -- pushes the running position one boundary forward.  Concrete
        -- cons-list chunks (toList "EV_ ", ":  ", " [", "] \"\" ", " 0",
        -- " DUMMY_...", " Vector...", ";\n") fold into the position
        -- definitionally between explicit splits.
        pos-as-advancePositions :
          advancePositions pos full-list ≡ p-lf
        pos-as-advancePositions =
          trans
            (advancePositions-++ pos (toList "EV_ ") (nm-chars ++ₗ T-name))
            (trans
              (advancePositions-++ p-ws1 nm-chars T-name)
              (trans
                (advancePositions-++ p-name (':' ∷ ' ' ∷ []) (vt-chars ++ₗ T-vt))
                (trans
                  (advancePositions-++ p-ws2 vt-chars T-vt)
                  (trans
                    (advancePositions-++ p-vt (' ' ∷ '[' ∷ []) (min-chars ++ₗ T-min))
                    (trans
                      (advancePositions-++ p-lbrack min-chars T-min)
                      (trans
                        (advancePositions-++ p-min ('|' ∷ []) (max-chars ++ₗ T-max))
                        (trans
                          (advancePositions-++ p-pipe max-chars T-max)
                          (trans
                            (advancePositions-++ p-max
                              (']' ∷ ' ' ∷ '"' ∷ '"' ∷ ' ' ∷ [])
                              (ini-chars ++ₗ T-ini))
                            (trans
                              (advancePositions-++ p-ws5 ini-chars T-ini)
                              -- After ini-chars, the remaining tail is all
                              -- concrete cons cells: ' ' '0' ' ' DUMMY...
                              -- ' ' Vector... ';' '\n'.  Each absorbs into
                              -- the position definitionally.
                              refl)))))))))

        shape-no-suffix : full-list ≡ emitEnvVar-chars ev
        shape-no-suffix =
          trans (sym (emitEnvVar-chars-shape ev []))
                (++-identityʳ (emitEnvVar-chars ev))

        pos-final-helper : p-lf ≡ advancePositions pos (emitEnvVar-chars ev)
        pos-final-helper =
          trans (sym pos-as-advancePositions)
                (cong (advancePositions pos) shape-no-suffix)

    step-pure :
      cont-manyLF [] p-lf in-manyLF
      ≡ just (mkResult ev
               (advancePositions pos (emitEnvVar-chars ev))
               suffix)
    step-pure =
      trans
        (cong (λ p →
                 just (mkResult
                         (record { name = nm-id; varType = vt;
                                   initial = ini; minimum = min; maximum = max })
                         p suffix))
              pos-final-eq)
        (cong (λ result →
                 just (mkResult result
                                (advancePositions pos (emitEnvVar-chars ev))
                                suffix))
              eta)
      where
        eta : record { name = nm-id; varType = vt;
                       initial = ini; minimum = min; maximum = max } ≡ ev
        eta = refl
