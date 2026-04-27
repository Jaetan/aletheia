{-# OPTIONS --safe --without-K #-}

-- Signal-group emitter for the DBC text format (Phase B.3.c.7; layer-1
-- form 2026-04-24).
--
-- Grammar slice emitted (mirrors `TextParser.SignalGroups`):
--   sig-group    ::= "SIG_GROUP_" ws nat ws identifier ws nat ws? ":"
--                    (ws identifier)* ws? ";" newline
--
-- Synthetic CAN ID / repetitions:
--   The Agda `SignalGroup` record only carries `name` and `signals`; the
--   owning-message CAN ID and the repetitions count are not in the core
--   (cf. `TextParser.SignalGroups` module header — cantools' Python
--   `signal_group_to_json` drops both on the way in).  The emitter
--   therefore synthesises a stable placeholder pair — CAN ID `0`,
--   repetitions `1` — which is the cantools-canonical "one rep,
--   message-agnostic" shape used by the `comments_groups.dbc` corpus for
--   groups that don't pin to a specific message.  The parser is ID-agnostic
--   (discards both nats), so the B.3.d roundtrip `parseText ∘ formatText`
--   sees a stable value regardless of what was in the original source.
--
-- Canonical spacing (cantools parity):
--   * Single space between every lexeme.  The parser accepts runs of
--     whitespace (`parseWS = some (satisfy isHSpace)`), so the roundtrip
--     `parseText ∘ formatText ≡ id` (B.3.d) composes either way.
--   * Space before `:` (the grammar's pre-`:` `ws?` slot, always filled
--     here) and no space before `;` on non-empty entry lists.  Matches
--     the corpus shape `SIG_GROUP_ 500 Electrical 1 : Voltage Current;`.
--   * Empty-signals case collapses to `: ... 1 :;\n` — no space between
--     `:` and `;`.  Grammar's `ws?` before `;` accepts the tight form;
--     the corpus never exercises it but the shape stays valid.
--
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.SignalGroups where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.String using (String; toList)

open import Aletheia.DBC.Types using (SignalGroup)

-- ============================================================================
-- SIGNAL LIST EMITTER
-- ============================================================================

-- Emits each signal name prefixed by a single space.  Empty list emits
-- `[]`, non-empty emits ` sig1 sig2 ... sigN`.  The `:`/`;` boundary
-- characters are added by the line emitter, so this helper stays
-- delimiter-agnostic.
emitSignalNames-chars : List Identifier → List Char
emitSignalNames-chars =
  foldr (λ s acc → ' ' ∷ Identifier.name s ++ₗ acc) []

-- ============================================================================
-- LINE EMITTER
-- ============================================================================

-- `SIG_GROUP_ 0 <name> 1 :<emitted-signals>;\n`.  See module header for
-- the synthetic `0`/`1` choice and the space-before-`:` /
-- no-space-before-`;` convention.
emitSignalGroup-chars : SignalGroup → List Char
emitSignalGroup-chars sg =
  toList "SIG_GROUP_ 0 " ++ₗ Identifier.name (SignalGroup.name sg) ++ₗ
  toList " 1 :" ++ₗ
  emitSignalNames-chars (SignalGroup.signals sg) ++ₗ
  toList ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

-- Zero-or-more SIG_GROUP_ lines concatenated.  Empty list emits `[]`,
-- matching cantools' behaviour on group-free databases.  Blank-line
-- separation between this section and the next is the composer's
-- responsibility.
emitSignalGroups-chars : List SignalGroup → List Char
emitSignalGroups-chars =
  foldr (λ sg acc → emitSignalGroup-chars sg ++ₗ acc) []
