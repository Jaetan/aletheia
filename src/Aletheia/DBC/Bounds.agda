-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The size bounds a DBC meets before it is validated, loaded or formatted:
-- how many items each of its lists holds and how long each of its texts is.
-- `IsBoundedDBC` states them; `checkBounds` decides them, refusing with the
-- first bound crossed or returning the DBC as a `BoundedDBC`, with the
-- erased proof that it meets every one.
--
-- Order of discovery: every count before any text.  Counts: messages, then
-- per message its signals, senders, and per signal its receivers and
-- multiplex values; attributes and per attribute its enum labels; comments;
-- nodes; value tables; value descriptions in total; signal groups and per
-- group its members; environment variables; unresolved value descriptions.
-- Texts: version, per signal its unit and value labels, comments, attribute
-- names, enum labels and string values, value-table labels, unresolved
-- value labels.
--
-- Each bound is one decision, `within`, carrying its evidence erased; the
-- refusal, `InputBoundExceededAt`, is built where the decision is made and
-- names the field.  A text's length is its number of characters.  Identifiers are not walked: an `Identifier` carries its own
-- length bound.
module Aletheia.DBC.Bounds where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length)
open import Data.List.NonEmpty using () renaming (length to length⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; _+_)
open import Data.Nat.Properties using (≤ᵇ-reflects-≤)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary.Reflects using (invert)

open import Aletheia.Data.Dec0 using (Dec₀; _because₀_; dec₀)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; SignalPresence; Always; When; SignalGroup
  ; ValueTable; RawValueDesc; DBCComment; Node
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  )
open import Aletheia.Error using (Error; InputBoundExceededAt)
open import Aletheia.Limits using
  ( BoundKind; ArrayCardinality; StringLength
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-comments-per-file; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file; max-signal-groups-per-file
  ; max-environment-variables-per-file; max-unresolved-value-descriptions-per-file
  ; max-enum-labels-per-attribute; max-multiplex-values-per-signal
  ; max-string-length-characters
  )

-- ============================================================================
-- VERDICTS
-- ============================================================================

-- Evidence that exists at type-checking time only.
record Erased (A : Set) : Set where
  constructor [_]
  field
    @0 erased : A

-- A bound's verdict: the refusal, or the erased evidence that it holds.
Checked : Set → Set
Checked P = Error ⊎ Erased P

infixl 1 _>>=_

_>>=_ : ∀ {P Q : Set} → Checked P → (@0 P → Checked Q) → Checked Q
inj₁ e     >>= _ = inj₁ e
inj₂ [ p ] >>= k = k p

-- Turn a decision into a verdict, refusing with the given error.
decide : ∀ {P : Set} → Error → Dec₀ P → Checked P
decide _ (true  because₀ r) = inj₂ [ invert r ]
decide e (false because₀ _) = inj₁ e

-- The one decision every bound makes.
within : (n limit : ℕ) → Dec₀ (n ≤ limit)
within n limit = dec₀ (n ≤ᵇ limit) (≤ᵇ-reflects-≤ n limit)

bound : BoundKind → String → (n limit : ℕ) → Checked (n ≤ limit)
bound kind tag n limit =
  decide (InputBoundExceededAt tag kind n limit) (within n limit)

count : String → (n limit : ℕ) → Checked (n ≤ limit)
count = bound ArrayCardinality

ShortText : List Char → Set
ShortText cs = length cs ≤ max-string-length-characters

text : String → (cs : List Char) → Checked (ShortText cs)
text tag cs = bound StringLength tag (length cs) max-string-length-characters

-- Every item of a list, in order.  The evidence for the items already
-- passed is folded into an erased continuation, so the walk is a loop.
walk : ∀ {A : Set} {P : A → Set} {xs : List A}
     → (∀ x → Checked (P x)) → (ys : List A) → @0 (All P ys → All P xs)
     → Checked (All P xs)
walk f []       k = inj₂ [ k [] ]
walk f (y ∷ ys) k with f y
... | inj₁ e     = inj₁ e
... | inj₂ [ p ] = walk f ys (λ ps → k (p ∷ ps))

every : ∀ {A : Set} {P : A → Set} → (∀ x → Checked (P x)) → (xs : List A) → Checked (All P xs)
every f xs = walk f xs (λ ps → ps)

-- ============================================================================
-- COUNTS
-- ============================================================================

-- Value descriptions in total: per signal, per value table, and on the
-- `VAL_` lines naming no signal.
vdsInSignals : List DBCSignal → ℕ
vdsInSignals [] = 0
vdsInSignals (s ∷ rest) = length (DBCSignal.valueDescriptions s) + vdsInSignals rest

vdsInMessages : List DBCMessage → ℕ
vdsInMessages [] = 0
vdsInMessages (m ∷ rest) = vdsInSignals (DBCMessage.signals m) + vdsInMessages rest

vdsInTables : List ValueTable → ℕ
vdsInTables [] = 0
vdsInTables (t ∷ rest) = length (ValueTable.entries t) + vdsInTables rest

vdsInUnresolved : List RawValueDesc → ℕ
vdsInUnresolved [] = 0
vdsInUnresolved (rv ∷ rest) = length (RawValueDesc.entries rv) + vdsInUnresolved rest

totalValueDescriptions : DBC → ℕ
totalValueDescriptions dbc =
  vdsInMessages (DBC.messages dbc) +
  vdsInTables (DBC.valueTables dbc) +
  vdsInUnresolved (DBC.unresolvedValueDescs dbc)

SelectorCount : SignalPresence → Set
SelectorCount Always      = ⊤
SelectorCount (When _ vs) = length⁺ vs ≤ max-multiplex-values-per-signal

record SignalCounts (sig : DBCSignal) : Set where
  field
    receivers : length (CanonicalReceivers.list (DBCSignal.receivers sig)) ≤ max-nodes-per-file
    selector  : SelectorCount (DBCSignal.presence sig)

record MessageCounts (msg : DBCMessage) : Set where
  field
    signals    : length (DBCMessage.signals msg) ≤ max-signals-per-message
    senders    : length (DBCMessage.senders msg) ≤ max-nodes-per-file
    eachSignal : All SignalCounts (DBCMessage.signals msg)

LabelCount : AttrType → Set
LabelCount (ATEnum vs) = length vs ≤ max-enum-labels-per-attribute
LabelCount _           = ⊤

AttributeCounts : DBCAttribute → Set
AttributeCounts (DBCAttrDef d) = LabelCount (AttrDef.attrType d)
AttributeCounts _              = ⊤

GroupCount : SignalGroup → Set
GroupCount g = length (SignalGroup.signals g) ≤ max-signals-per-message

record DBCCounts (dbc : DBC) : Set where
  field
    messages             : length (DBC.messages dbc) ≤ max-messages-per-file
    eachMessage          : All MessageCounts (DBC.messages dbc)
    attributes           : length (DBC.attributes dbc) ≤ max-attributes-per-file
    eachAttribute        : All AttributeCounts (DBC.attributes dbc)
    comments             : length (DBC.comments dbc) ≤ max-comments-per-file
    nodes                : length (DBC.nodes dbc) ≤ max-nodes-per-file
    valueTables          : length (DBC.valueTables dbc) ≤ max-value-tables-per-file
    valueDescriptions    : totalValueDescriptions dbc ≤ max-value-descriptions-per-file
    signalGroups         : length (DBC.signalGroups dbc) ≤ max-signal-groups-per-file
    eachSignalGroup      : All GroupCount (DBC.signalGroups dbc)
    environmentVars      : length (DBC.environmentVars dbc) ≤ max-environment-variables-per-file
    unresolvedValueDescs : length (DBC.unresolvedValueDescs dbc) ≤ max-unresolved-value-descriptions-per-file

selectorCount : (p : SignalPresence) → Checked (SelectorCount p)
selectorCount Always      = inj₂ [ tt ]
selectorCount (When _ vs) = count "multiplex values array" (length⁺ vs) max-multiplex-values-per-signal

signalCounts : (sig : DBCSignal) → Checked (SignalCounts sig)
signalCounts sig =
  count "receivers array" (length (CanonicalReceivers.list (DBCSignal.receivers sig))) max-nodes-per-file >>= λ r →
  selectorCount (DBCSignal.presence sig) >>= λ s →
  inj₂ [ record { receivers = r ; selector = s } ]

messageCounts : (msg : DBCMessage) → Checked (MessageCounts msg)
messageCounts msg =
  count "signals array" (length (DBCMessage.signals msg)) max-signals-per-message >>= λ s →
  count "senders array" (length (DBCMessage.senders msg)) max-nodes-per-file >>= λ t →
  every signalCounts (DBCMessage.signals msg) >>= λ e →
  inj₂ [ record { signals = s ; senders = t ; eachSignal = e } ]

labelCount : (t : AttrType) → Checked (LabelCount t)
labelCount (ATInt _ _)   = inj₂ [ tt ]
labelCount (ATFloat _ _) = inj₂ [ tt ]
labelCount ATString      = inj₂ [ tt ]
labelCount (ATEnum vs)   = count "enum labels array" (length vs) max-enum-labels-per-attribute
labelCount (ATHex _ _)   = inj₂ [ tt ]

attributeCounts : (a : DBCAttribute) → Checked (AttributeCounts a)
attributeCounts (DBCAttrDef d)     = labelCount (AttrDef.attrType d)
attributeCounts (DBCAttrDefault _) = inj₂ [ tt ]
attributeCounts (DBCAttrAssign _)  = inj₂ [ tt ]

groupCount : (g : SignalGroup) → Checked (GroupCount g)
groupCount g = count "signal group members array" (length (SignalGroup.signals g)) max-signals-per-message

dbcCounts : (dbc : DBC) → Checked (DBCCounts dbc)
dbcCounts dbc =
  count "messages array" (length (DBC.messages dbc)) max-messages-per-file >>= λ m →
  every messageCounts (DBC.messages dbc) >>= λ ms →
  count "attributes array" (length (DBC.attributes dbc)) max-attributes-per-file >>= λ a →
  every attributeCounts (DBC.attributes dbc) >>= λ as →
  count "comments array" (length (DBC.comments dbc)) max-comments-per-file >>= λ c →
  count "nodes array" (length (DBC.nodes dbc)) max-nodes-per-file >>= λ n →
  count "value tables array" (length (DBC.valueTables dbc)) max-value-tables-per-file >>= λ t →
  count "value descriptions total" (totalValueDescriptions dbc) max-value-descriptions-per-file >>= λ v →
  count "signal groups array" (length (DBC.signalGroups dbc)) max-signal-groups-per-file >>= λ g →
  every groupCount (DBC.signalGroups dbc) >>= λ gs →
  count "environment variables array" (length (DBC.environmentVars dbc))
    max-environment-variables-per-file >>= λ e →
  count "unresolved value descriptions array" (length (DBC.unresolvedValueDescs dbc))
    max-unresolved-value-descriptions-per-file >>= λ u →
  inj₂ [ record
    { messages = m ; eachMessage = ms ; attributes = a ; eachAttribute = as
    ; comments = c ; nodes = n ; valueTables = t ; valueDescriptions = v
    ; signalGroups = g ; eachSignalGroup = gs ; environmentVars = e
    ; unresolvedValueDescs = u
    } ]

-- ============================================================================
-- TEXTS
-- ============================================================================

ShortLabels : List (ℕ × List Char) → Set
ShortLabels = All (ShortText ∘ proj₂)

record SignalTexts (sig : DBCSignal) : Set where
  field
    unit   : ShortText (DBCSignal.unit sig)
    labels : ShortLabels (DBCSignal.valueDescriptions sig)

ShortType : AttrType → Set
ShortType (ATEnum vs) = All ShortText vs
ShortType _           = ⊤

ShortValue : AttrValue → Set
ShortValue (AVString cs) = ShortText cs
ShortValue _             = ⊤

AttributeTexts : DBCAttribute → Set
AttributeTexts (DBCAttrDef d)     = ShortText (AttrDef.name d) × ShortType (AttrDef.attrType d)
AttributeTexts (DBCAttrDefault d) = ShortText (AttrDefault.name d) × ShortValue (AttrDefault.value d)
AttributeTexts (DBCAttrAssign a)  = ShortText (AttrAssign.name a) × ShortValue (AttrAssign.value a)

record DBCTexts (dbc : DBC) : Set where
  field
    version              : ShortText (DBC.version dbc)
    signals              : All (All SignalTexts ∘ DBCMessage.signals) (DBC.messages dbc)
    comments             : All (ShortText ∘ DBCComment.text) (DBC.comments dbc)
    attributes           : All AttributeTexts (DBC.attributes dbc)
    valueTables          : All (ShortLabels ∘ ValueTable.entries) (DBC.valueTables dbc)
    unresolvedValueDescs : All (ShortLabels ∘ RawValueDesc.entries) (DBC.unresolvedValueDescs dbc)

shortLabels : String → (vs : List (ℕ × List Char)) → Checked (ShortLabels vs)
shortLabels tag = every (λ e → text tag (proj₂ e))

signalTexts : (sig : DBCSignal) → Checked (SignalTexts sig)
signalTexts sig =
  text "signal text field" (DBCSignal.unit sig) >>= λ u →
  shortLabels "signal text field" (DBCSignal.valueDescriptions sig) >>= λ l →
  inj₂ [ record { unit = u ; labels = l } ]

shortType : (t : AttrType) → Checked (ShortType t)
shortType (ATInt _ _)   = inj₂ [ tt ]
shortType (ATFloat _ _) = inj₂ [ tt ]
shortType ATString      = inj₂ [ tt ]
shortType (ATEnum vs)   = every (text "attribute text field") vs
shortType (ATHex _ _)   = inj₂ [ tt ]

shortValue : (v : AttrValue) → Checked (ShortValue v)
shortValue (AVInt _)     = inj₂ [ tt ]
shortValue (AVFloat _)   = inj₂ [ tt ]
shortValue (AVString cs) = text "attribute text field" cs
shortValue (AVEnum _)    = inj₂ [ tt ]
shortValue (AVHex _)     = inj₂ [ tt ]

attributeTexts : (a : DBCAttribute) → Checked (AttributeTexts a)
attributeTexts (DBCAttrDef d) =
  text "attribute text field" (AttrDef.name d) >>= λ n →
  shortType (AttrDef.attrType d) >>= λ t → inj₂ [ (n , t) ]
attributeTexts (DBCAttrDefault d) =
  text "attribute text field" (AttrDefault.name d) >>= λ n →
  shortValue (AttrDefault.value d) >>= λ v → inj₂ [ (n , v) ]
attributeTexts (DBCAttrAssign a) =
  text "attribute text field" (AttrAssign.name a) >>= λ n →
  shortValue (AttrAssign.value a) >>= λ v → inj₂ [ (n , v) ]

dbcTexts : (dbc : DBC) → Checked (DBCTexts dbc)
dbcTexts dbc =
  text "version string" (DBC.version dbc) >>= λ v →
  every (every signalTexts ∘ DBCMessage.signals) (DBC.messages dbc) >>= λ s →
  every (text "comment text" ∘ DBCComment.text) (DBC.comments dbc) >>= λ c →
  every attributeTexts (DBC.attributes dbc) >>= λ a →
  every (shortLabels "value table label" ∘ ValueTable.entries) (DBC.valueTables dbc) >>= λ t →
  every (shortLabels "unresolved value description label" ∘ RawValueDesc.entries)
    (DBC.unresolvedValueDescs dbc) >>= λ u →
  inj₂ [ record
    { version = v ; signals = s ; comments = c ; attributes = a
    ; valueTables = t ; unresolvedValueDescs = u
    } ]

-- ============================================================================
-- THE BOUNDED DBC
-- ============================================================================

record IsBoundedDBC (dbc : DBC) : Set where
  field
    counts : DBCCounts dbc
    texts  : DBCTexts dbc

-- A DBC with the proof that it meets every bound.  `checkBounds` is its
-- producer; the proof is erased, so it costs nothing at run time.
record BoundedDBC : Set where
  constructor bounded
  field
    dbc           : DBC
    @0 isBounded  : IsBoundedDBC dbc

isBounded? : (dbc : DBC) → Checked (IsBoundedDBC dbc)
isBounded? dbc =
  dbcCounts dbc >>= λ c →
  dbcTexts dbc >>= λ t →
  inj₂ [ record { counts = c ; texts = t } ]

checkBounds : DBC → Error ⊎ BoundedDBC
checkBounds dbc with isBounded? dbc
... | inj₁ e     = inj₁ e
... | inj₂ [ p ] = inj₂ (bounded dbc p)

-- The same DBC with its node list replaced, still bounded: only the new
-- list's count is decided, the rest of the proof carries over.
withNodes : BoundedDBC → List Node → Error ⊎ BoundedDBC
withNodes (bounded d p) ns with count "nodes array" (length ns) max-nodes-per-file
... | inj₁ e     = inj₁ e
... | inj₂ [ q ] = inj₂ (bounded (record d { nodes = ns }) (record
  { counts = record
      { messages = DBCCounts.messages c ; eachMessage = DBCCounts.eachMessage c
      ; attributes = DBCCounts.attributes c ; eachAttribute = DBCCounts.eachAttribute c
      ; comments = DBCCounts.comments c ; nodes = q ; valueTables = DBCCounts.valueTables c
      ; valueDescriptions = DBCCounts.valueDescriptions c ; signalGroups = DBCCounts.signalGroups c
      ; eachSignalGroup = DBCCounts.eachSignalGroup c ; environmentVars = DBCCounts.environmentVars c
      ; unresolvedValueDescs = DBCCounts.unresolvedValueDescs c
      }
  ; texts = record
      { version = DBCTexts.version t ; signals = DBCTexts.signals t ; comments = DBCTexts.comments t
      ; attributes = DBCTexts.attributes t ; valueTables = DBCTexts.valueTables t
      ; unresolvedValueDescs = DBCTexts.unresolvedValueDescs t
      }
  }))
  where
    @0 c : DBCCounts d
    c = IsBoundedDBC.counts p
    @0 t : DBCTexts d
    t = IsBoundedDBC.texts p
