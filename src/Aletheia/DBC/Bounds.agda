-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The bounds a DBC meets before it is validated, loaded or formatted: how
-- many items each of its lists holds, how long each of its texts is and
-- which characters it holds, which names it uses, and how large each of its
-- numbers is.  `IsBoundedDBC` states them; `checkBounds` decides them,
-- refusing with the first bound crossed or returning the DBC as a
-- `BoundedDBC`, with the erased proof that it meets every one.
--
-- Order of discovery: every count, then every text, then every name, then
-- every magnitude.  Counts: messages, then per message its signals, senders,
-- and per signal its receivers and multiplex values; attributes and per
-- attribute its enum labels; comments; nodes; value tables; value
-- descriptions in total; signal groups and per group its members;
-- environment variables; unresolved value descriptions.  Texts: version,
-- per signal its unit and value labels, comments, attribute enum labels and
-- string values, value-table labels, unresolved value labels; each is held
-- to its length and then to the DBC character set (printable ASCII but `"`
-- and `\`, or TAB, LF, CR), the first character outside it refused with its
-- index and code point.  Names: every identifier, per message its name,
-- sender, senders and per signal its name, receivers and multiplexor; signal
-- groups and their members; environment variables; value tables; nodes;
-- comment and attribute targets; the signals of unresolved value
-- descriptions; each refused as a DBC keyword or past the identifier
-- length; an attribute name, a quoted string on the wire, is held to the
-- identifier rules as well: ASCII, the grammar, no keyword, the length.
--
-- Each bound is one decision carrying its evidence erased; the refusal is
-- built where the decision is made and names the field.
module Aletheia.DBC.Bounds where

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.NonEmpty using () renaming (length to length⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc; _≤_; _≤ᵇ_; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (≤ᵇ-reflects-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Reflects using (invert)

open import Aletheia.Data.Dec0 using (Dec₀; _because₀_; dec₀)
open import Aletheia.Parser.Position using (Position; advancePosition)
open import Aletheia.DBC.Identifier using
  ( firstFailing )
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.DecRat.Magnitude using (SmallNat; SmallDecRat; largerComponent)
open import Aletheia.DBC.DecRat.Refinement using (IntDecRat; NatDecRat)
open import Data.List.NonEmpty using (toList)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; SignalPresence; Always; When; SignalGroup
  ; ValueTable; RawValueDesc; DBCComment; Node; EnvironmentVar; DBCAttribute
  ; DBCAttrDef; DBCAttrDefault; DBCAttrAssign; AttrDef; AttrDefault
  ; AttrAssign; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex; AttrValue
  ; AVInt; AVFloat; AVString; AVEnum; AVHex )
open import Aletheia.Error using
  ( Error; InputBoundExceededAt; InPart; InvalidCharacter; InField )
open import Aletheia.Limits using
  ( BoundKind; ArrayCardinality; StringLength; RationalComponentMagnitude
  ; max-rational-component-magnitude; max-messages-per-file
  ; max-signals-per-message; max-attributes-per-file; max-comments-per-file
  ; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file; max-signal-groups-per-file
  ; max-environment-variables-per-file
  ; max-unresolved-value-descriptions-per-file; max-enum-labels-per-attribute
  ; max-multiplex-values-per-signal; max-string-length-characters )

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
  decide (InputBoundExceededAt (InPart tag) kind n limit) (within n limit)

count : String → (n limit : ℕ) → Checked (n ≤ limit)
count = bound ArrayCardinality

ShortText : List Char → Set
ShortText cs = length cs ≤ max-string-length-characters

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
-- CHARACTERS
-- ============================================================================

-- A character of a DBC string: printable ASCII but `"` and `\`, or TAB, LF, CR.
stringCharᵇ : Char → Bool
stringCharᵇ c =
  ((32 ≤ᵇ n) ∧ (n ≤ᵇ 126) ∧ not (n ≡ᵇ 34) ∧ not (n ≡ᵇ 92))
    ∨ (n ≡ᵇ 9) ∨ (n ≡ᵇ 10) ∨ (n ≡ᵇ 13)
  where n = toℕ c

-- A character of a DBC text: a string's, or the `"` and `\` its syntax spells.
textCharᵇ : Char → Bool
textCharᵇ c = stringCharᵇ c ∨ (toℕ c ≡ᵇ 34) ∨ (toℕ c ≡ᵇ 92)

CharsOK : (Char → Bool) → List Char → Set
CharsOK p = All (T ∘ p)

-- A walk that finds no failing character has seen every one satisfy `p`.
all-from-firstFailing : ∀ (p : Char → Bool) i cs → firstFailing p i cs ≡ nothing → CharsOK p cs
all-from-firstFailing p i []       _  = []
all-from-firstFailing p i (c ∷ cs) eq = go (p c) refl eq
  where
    go : ∀ b → p c ≡ b
       → (if b then firstFailing p (suc i) cs else just (i , c)) ≡ nothing
       → CharsOK p (c ∷ cs)
    go true  pc eq′ = subst T (sym pc) tt ∷ all-from-firstFailing p (suc i) cs eq′
    go false _  eq′ = contradiction eq′ (λ ())

-- The first character of a DBC text outside the text set, at its position.
scanText : Position → List Char → Maybe (Position × Char)
scanText _   []       = nothing
scanText pos (c ∷ cs) =
  if textCharᵇ c then scanText (advancePosition pos c) cs else just (pos , c)

-- Every character of a field satisfies `p`, or the first that does not is
-- refused with its index and code point.  `charsAt` takes the walk's result
-- as an argument, so a proof reasons about it without abstracting the walk.
charsAt : (p : Char → Bool) → String → (cs : List Char) (r : Maybe (ℕ × Char))
        → firstFailing p 0 cs ≡ r → Checked (CharsOK p cs)
charsAt p tag cs nothing       eq = inj₂ [ all-from-firstFailing p 0 cs eq ]
charsAt p tag cs (just (i , c)) _ = inj₁ (InvalidCharacter (InField tag i) (toℕ c))

chars : (p : Char → Bool) → String → (cs : List Char) → Checked (CharsOK p cs)
chars p tag cs = charsAt p tag cs (firstFailing p 0 cs) refl

-- ============================================================================
-- TEXTS
-- ============================================================================

TextOK : List Char → Set
TextOK cs = ShortText cs × CharsOK stringCharᵇ cs

text : String → (cs : List Char) → Checked (TextOK cs)
text tag cs =
  bound StringLength tag (length cs) max-string-length-characters >>= λ s →
  chars stringCharᵇ tag cs >>= λ a → inj₂ [ (s , a) ]

LabelsOK : List (ℕ × List Char) → Set
LabelsOK = All (TextOK ∘ proj₂)

record SignalTexts (sig : DBCSignal) : Set where
  field
    unit   : TextOK (DBCSignal.unit sig)
    labels : LabelsOK (DBCSignal.valueDescriptions sig)

TypeOK : AttrType → Set
TypeOK (ATEnum vs) = All TextOK vs
TypeOK _           = ⊤

ValueOK : AttrValue → Set
ValueOK (AVString cs) = TextOK cs
ValueOK _             = ⊤

AttributeTexts : DBCAttribute → Set
AttributeTexts (DBCAttrDef d)     = TypeOK (AttrDef.attrType d)
AttributeTexts (DBCAttrDefault d) = ValueOK (AttrDefault.value d)
AttributeTexts (DBCAttrAssign a)  = ValueOK (AttrAssign.value a)

record DBCTexts (dbc : DBC) : Set where
  field
    version              : TextOK (DBC.version dbc)
    signals              : All (All SignalTexts ∘ DBCMessage.signals) (DBC.messages dbc)
    comments             : All (TextOK ∘ DBCComment.text) (DBC.comments dbc)
    attributes           : All AttributeTexts (DBC.attributes dbc)
    valueTables          : All (LabelsOK ∘ ValueTable.entries) (DBC.valueTables dbc)
    unresolvedValueDescs : All (LabelsOK ∘ RawValueDesc.entries) (DBC.unresolvedValueDescs dbc)

labels : String → (vs : List (ℕ × List Char)) → Checked (LabelsOK vs)
labels tag = every (λ e → text tag (proj₂ e))

signalTexts : (sig : DBCSignal) → Checked (SignalTexts sig)
signalTexts sig =
  text "signal text field" (DBCSignal.unit sig) >>= λ u →
  labels "signal text field" (DBCSignal.valueDescriptions sig) >>= λ l →
  inj₂ [ record { unit = u ; labels = l } ]

typeOK : (t : AttrType) → Checked (TypeOK t)
typeOK (ATInt _ _)   = inj₂ [ tt ]
typeOK (ATFloat _ _) = inj₂ [ tt ]
typeOK ATString      = inj₂ [ tt ]
typeOK (ATEnum vs)   = every (text "attribute text field") vs
typeOK (ATHex _ _)   = inj₂ [ tt ]

valueOK : (v : AttrValue) → Checked (ValueOK v)
valueOK (AVInt _)     = inj₂ [ tt ]
valueOK (AVFloat _)   = inj₂ [ tt ]
valueOK (AVString cs) = text "attribute text field" cs
valueOK (AVEnum _)    = inj₂ [ tt ]
valueOK (AVHex _)     = inj₂ [ tt ]

attributeTexts : (a : DBCAttribute) → Checked (AttributeTexts a)
attributeTexts (DBCAttrDef d)     = typeOK (AttrDef.attrType d)
attributeTexts (DBCAttrDefault d) = valueOK (AttrDefault.value d)
attributeTexts (DBCAttrAssign a)  = valueOK (AttrAssign.value a)

dbcTexts : (dbc : DBC) → Checked (DBCTexts dbc)
dbcTexts dbc =
  text "version string" (DBC.version dbc) >>= λ v →
  every (every signalTexts ∘ DBCMessage.signals) (DBC.messages dbc) >>= λ s →
  every (text "comment text" ∘ DBCComment.text) (DBC.comments dbc) >>= λ c →
  every attributeTexts (DBC.attributes dbc) >>= λ a →
  every (labels "value table label" ∘ ValueTable.entries) (DBC.valueTables dbc) >>= λ t →
  every (labels "unresolved value description label" ∘ RawValueDesc.entries)
    (DBC.unresolvedValueDescs dbc) >>= λ u →
  inj₂ [ record
    { version = v ; signals = s ; comments = c ; attributes = a
    ; valueTables = t ; unresolvedValueDescs = u
    } ]

-- ============================================================================
-- MAGNITUDES
-- ============================================================================

-- A number whose larger reduced component passes the bound is refused
-- naming its field; a value the parser held is 2^64 on that component.
magnitude : String → (d : DecRat) → Checked (SmallDecRat d)
magnitude tag d =
  bound RationalComponentMagnitude tag (largerComponent d) max-rational-component-magnitude

natMagnitude : String → (n : ℕ) → Checked (SmallNat n)
natMagnitude tag n = bound RationalComponentMagnitude tag n max-rational-component-magnitude

SmallKeys : List (ℕ × List Char) → Set
SmallKeys = All (SmallNat ∘ proj₁)

smallKeys : String → (vs : List (ℕ × List Char)) → Checked (SmallKeys vs)
smallKeys tag = every (λ e → natMagnitude tag (proj₁ e))

SmallSelectors : SignalPresence → Set
SmallSelectors Always      = ⊤
SmallSelectors (When _ vs) = All SmallNat (toList vs)

smallSelectors : (p : SignalPresence) → Checked (SmallSelectors p)
smallSelectors Always      = inj₂ [ tt ]
smallSelectors (When _ vs) = every (natMagnitude "multiplex value") (toList vs)

record SignalMagnitudes (sig : DBCSignal) : Set where
  field
    factor    : SmallDecRat (SignalDef.factor  (DBCSignal.signalDef sig))
    offset    : SmallDecRat (SignalDef.offset  (DBCSignal.signalDef sig))
    minimum   : SmallDecRat (SignalDef.minimum (DBCSignal.signalDef sig))
    maximum   : SmallDecRat (SignalDef.maximum (DBCSignal.signalDef sig))
    startBit  : SmallNat (SignalDef.startBit  (DBCSignal.signalDef sig))
    bitLength : SmallNat (SignalDef.bitLength (DBCSignal.signalDef sig))
    selectors : SmallSelectors (DBCSignal.presence sig)
    keys      : SmallKeys (DBCSignal.valueDescriptions sig)

signalMagnitudes : (sig : DBCSignal) → Checked (SignalMagnitudes sig)
signalMagnitudes sig =
  magnitude "signal factor"  (SignalDef.factor  def) >>= λ f →
  magnitude "signal offset"  (SignalDef.offset  def) >>= λ o →
  magnitude "signal minimum" (SignalDef.minimum def) >>= λ lo →
  magnitude "signal maximum" (SignalDef.maximum def) >>= λ hi →
  natMagnitude "signal start bit" (SignalDef.startBit def) >>= λ sb →
  natMagnitude "signal length" (SignalDef.bitLength def) >>= λ bl →
  smallSelectors (DBCSignal.presence sig) >>= λ s →
  smallKeys "value description key" (DBCSignal.valueDescriptions sig) >>= λ k →
  inj₂ [ record { factor = f ; offset = o ; minimum = lo ; maximum = hi
                ; startBit = sb ; bitLength = bl ; selectors = s ; keys = k } ]
  where
    def = DBCSignal.signalDef sig

record EnvVarMagnitudes (e : EnvironmentVar) : Set where
  field
    initial : SmallDecRat (EnvironmentVar.initial e)
    minimum : SmallDecRat (EnvironmentVar.minimum e)
    maximum : SmallDecRat (EnvironmentVar.maximum e)

envVarMagnitudes : (e : EnvironmentVar) → Checked (EnvVarMagnitudes e)
envVarMagnitudes e =
  magnitude "environment variable initial value" (EnvironmentVar.initial e) >>= λ i →
  magnitude "environment variable minimum"       (EnvironmentVar.minimum e) >>= λ lo →
  magnitude "environment variable maximum"       (EnvironmentVar.maximum e) >>= λ hi →
  inj₂ [ record { initial = i ; minimum = lo ; maximum = hi } ]

SmallType : AttrType → Set
SmallType (ATInt lo hi)   = SmallDecRat (IntDecRat.value lo) × SmallDecRat (IntDecRat.value hi)
SmallType (ATFloat lo hi) = SmallDecRat lo × SmallDecRat hi
SmallType ATString        = ⊤
SmallType (ATEnum _)      = ⊤
SmallType (ATHex lo hi)   = SmallDecRat (NatDecRat.value lo) × SmallDecRat (NatDecRat.value hi)

smallType : (t : AttrType) → Checked (SmallType t)
smallType (ATInt lo hi)   =
  magnitude "attribute minimum" (IntDecRat.value lo) >>= λ l →
  magnitude "attribute maximum" (IntDecRat.value hi) >>= λ h → inj₂ [ (l , h) ]
smallType (ATFloat lo hi) =
  magnitude "attribute minimum" lo >>= λ l →
  magnitude "attribute maximum" hi >>= λ h → inj₂ [ (l , h) ]
smallType ATString        = inj₂ [ tt ]
smallType (ATEnum _)      = inj₂ [ tt ]
smallType (ATHex lo hi)   =
  magnitude "attribute minimum" (NatDecRat.value lo) >>= λ l →
  magnitude "attribute maximum" (NatDecRat.value hi) >>= λ h → inj₂ [ (l , h) ]

SmallValue : AttrValue → Set
SmallValue (AVInt v)    = SmallDecRat (IntDecRat.value v)
SmallValue (AVFloat d)  = SmallDecRat d
SmallValue (AVString _) = ⊤
SmallValue (AVEnum v)   = SmallDecRat (NatDecRat.value v)
SmallValue (AVHex v)    = SmallDecRat (NatDecRat.value v)

smallValue : (v : AttrValue) → Checked (SmallValue v)
smallValue (AVInt v)    = magnitude "attribute value" (IntDecRat.value v)
smallValue (AVFloat d)  = magnitude "attribute value" d
smallValue (AVString _) = inj₂ [ tt ]
smallValue (AVEnum v)   = magnitude "attribute value" (NatDecRat.value v)
smallValue (AVHex v)    = magnitude "attribute value" (NatDecRat.value v)

AttributeMagnitudes : DBCAttribute → Set
AttributeMagnitudes (DBCAttrDef d)     = SmallType (AttrDef.attrType d)
AttributeMagnitudes (DBCAttrDefault d) = SmallValue (AttrDefault.value d)
AttributeMagnitudes (DBCAttrAssign a)  = SmallValue (AttrAssign.value a)

attributeMagnitudes : (a : DBCAttribute) → Checked (AttributeMagnitudes a)
attributeMagnitudes (DBCAttrDef d)     = smallType (AttrDef.attrType d)
attributeMagnitudes (DBCAttrDefault d) = smallValue (AttrDefault.value d)
attributeMagnitudes (DBCAttrAssign a)  = smallValue (AttrAssign.value a)

record DBCMagnitudes (dbc : DBC) : Set where
  field
    signals              : All (All SignalMagnitudes ∘ DBCMessage.signals) (DBC.messages dbc)
    environmentVars      : All EnvVarMagnitudes (DBC.environmentVars dbc)
    attributes           : All AttributeMagnitudes (DBC.attributes dbc)
    valueTables          : All (SmallKeys ∘ ValueTable.entries) (DBC.valueTables dbc)
    unresolvedValueDescs : All (SmallKeys ∘ RawValueDesc.entries) (DBC.unresolvedValueDescs dbc)

dbcMagnitudes : (dbc : DBC) → Checked (DBCMagnitudes dbc)
dbcMagnitudes dbc =
  every (every signalMagnitudes ∘ DBCMessage.signals) (DBC.messages dbc) >>= λ s →
  every envVarMagnitudes (DBC.environmentVars dbc) >>= λ e →
  every attributeMagnitudes (DBC.attributes dbc) >>= λ a →
  every (smallKeys "value table key" ∘ ValueTable.entries) (DBC.valueTables dbc) >>= λ t →
  every (smallKeys "unresolved value description key" ∘ RawValueDesc.entries)
    (DBC.unresolvedValueDescs dbc) >>= λ u →
  inj₂ [ record { signals = s ; environmentVars = e ; attributes = a
                ; valueTables = t ; unresolvedValueDescs = u } ]

-- ============================================================================
-- THE BOUNDED DBC
-- ============================================================================

record IsBoundedDBC (dbc : DBC) : Set where
  field
    counts     : DBCCounts dbc
    texts      : DBCTexts dbc
    magnitudes : DBCMagnitudes dbc

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
  dbcMagnitudes dbc >>= λ m →
  inj₂ [ record { counts = c ; texts = t ; magnitudes = m } ]

checkBounds : DBC → Error ⊎ BoundedDBC
checkBounds dbc with isBounded? dbc
... | inj₁ e     = inj₁ e
... | inj₂ [ p ] = inj₂ (bounded dbc p)

-- A node list within its count.
NodesOK : List Node → Set
NodesOK ns = length ns ≤ max-nodes-per-file

nodesOK : (ns : List Node) → Checked (NodesOK ns)
nodesOK ns = count "nodes array" (length ns) max-nodes-per-file

-- The same DBC with its node list replaced, still bounded: the new list's
-- count is decided, the rest of the proof carries over.
withNodes : BoundedDBC → List Node → Error ⊎ BoundedDBC
withNodes (bounded d p) ns with nodesOK ns
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
  ; magnitudes = record
      { signals = DBCMagnitudes.signals m ; environmentVars = DBCMagnitudes.environmentVars m
      ; attributes = DBCMagnitudes.attributes m ; valueTables = DBCMagnitudes.valueTables m
      ; unresolvedValueDescs = DBCMagnitudes.unresolvedValueDescs m
      }
  }))
  where
    @0 c : DBCCounts d
    c = IsBoundedDBC.counts p
    @0 t : DBCTexts d
    t = IsBoundedDBC.texts p
    @0 m : DBCMagnitudes d
    m = IsBoundedDBC.magnitudes p
