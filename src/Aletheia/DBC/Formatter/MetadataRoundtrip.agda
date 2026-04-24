{-# OPTIONS --safe --without-K #-}

-- Metadata-level roundtrip proofs for the DBC formatter.
--
-- Purpose: Prove roundtrip for signal groups, environment variables, value
-- tables, nodes, comments, and attributes. These metadata types have no
-- bounds constraints (unlike signals/messages which need WellFormed /
-- PhysicallyValid), so the proofs are unconditional.
-- Role: Middle layer — used by Properties.agda for the top-level roundtrip.
module Aletheia.DBC.Formatter.MetadataRoundtrip where
open import Aletheia.DBC.Types using (nodeNameStr; signalGroupNameStr; envVarNameStr; valueTableNameStr; attrDefNameStr; attrDefaultNameStr; attrAssignNameStr; messageNameStr)
open import Aletheia.DBC.Identifier using (Identifier; mkIdent; validIdentifierᵇ)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)

open import Data.Bool using (T)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Aletheia.DBC.DecRat using (DecRat; toℚ)
open import Aletheia.DBC.DecRat.RationalRoundtrip using (fromℚ?-after-toℚ)

open import Aletheia.DBC.Types using (SignalGroup; EnvironmentVar; ValueTable;
  VarType; IntVar; FloatVar; StringVar; varTypeToℕ;
  Node; mkNode; DBCComment; mkComment;
  CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar;
  AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar; ASNodeMsg; ASNodeSig;
  AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex;
  AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex;
  AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar;
  ATgtNodeMsg; ATgtNodeSig;
  AttrDef; mkAttrDef; AttrDefault; mkAttrDefault; AttrAssign; mkAttrAssign;
  DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign)
open import Aletheia.DBC.Formatter using (ℕtoJSON; ℤtoJSON;
  formatSignalGroup; formatEnvironmentVar; formatValueTable; formatValueEntry;
  formatNode; formatComment; formatCommentTarget;
  formatAttribute; formatAttrScope; formatAttrType;
  formatAttrValue; formatAttrTarget;
  attrDefFields; attrDefaultFields; attrAssignFields)
open import Aletheia.DBC.JSONParser using (parseStringList; parseVarType;
  parseSignalGroup; parseSignalGroupList;
  parseEnvironmentVar; parseEnvironmentVarList;
  parseValueEntry; parseValueEntryList;
  parseValueTable; parseValueTableList;
  parseObjectList;
  parseNode; parseNodeList;
  parseComment; parseCommentTarget; parseCommentList;
  parseAttrScope; parseAttrType; parseAttrValue; parseAttrTarget;
  parseAttrDef; parseAttrDefault; parseAttrAssign;
  parseAttribute; parseAttributeList;
  parseCANId;
  validateIdent; validateIdentList)
open import Aletheia.JSON using (JSON; JObject; JString; JNumber; JArray)
open import Aletheia.DBC.Formatter.WellFormed using (getNat-ℕtoJSON; getInt-ℤtoJSON)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.Prelude using (ifᵀ-witness; _>>=ₑ_)

-- Local bind-cong lemma used throughout. Identical in spirit to
-- MessageRoundtrip.Base.>>=ₑ-congʳ but kept here to avoid a cross-layer
-- dependency from MetadataRoundtrip into MessageRoundtrip/*.
private
  >>=ₑ-congʳ : ∀ {E A B : Set} {x : E ⊎ A} {a : A} (f : A → E ⊎ B)
    → x ≡ inj₂ a → (x >>=ₑ f) ≡ f a
  >>=ₑ-congʳ f refl = refl

-- ============================================================================
-- STRING LIST ROUNDTRIP
-- ============================================================================

parseStringList-roundtrip : ∀ ss → parseStringList (map JString ss) ≡ inj₂ ss
parseStringList-roundtrip [] = refl
parseStringList-roundtrip (s ∷ ss)
  rewrite parseStringList-roundtrip ss = refl

-- Identifier roundtrip: validating the `name` field of a valid Identifier
-- returns the original Identifier.  No axiom — `mkIdentFromString` uses
-- `T?`, so in the `yes w` branch we have a witness and close via
-- `T-irrelevant`; in the `no ¬w` branch, `¬w valid` produces ⊥.
validateIdent-roundtrip : ∀ (i : Identifier) → validateIdent (Identifier.name i) ≡ inj₂ i
validateIdent-roundtrip (mkIdent name valid)
  with T? (validIdentifierᵇ (toList name))
... | yes w  = cong (λ v → inj₂ (mkIdent name v)) (T-irrelevant w valid)
... | no  ¬w = ⊥-elim (¬w valid)

-- `map` post-compose through `Identifier.name` — used in SignalGroup /
-- receivers / senders roundtrips where the formatter emits
-- `map (JString ∘ Identifier.name) xs`.  Exported for SignalRoundtrip /
-- MessageRoundtrip which need the same lemma for their identifier fields.
map-∘-identifier : ∀ {A : Set} (f : String → A) (is : List Identifier)
  → map (λ i → f (Identifier.name i)) is ≡ map f (map Identifier.name is)
map-∘-identifier _ []       = refl
map-∘-identifier f (_ ∷ is) = cong (_ ∷_) (map-∘-identifier f is)

-- List-of-identifiers roundtrip: mapped validateIdentList matches.
validateIdentList-roundtrip :
  ∀ (is : List Identifier) →
    validateIdentList (map Identifier.name is) ≡ inj₂ is
validateIdentList-roundtrip [] = refl
validateIdentList-roundtrip (i ∷ is)
  rewrite validateIdent-roundtrip i
        | validateIdentList-roundtrip is = refl

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
    ("name"    , JString (signalGroupNameStr sg)) ∷
    ("signals" , JArray (map (λ s → JString (Identifier.name s)) (SignalGroup.signals sg))) ∷
    []

signalGroup-roundtrip : ∀ sg
  → parseSignalGroup (signalGroupFields sg) ≡ inj₂ sg
signalGroup-roundtrip sg
  rewrite map-∘-identifier JString (SignalGroup.signals sg)
        | parseStringList-roundtrip (map Identifier.name (SignalGroup.signals sg))
        | validateIdent-roundtrip (SignalGroup.name sg)
        | validateIdentList-roundtrip (SignalGroup.signals sg) = refl

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
    ("name"    , JString (envVarNameStr ev)) ∷
    ("varType" , ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))) ∷
    ("initial" , JNumber (toℚ (EnvironmentVar.initial ev))) ∷
    ("minimum" , JNumber (toℚ (EnvironmentVar.minimum ev))) ∷
    ("maximum" , JNumber (toℚ (EnvironmentVar.maximum ev))) ∷
    []

environmentVar-roundtrip : ∀ ev
  → parseEnvironmentVar (environmentVarFields ev) ≡ inj₂ ev
environmentVar-roundtrip ev
  rewrite getNat-ℕtoJSON (varTypeToℕ (EnvironmentVar.varType ev))
        | parseVarType-roundtrip (EnvironmentVar.varType ev)
        | fromℚ?-after-toℚ (EnvironmentVar.initial ev)
        | fromℚ?-after-toℚ (EnvironmentVar.minimum ev)
        | fromℚ?-after-toℚ (EnvironmentVar.maximum ev)
        | validateIdent-roundtrip (EnvironmentVar.name ev) = refl

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
    ("name"    , JString (valueTableNameStr vt)) ∷
    ("entries" , JArray (map formatValueEntry (ValueTable.entries vt))) ∷
    []

valueTable-roundtrip : ∀ vt
  → parseValueTable (valueTableFields vt) ≡ inj₂ vt
valueTable-roundtrip vt
  rewrite valueEntryList-roundtrip (ValueTable.entries vt)
        | validateIdent-roundtrip (ValueTable.name vt) = refl

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

-- ============================================================================
-- NODE ROUNDTRIP (Tier 2)
-- ============================================================================

-- Node has a single `name : String` field, so the roundtrip reduces by record
-- eta (`mkNode (nodeNameStr n) ≡ n` definitionally).
private
  nodeFields : Node → List (String × JSON)
  nodeFields n = ("name" , JString (nodeNameStr n)) ∷ []

node-roundtrip : ∀ n → parseNode (nodeFields n) ≡ inj₂ n
node-roundtrip (mkNode name)
  rewrite validateIdent-roundtrip name = refl

-- `rewrite` on `node-roundtrip x` with an abstract `x : Node` fails under
-- `--without-K`: Node has an explicit `constructor mkNode` declaration, so
-- the rewrite machinery's internal `refl` match on `inj₂ x ≡ inj₂ x`
-- decomposes to `x = x` and hits K-elimination on the record. Records
-- *without* explicit constructors (SignalGroup, ValueTable, EnvironmentVar
-- above) avoid this via eta alone. Fix: pattern-match on `mkNode _` so
-- `formatNode`/`parseNode` reduce directly — only the list-tail rewrite
-- remains, on `List Node`, which is a datatype and unifies cleanly.
private
  node-list-go : ∀ n ns
    → parseObjectList "node" parseNode n (map formatNode ns) ≡ inj₂ ns
  node-list-go _ [] = refl
  node-list-go n (mkNode name ∷ xs)
    rewrite validateIdent-roundtrip name
          | node-list-go (suc n) xs = refl

node-list-roundtrip : ∀ ns
  → parseNodeList (map formatNode ns) ≡ inj₂ ns
node-list-roundtrip = node-list-go 0

-- ============================================================================
-- COMMENT TARGET ROUNDTRIP (Tier 2)
-- ============================================================================

-- CommentTarget is a 5-way tagged union keyed on "kind". For the two variants
-- carrying a CANId (CTMessage, CTSignal), the roundtrip splits further on
-- Standard/Extended — 7 branches total. Literal string equality reduces
-- definitionally, so the chained `if_then_else_` collapses to the right case
-- automatically; the only non-trivial steps are the ℕ-bridge (for id) and the
-- CANId-ifᵀ-witness (for the bounded proof).

commentTarget-roundtrip : ∀ tgt
  → parseCommentTarget (formatCommentTarget tgt) ≡ inj₂ tgt
commentTarget-roundtrip CTNetwork  = refl
commentTarget-roundtrip (CTNode n)
  rewrite validateIdent-roundtrip n = refl
commentTarget-roundtrip (CTMessage (Standard rawId pf))
  rewrite getNat-ℕtoJSON rawId
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
commentTarget-roundtrip (CTMessage (Extended rawId pf))
  rewrite getNat-ℕtoJSON rawId
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
commentTarget-roundtrip (CTSignal (Standard rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
commentTarget-roundtrip (CTSignal (Extended rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
commentTarget-roundtrip (CTEnvVar ev)
  rewrite validateIdent-roundtrip ev = refl

-- ============================================================================
-- COMMENT ROUNDTRIP (Tier 2)
-- ============================================================================

private
  commentFields : DBCComment → List (String × JSON)
  commentFields c =
    ("target" , JObject (formatCommentTarget (DBCComment.target c))) ∷
    ("text"   , JString (DBCComment.text c)) ∷
    []

comment-roundtrip : ∀ c → parseComment (commentFields c) ≡ inj₂ c
comment-roundtrip c
  rewrite commentTarget-roundtrip (DBCComment.target c) = refl

-- Same K-avoidance strategy as node-list-go: pattern-match on `mkComment`
-- to force field-level reduction, leaving a single datatype-level rewrite.
private
  comment-list-go : ∀ n cs
    → parseObjectList "comment" parseComment n (map formatComment cs) ≡ inj₂ cs
  comment-list-go _ [] = refl
  comment-list-go n (mkComment tgt _ ∷ cs)
    rewrite commentTarget-roundtrip tgt
          | comment-list-go (suc n) cs = refl

comment-list-roundtrip : ∀ cs
  → parseCommentList (map formatComment cs) ≡ inj₂ cs
comment-list-roundtrip = comment-list-go 0

-- ============================================================================
-- ATTRIBUTE ROUNDTRIPS (Tier 2)
-- ============================================================================

-- AttrScope: 7 string-keyed variants, each a trivial `refl`.
attrScope-roundtrip : ∀ s → parseAttrScope (formatAttrScope s) ≡ inj₂ s
attrScope-roundtrip ASNetwork = refl
attrScope-roundtrip ASNode    = refl
attrScope-roundtrip ASMessage = refl
attrScope-roundtrip ASSignal  = refl
attrScope-roundtrip ASEnvVar  = refl
attrScope-roundtrip ASNodeMsg = refl
attrScope-roundtrip ASNodeSig = refl

-- AttrType: 5 tagged variants. Int uses ℤ bridge, Enum uses parseStringList,
-- Hex uses ℕ bridge, Float/String are direct `refl` (getRational/getString
-- on JNumber/JString reduce definitionally).
attrType-roundtrip : ∀ t → parseAttrType (formatAttrType t) ≡ inj₂ t
attrType-roundtrip (ATInt mn mx)
  rewrite getInt-ℤtoJSON mn | getInt-ℤtoJSON mx = refl
attrType-roundtrip (ATFloat mn mx)
  rewrite fromℚ?-after-toℚ mn | fromℚ?-after-toℚ mx = refl
attrType-roundtrip ATString      = refl
attrType-roundtrip (ATEnum labels)
  rewrite parseStringList-roundtrip labels = refl
attrType-roundtrip (ATHex mn mx)
  rewrite getNat-ℕtoJSON mn | getNat-ℕtoJSON mx = refl

-- AttrValue: 5 tagged variants, same bridge story as AttrType.
attrValue-roundtrip : ∀ v → parseAttrValue (formatAttrValue v) ≡ inj₂ v
attrValue-roundtrip (AVInt v)    rewrite getInt-ℤtoJSON v = refl
attrValue-roundtrip (AVFloat v)  rewrite fromℚ?-after-toℚ v = refl
attrValue-roundtrip (AVString _) = refl
attrValue-roundtrip (AVEnum v)   rewrite getNat-ℕtoJSON v = refl
attrValue-roundtrip (AVHex v)    rewrite getNat-ℕtoJSON v = refl

-- AttrTarget: 10 branches (7 kinds × 2 CANId flavours where applicable).
-- Mirrors commentTarget-roundtrip with two extra relation variants.
attrTarget-roundtrip : ∀ t → parseAttrTarget (formatAttrTarget t) ≡ inj₂ t
attrTarget-roundtrip ATgtNetwork    = refl
attrTarget-roundtrip (ATgtNode n)
  rewrite validateIdent-roundtrip n = refl
attrTarget-roundtrip (ATgtMessage (Standard rawId pf))
  rewrite getNat-ℕtoJSON rawId
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtMessage (Extended rawId pf))
  rewrite getNat-ℕtoJSON rawId
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtSignal (Standard rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtSignal (Extended rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtEnvVar ev)
  rewrite validateIdent-roundtrip ev = refl
attrTarget-roundtrip (ATgtNodeMsg n (Standard rawId pf))
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip n
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtNodeMsg n (Extended rawId pf))
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip n
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtNodeSig n (Standard rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip n
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)
attrTarget-roundtrip (ATgtNodeSig n (Extended rawId pf) s)
  rewrite getNat-ℕtoJSON rawId
        | validateIdent-roundtrip n
        | validateIdent-roundtrip s
  = >>=ₑ-congʳ _ (ifᵀ-witness _ _ pf)

-- AttrDef/Default/Assign: straightforward field-by-field composition.
-- Record eta closes the `mk*` equality at the end.
attrDef-roundtrip : ∀ d → parseAttrDef (attrDefFields d) ≡ inj₂ d
attrDef-roundtrip d
  rewrite attrScope-roundtrip (AttrDef.scope d)
        | attrType-roundtrip (AttrDef.attrType d) = refl

attrDefault-roundtrip : ∀ d → parseAttrDefault (attrDefaultFields d) ≡ inj₂ d
attrDefault-roundtrip d
  rewrite attrValue-roundtrip (AttrDefault.value d) = refl

attrAssign-roundtrip : ∀ a → parseAttrAssign (attrAssignFields a) ≡ inj₂ a
attrAssign-roundtrip a
  rewrite attrTarget-roundtrip (AttrAssign.target a)
        | attrValue-roundtrip (AttrAssign.value a) = refl

-- DBCAttribute: 3-way tagged union keyed on "kind". parseAttribute dispatches
-- then forwards the full object (including the leading "kind" entry) to the
-- sub-parser; the sub-parsers all look up named fields other than "kind",
-- so `lookupByKey` skips the leading entry definitionally via literal-string
-- inequality, reducing `parseAttrX (("kind", …) ∷ attrXFields x)` to
-- `parseAttrX (attrXFields x)`.
private
  attributeFields : DBCAttribute → List (String × JSON)
  attributeFields (DBCAttrDef d)     = ("kind" , JString "definition") ∷ attrDefFields d
  attributeFields (DBCAttrDefault d) = ("kind" , JString "default")    ∷ attrDefaultFields d
  attributeFields (DBCAttrAssign a)  = ("kind" , JString "assignment") ∷ attrAssignFields a

attribute-roundtrip : ∀ a → parseAttribute (attributeFields a) ≡ inj₂ a
attribute-roundtrip (DBCAttrDef d)     = >>=ₑ-congʳ _ (attrDef-roundtrip d)
attribute-roundtrip (DBCAttrDefault d) = >>=ₑ-congʳ _ (attrDefault-roundtrip d)
attribute-roundtrip (DBCAttrAssign a)  = >>=ₑ-congʳ _ (attrAssign-roundtrip a)

-- DBCAttribute: two subtleties here relative to node/comment.
-- (1) `rewrite` fails because each payload is a record with an explicit
--     constructor — same K-elimination issue as `node-list-go`.
-- (2) `formatAttribute` pattern-matches on the DBCAttribute constructor, so
--     the `JObject _ ∷ _` pattern inside `parseObjectList` does not fire for
--     an abstract `a`. We split on the sum's constructor to drive reduction.
private
  attribute-list-go : ∀ n as
    → parseObjectList "attribute" parseAttribute n (map formatAttribute as) ≡ inj₂ as
  attribute-list-go _ [] = refl
  attribute-list-go n (DBCAttrDef d ∷ as) =
    trans (>>=ₑ-congʳ _ (attribute-roundtrip (DBCAttrDef d)))
          (>>=ₑ-congʳ _ (attribute-list-go (suc n) as))
  attribute-list-go n (DBCAttrDefault d ∷ as) =
    trans (>>=ₑ-congʳ _ (attribute-roundtrip (DBCAttrDefault d)))
          (>>=ₑ-congʳ _ (attribute-list-go (suc n) as))
  attribute-list-go n (DBCAttrAssign a ∷ as) =
    trans (>>=ₑ-congʳ _ (attribute-roundtrip (DBCAttrAssign a)))
          (>>=ₑ-congʳ _ (attribute-list-go (suc n) as))

attribute-list-roundtrip : ∀ as
  → parseAttributeList (map formatAttribute as) ≡ inj₂ as
attribute-list-roundtrip = attribute-list-go 0
