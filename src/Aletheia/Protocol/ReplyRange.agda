-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The form of every number, string and array a reply writes, by the place
-- it sits.
--
-- A value's place is its path, the keys from the reply's root down to it
-- (an array adds none), and its type, set by the fields of the object
-- holding it written before it: a `kind` or a `type` string, or an
-- `extended` flag, which types a CAN id `standard` or `extended`; `nothing`
-- where none came first.  Three tables, each one row per path and type,
-- give each place's form.  `replyRange` gives a number's range: a natural
-- at most a named limit, a positive natural at most a named limit, an
-- integer of magnitude at most a named limit, a rational whose reduced
-- components are within a named limit, or a CAN payload's byte count; a
-- place it does not list holds no number, and every limit a row names is
-- within the component bound, which every binding's reader holds.
-- `replyText` gives a string's form: one of a set of literals, or any text
-- that is not empty; a place it does not list holds any string.
-- `replyNonEmpty` names the arrays that hold at least one element.  Every
-- definition but the forms and the record of the three tables is erased.
module Aletheia.Protocol.ReplyRange where

open import Data.Bool using (Bool; T; true; false; if_then_else_)
open import Data.Integer using (∣_∣)
open import Data.Char using (Char)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _∷ʳ_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Rational using (ℚ)
open import Data.String using (String; _==_; fromList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.CAN.Constants using (max-standard-can-id; max-extended-can-id)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.Limits using
  ( max-rational-component-magnitude; max-start-bit; max-bit-length
  ; max-multiplex-value; max-value-description-key-magnitude
  ; max-attribute-magnitude; max-var-type; observed-ceiling; bound-ceiling )
open import Aletheia.Prelude using (ℕtoℚ; fromℤ)
open import Aletheia.Protocol.JSON.Types using
  ( JSON; JNull; JBool; JNumber; JString; JArray; JObject; ComponentsWithin
  ; NumbersSatisfy; ListNumbersSatisfy; FieldsNumbersSatisfy )

-- ============================================================================
-- RANGE FORMS
-- ============================================================================

-- A row's range, a limit carrying the proof that it is within the
-- component bound (found by instance search on the literal limit).
data RangeForm : Set where
  naturalAtMost  : (limit : ℕ) → ⦃ T (limit ≤ᵇ max-rational-component-magnitude) ⦄ → RangeForm
  positiveAtMost : (limit : ℕ) → ⦃ T (limit ≤ᵇ max-rational-component-magnitude) ⦄ → RangeForm
  integerAtMost  : (limit : ℕ) → ⦃ T (limit ≤ᵇ max-rational-component-magnitude) ⦄ → RangeForm
  rationalWithin : (limit : ℕ) → ⦃ T (limit ≤ᵇ max-rational-component-magnitude) ⦄ → RangeForm
  byteCount      : RangeForm

-- A number in a row's range; at a place no row lists, none is.
@0 InRange : Maybe RangeForm → ℚ → Set
InRange nothing                       _ = ⊥
InRange (just (naturalAtMost limit))  q = ∃[ n ] (q ≡ ℕtoℚ n × n ≤ limit)
InRange (just (positiveAtMost limit)) q = ∃[ n ] (q ≡ ℕtoℚ n × 1 ≤ n × n ≤ limit)
InRange (just (integerAtMost limit))  q = ∃[ z ] (q ≡ fromℤ z × ∣ z ∣ ≤ limit)
InRange (just (rationalWithin limit)) q = ComponentsWithin limit q
InRange (just byteCount)              q = ∃[ d ] (q ≡ ℕtoℚ (dlcBytes d))

-- ============================================================================
-- THE ROWS
-- ============================================================================

@0 replyRange : List String → Maybe String → Maybe RangeForm
-- A property result and a warning.
replyRange ("results" ∷ "property_index" ∷ [])  (just "property")      = just (naturalAtMost observed-ceiling)
replyRange ("results" ∷ "timestamp" ∷ [])       (just "property")      = just (naturalAtMost observed-ceiling)
replyRange ("warnings" ∷ "property_index" ∷ []) (just "uncached_atom") = just (naturalAtMost observed-ceiling)
-- An extracted value.
replyRange ("values" ∷ "value" ∷ [])            nothing                = just (rationalWithin max-rational-component-magnitude)
-- An error's position, character and bound.
replyRange ("line" ∷ [])             nothing = just (naturalAtMost observed-ceiling)
replyRange ("column" ∷ [])           nothing = just (naturalAtMost observed-ceiling)
replyRange ("statement_line" ∷ [])   nothing = just (naturalAtMost observed-ceiling)
replyRange ("statement_column" ∷ []) nothing = just (naturalAtMost observed-ceiling)
replyRange ("index" ∷ [])            nothing = just (naturalAtMost observed-ceiling)
replyRange ("code_point" ∷ [])       nothing = just (naturalAtMost observed-ceiling)
replyRange ("observed" ∷ [])         nothing = just (positiveAtMost bound-ceiling)
replyRange ("limit" ∷ [])            nothing = just (positiveAtMost bound-ceiling)
-- A DBC's messages and signals.
replyRange ("dbc" ∷ "messages" ∷ "id" ∷ [])  (just "standard") = just (naturalAtMost max-standard-can-id)
replyRange ("dbc" ∷ "messages" ∷ "id" ∷ [])  (just "extended") = just (naturalAtMost max-extended-can-id)
replyRange ("dbc" ∷ "messages" ∷ "dlc" ∷ []) (just "standard") = just byteCount
replyRange ("dbc" ∷ "messages" ∷ "dlc" ∷ []) (just "extended") = just byteCount
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "startBit" ∷ [])  nothing = just (naturalAtMost max-start-bit)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "length" ∷ [])    nothing = just (naturalAtMost max-bit-length)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "factor" ∷ [])    nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "offset" ∷ [])    nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "minimum" ∷ [])   nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "maximum" ∷ [])   nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "multiplex_values" ∷ []) nothing = just (naturalAtMost max-multiplex-value)
replyRange ("dbc" ∷ "messages" ∷ "signals" ∷ "valueDescriptions" ∷ "value" ∷ []) nothing = just (integerAtMost max-value-description-key-magnitude)
-- Environment variables, value tables and unresolved value descriptions.
replyRange ("dbc" ∷ "environmentVars" ∷ "varType" ∷ []) nothing = just (naturalAtMost max-var-type)
replyRange ("dbc" ∷ "environmentVars" ∷ "initial" ∷ []) nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "environmentVars" ∷ "minimum" ∷ []) nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "environmentVars" ∷ "maximum" ∷ []) nothing = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "valueTables" ∷ "entries" ∷ "value" ∷ []) nothing = just (integerAtMost max-value-description-key-magnitude)
replyRange ("dbc" ∷ "unresolvedValueDescs" ∷ "id" ∷ []) (just "standard") = just (naturalAtMost max-standard-can-id)
replyRange ("dbc" ∷ "unresolvedValueDescs" ∷ "id" ∷ []) (just "extended") = just (naturalAtMost max-extended-can-id)
replyRange ("dbc" ∷ "unresolvedValueDescs" ∷ "entries" ∷ "value" ∷ []) nothing = just (integerAtMost max-value-description-key-magnitude)
-- Comment targets.
replyRange ("dbc" ∷ "comments" ∷ "target" ∷ "id" ∷ []) (just "standard") = just (naturalAtMost max-standard-can-id)
replyRange ("dbc" ∷ "comments" ∷ "target" ∷ "id" ∷ []) (just "extended") = just (naturalAtMost max-extended-can-id)
-- Attribute types, values and targets.
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "min" ∷ []) (just "int")   = just (integerAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "max" ∷ []) (just "int")   = just (integerAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "min" ∷ []) (just "hex")   = just (naturalAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "max" ∷ []) (just "hex")   = just (naturalAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "min" ∷ []) (just "float") = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "attrType" ∷ "max" ∷ []) (just "float") = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "value" ∷ "value" ∷ []) (just "int")   = just (integerAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "value" ∷ "value" ∷ []) (just "hex")   = just (naturalAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "value" ∷ "value" ∷ []) (just "enum")  = just (naturalAtMost max-attribute-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "value" ∷ "value" ∷ []) (just "float") = just (rationalWithin max-rational-component-magnitude)
replyRange ("dbc" ∷ "attributes" ∷ "target" ∷ "id" ∷ []) (just "standard") = just (naturalAtMost max-standard-can-id)
replyRange ("dbc" ∷ "attributes" ∷ "target" ∷ "id" ∷ []) (just "extended") = just (naturalAtMost max-extended-can-id)
replyRange _ _ = nothing


-- ============================================================================
-- TEXT FORMS AND NON-EMPTY ARRAYS
-- ============================================================================

-- A string place's form: one of a set of literals, or any text that is not
-- empty.
data TextForm : Set where
  oneOf    : List String → TextForm
  anyNonEmpty : TextForm

-- A string in a row's form; at a place no row lists, any string is.
@0 TextIn : Maybe TextForm → List Char → Set
TextIn nothing           _       = ⊤
TextIn (just (oneOf ls)) cs      = T (any (fromList cs ==_) ls)
TextIn (just anyNonEmpty) []      = ⊥
TextIn (just anyNonEmpty) (_ ∷ _) = ⊤

-- The values a validation issue's severity, an attribute's or a value's
-- kind, an attribute's scope and target take.
@0 severities : List String
severities = "error" ∷ "warning" ∷ []

@0 attributeKinds : List String
attributeKinds = "int" ∷ "float" ∷ "string" ∷ "enum" ∷ "hex" ∷ []

@0 scopes : List String
scopes = "network" ∷ "node" ∷ "message" ∷ "signal" ∷ "envVar" ∷ "nodeMsg" ∷ "nodeSig" ∷ []

@0 replyText : List String → Maybe String → Maybe TextForm
-- A reply's status and type, a property result and a warning.
replyText ("status" ∷ [])               nothing          = just (oneOf ("success" ∷ "error" ∷ "ack" ∷ "complete" ∷ "validation" ∷ []))
replyText ("type" ∷ [])                 nothing          = just (oneOf ("property_batch" ∷ []))
replyText ("results" ∷ "type" ∷ [])     nothing          = just (oneOf ("property" ∷ []))
replyText ("results" ∷ "status" ∷ [])   (just "property") = just (oneOf ("holds" ∷ "fails" ∷ "unresolved" ∷ []))
replyText ("warnings" ∷ "kind" ∷ [])    nothing          = just (oneOf ("uncached_atom" ∷ []))
-- A validation issue, in a validation or an error reply and among a load's
-- warnings.
replyText ("issues" ∷ "severity" ∷ [])   nothing = just (oneOf severities)
replyText ("warnings" ∷ "severity" ∷ []) nothing = just (oneOf severities)
-- A bound refusal's kind.
replyText ("bound_kind" ∷ []) nothing =
  just (oneOf ( "input_length_bytes" ∷ "nesting_depth" ∷ "array_cardinality" ∷ "identifier_length"
              ∷ "string_length" ∷ "atom_count" ∷ "property_count" ∷ "rational_component_magnitude" ∷ []))
-- A DBC's signals, comments and attributes.
replyText ("dbc" ∷ "messages" ∷ "signals" ∷ "byteOrder" ∷ [])   nothing = just (oneOf ("little_endian" ∷ "big_endian" ∷ []))
replyText ("dbc" ∷ "messages" ∷ "signals" ∷ "presence" ∷ [])    nothing = just (oneOf ("always" ∷ "multiplexed" ∷ []))
replyText ("dbc" ∷ "messages" ∷ "signals" ∷ "multiplexor" ∷ []) nothing = just anyNonEmpty
replyText ("dbc" ∷ "comments" ∷ "target" ∷ "kind" ∷ []) nothing =
  just (oneOf ("network" ∷ "node" ∷ "message" ∷ "signal" ∷ "envVar" ∷ []))
replyText ("dbc" ∷ "attributes" ∷ "kind" ∷ []) nothing = just (oneOf ("definition" ∷ "default" ∷ "assignment" ∷ []))
replyText ("dbc" ∷ "attributes" ∷ "scope" ∷ []) (just "definition") = just (oneOf scopes)
replyText ("dbc" ∷ "attributes" ∷ "attrType" ∷ "kind" ∷ []) nothing = just (oneOf attributeKinds)
replyText ("dbc" ∷ "attributes" ∷ "value" ∷ "kind" ∷ [])    nothing = just (oneOf attributeKinds)
replyText ("dbc" ∷ "attributes" ∷ "target" ∷ "kind" ∷ [])   nothing = just (oneOf scopes)
replyText _ _ = nothing

-- The arrays a reply writes with at least one element: a property batch's
-- results and a multiplexed signal's selector values.
@0 replyNonEmpty : List String → Maybe String → Bool
replyNonEmpty ("results" ∷ []) (just "property_batch") = true
replyNonEmpty ("dbc" ∷ "messages" ∷ "signals" ∷ "multiplex_values" ∷ []) nothing = true
replyNonEmpty _ _ = false

-- The three tables a walk reads.
record Places : Set where
  field
    range    : List String → Maybe String → Maybe RangeForm
    text     : List String → Maybe String → Maybe TextForm
    nonEmpty : List String → Maybe String → Bool

@0 replyPlaces : Places
replyPlaces = record { range = replyRange ; text = replyText ; nonEmpty = replyNonEmpty }

-- ============================================================================
-- EVERY VALUE AT ITS PLACE
-- ============================================================================

-- The type an object's later fields see: a field keyed `kind` or `type`
-- holding a string sets it, and one keyed `extended` holding a flag sets it
-- to the width of the CAN id after it.  The key is compared first, so a
-- field whose value is not known leaves the type as it was.
@0 kindOf : Maybe String → JSON → Maybe String
kindOf _ (JString cs) = just (fromList cs)
kindOf t _            = t

@0 widthOf : Maybe String → JSON → Maybe String
widthOf _ (JBool true)  = just "extended"
widthOf _ (JBool false) = just "standard"
widthOf t _             = t

@0 step : Maybe String → String → JSON → Maybe String
step t k v =
  if k == "kind" then kindOf t v
  else if k == "type" then kindOf t v
  else if k == "extended" then widthOf t v
  else t

-- Every value in a JSON value in the form the tables `P` give its place: an
-- object extends the path with each key, its fields starting with no type;
-- an array keeps its path and type, and holds an element where `P` asks.
mutual
  @0 ValuesAt : Places → List String → Maybe String → JSON → Set
  ValuesAt _ _ _ JNull         = ⊤
  ValuesAt _ _ _ (JBool _)     = ⊤
  ValuesAt P p t (JNumber q)   = InRange (Places.range P p t) q
  ValuesAt P p t (JString cs)  = TextIn (Places.text P p t) cs
  ValuesAt P p t (JArray xs)   = ArrayAt P p t (Places.nonEmpty P p t) xs
  ValuesAt P p _ (JObject fs)  = FieldsValuesAt P p nothing fs

  @0 ArrayAt : Places → List String → Maybe String → Bool → List JSON → Set
  ArrayAt P p t false xs       = ListValuesAt P p t xs
  ArrayAt _ _ _ true  []       = ⊥
  ArrayAt P p t true  (x ∷ xs) = ListValuesAt P p t (x ∷ xs)

  @0 ListValuesAt : Places → List String → Maybe String → List JSON → Set
  ListValuesAt _ _ _ []       = ⊤
  ListValuesAt P p t (x ∷ xs) = ValuesAt P p t x × ListValuesAt P p t xs

  @0 FieldsValuesAt : Places → List String → Maybe String → List (String × JSON) → Set
  FieldsValuesAt _ _ _ []             = ⊤
  FieldsValuesAt P p t ((k , v) ∷ fs) = ValuesAt P (p ∷ʳ k) t v × FieldsValuesAt P p (step t k v) fs

-- An array's elements, whether or not its place asks for one.
@0 arrayAt-list : ∀ {P p t} b xs → ArrayAt P p t b xs → ListValuesAt P p t xs
arrayAt-list false _       w = w
arrayAt-list true  (_ ∷ _) w = w

-- A natural, a positive natural, an integer and a byte count in their rows'
-- ranges.
@0 natural-in : ∀ {limit} ⦃ b : T (limit ≤ᵇ max-rational-component-magnitude) ⦄ n → n ≤ limit
  → InRange (just (naturalAtMost limit)) (ℕtoℚ n)
natural-in n n≤ = n , refl , n≤

@0 positive-in : ∀ {limit} ⦃ b : T (limit ≤ᵇ max-rational-component-magnitude) ⦄ n → 1 ≤ n → n ≤ limit
  → InRange (just (positiveAtMost limit)) (ℕtoℚ n)
positive-in n 1≤n n≤ = n , refl , 1≤n , n≤

@0 integer-in : ∀ {limit} ⦃ b : T (limit ≤ᵇ max-rational-component-magnitude) ⦄ z → ∣ z ∣ ≤ limit
  → InRange (just (integerAtMost limit)) (fromℤ z)
integer-in z z≤ = z , refl , z≤

@0 byteCount-in : ∀ d → InRange (just byteCount) (ℕtoℚ (dlcBytes d))
byteCount-in d = d , refl

-- An array of formatted elements, each at its place ...
@0 map-at : ∀ {P p t} {A : Set} {f : A → JSON}
  → (∀ x → ValuesAt P p t (f x)) → ∀ xs → ListValuesAt P p t (map f xs)
map-at h []       = tt
map-at h (x ∷ xs) = h x , map-at h xs

-- ... and the same with a premise per element.
@0 mapAll-at : ∀ {P p t} {A : Set} {f : A → JSON} {Q : A → Set}
  → (∀ x → Q x → ValuesAt P p t (f x)) → ∀ xs → All Q xs → ListValuesAt P p t (map f xs)
mapAll-at h []       []       = tt
mapAll-at h (x ∷ xs) (p ∷ ps) = h x p , mapAll-at h xs ps

-- A claim every row's range implies holds of every number.
mutual
  @0 at-satisfies : ∀ {P} {Q : ℚ → Set} → (∀ p t q → InRange (Places.range P p t) q → Q q)
    → ∀ p t j → ValuesAt P p t j → NumbersSatisfy Q j
  at-satisfies h p t JNull        _ = tt
  at-satisfies h p t (JBool _)    _ = tt
  at-satisfies h p t (JNumber q)  w = h p t q w
  at-satisfies h p t (JString _)  _ = tt
  at-satisfies {P} h p t (JArray xs)  w =
    list-at-satisfies h p t xs (arrayAt-list {P} {p} {t} (Places.nonEmpty P p t) xs w)
  at-satisfies h p t (JObject fs) w = fields-at-satisfies h p nothing fs w

  @0 list-at-satisfies : ∀ {P} {Q : ℚ → Set} → (∀ p t q → InRange (Places.range P p t) q → Q q)
    → ∀ p t xs → ListValuesAt P p t xs → ListNumbersSatisfy Q xs
  list-at-satisfies h p t []       _        = tt
  list-at-satisfies h p t (x ∷ xs) (w , ws) = at-satisfies h p t x w , list-at-satisfies h p t xs ws

  @0 fields-at-satisfies : ∀ {P} {Q : ℚ → Set} → (∀ p t q → InRange (Places.range P p t) q → Q q)
    → ∀ p t fs → FieldsValuesAt P p t fs → FieldsNumbersSatisfy Q fs
  fields-at-satisfies h p t []             _        = tt
  fields-at-satisfies h p t ((k , v) ∷ fs) (w , ws) =
    at-satisfies h (p ∷ʳ k) t v w , fields-at-satisfies h p (step t k v) fs ws
