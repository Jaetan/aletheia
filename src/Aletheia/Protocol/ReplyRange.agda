-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The range of every number a reply writes, by the place it sits.
--
-- A number's place is its path, the keys from the reply's root down to it
-- (an array adds none), and its type, set by the fields of the object
-- holding it written before it: a `kind` string, or an `extended` flag,
-- which types a CAN id `standard` or `extended`; `nothing` where neither
-- came first.  `replyRange` lists every place a reply writes a number, one
-- row per path and type, each with its own range: a natural at most a
-- named limit, a positive natural at most a named limit, an integer of
-- magnitude at most a named limit, a rational whose reduced components are
-- within a named limit, or a CAN payload's byte count.  A place it does not
-- list holds no number.  Every limit a row names is within the component
-- bound, which every binding's reader holds.  Every definition but the
-- range form is erased.
module Aletheia.Protocol.ReplyRange where

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.Integer using (∣_∣)
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
replyRange ("results" ∷ "property_index" ∷ [])  nothing                = just (naturalAtMost observed-ceiling)
replyRange ("results" ∷ "timestamp" ∷ [])       nothing                = just (naturalAtMost observed-ceiling)
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
-- EVERY NUMBER AT ITS PLACE
-- ============================================================================

-- The type an object's later fields see: a field keyed `kind` holding a
-- string sets it, and one keyed `extended` holding a flag sets it to the
-- width of the CAN id after it.  The key is compared first, so a field
-- whose value is not known leaves the type as it was.
@0 kindOf : Maybe String → JSON → Maybe String
kindOf _ (JString cs) = just (fromList cs)
kindOf t _            = t

@0 widthOf : Maybe String → JSON → Maybe String
widthOf _ (JBool true)  = just "extended"
widthOf _ (JBool false) = just "standard"
widthOf t _             = t

@0 step : Maybe String → String → JSON → Maybe String
step t k v = if k == "kind" then kindOf t v else if k == "extended" then widthOf t v else t

-- Every number in a JSON value in the range `R` gives its place: an object
-- extends the path with each key, its fields starting with no type; an
-- array keeps its path and type.
mutual
  @0 NumbersAt : (List String → Maybe String → Maybe RangeForm) → List String → Maybe String → JSON → Set
  NumbersAt _ _ _ JNull         = ⊤
  NumbersAt _ _ _ (JBool _)     = ⊤
  NumbersAt R p t (JNumber q)   = InRange (R p t) q
  NumbersAt _ _ _ (JString _)   = ⊤
  NumbersAt R p t (JArray xs)   = ListNumbersAt R p t xs
  NumbersAt R p _ (JObject fs)  = FieldsNumbersAt R p nothing fs

  @0 ListNumbersAt : (List String → Maybe String → Maybe RangeForm) → List String → Maybe String → List JSON → Set
  ListNumbersAt _ _ _ []       = ⊤
  ListNumbersAt R p t (x ∷ xs) = NumbersAt R p t x × ListNumbersAt R p t xs

  @0 FieldsNumbersAt : (List String → Maybe String → Maybe RangeForm) → List String → Maybe String → List (String × JSON) → Set
  FieldsNumbersAt _ _ _ []             = ⊤
  FieldsNumbersAt R p t ((k , v) ∷ fs) = NumbersAt R (p ∷ʳ k) t v × FieldsNumbersAt R p (step t k v) fs

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
@0 map-at : ∀ {R p t} {A : Set} {f : A → JSON}
  → (∀ x → NumbersAt R p t (f x)) → ∀ xs → ListNumbersAt R p t (map f xs)
map-at h []       = tt
map-at h (x ∷ xs) = h x , map-at h xs

-- ... and the same with a premise per element.
@0 mapAll-at : ∀ {R p t} {A : Set} {f : A → JSON} {P : A → Set}
  → (∀ x → P x → NumbersAt R p t (f x)) → ∀ xs → All P xs → ListNumbersAt R p t (map f xs)
mapAll-at h []       []       = tt
mapAll-at h (x ∷ xs) (p ∷ ps) = h x p , mapAll-at h xs ps

-- A claim every row's range implies holds of every number.
mutual
  @0 at-satisfies : ∀ {R} {P : ℚ → Set} → (∀ p t q → InRange (R p t) q → P q)
    → ∀ p t j → NumbersAt R p t j → NumbersSatisfy P j
  at-satisfies h p t JNull        _ = tt
  at-satisfies h p t (JBool _)    _ = tt
  at-satisfies h p t (JNumber q)  w = h p t q w
  at-satisfies h p t (JString _)  _ = tt
  at-satisfies h p t (JArray xs)  w = list-at-satisfies h p t xs w
  at-satisfies h p t (JObject fs) w = fields-at-satisfies h p nothing fs w

  @0 list-at-satisfies : ∀ {R} {P : ℚ → Set} → (∀ p t q → InRange (R p t) q → P q)
    → ∀ p t xs → ListNumbersAt R p t xs → ListNumbersSatisfy P xs
  list-at-satisfies h p t []       _        = tt
  list-at-satisfies h p t (x ∷ xs) (w , ws) = at-satisfies h p t x w , list-at-satisfies h p t xs ws

  @0 fields-at-satisfies : ∀ {R} {P : ℚ → Set} → (∀ p t q → InRange (R p t) q → P q)
    → ∀ p t fs → FieldsNumbersAt R p t fs → FieldsNumbersSatisfy P fs
  fields-at-satisfies h p t []             _        = tt
  fields-at-satisfies h p t ((k , v) ∷ fs) (w , ws) =
    at-satisfies h (p ∷ʳ k) t v w , fields-at-satisfies h p (step t k v) fs ws
