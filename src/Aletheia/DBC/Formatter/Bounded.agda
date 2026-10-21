-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What `formatDBC` writes for a bounded DBC stays within the bounds the DBC
-- met: an array it writes for a list has that list's length, and every
-- number it writes has both reduced components within
-- `max-rational-component-magnitude` (`formatDBC-within`).  Every
-- definition is erased, so a runtime module can carry the proof beside the
-- JSON it formats and MAlonzo compiles none of it.
--
-- The length lemmas reduce to `length-map`, since every array the formatter
-- writes is `JArray (map format-… field)`.  The number proof walks the
-- formatter one helper at a time.  A `DecRat` field, a signal's start bit,
-- length, multiplex values and value keys, a value table's and an unresolved
-- description's keys, and an attribute's components are within the bound
-- by `IsBoundedDBC` (its `DBCMagnitudes`).  The other numbers the formatter
-- writes are small by construction: a CAN id is below 2^29 (its
-- constructor's witness), a DLC's byte count is at most 64, a Motorola
-- start bit is below 8 times the frame's bytes, and a variable type is at
-- most 2.
module Aletheia.DBC.Formatter.Bounded where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using ()
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _^_; _≤_; _<ᵇ_; _/_; _%_; z≤n)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using
  ( ≤-refl; ≤-trans; ≤-pred; <⇒≤; <ᵇ⇒<; m≤m+n; 1+n≰n; m∸n≤m; ∸-monoˡ-≤
  ; *-monoˡ-≤; +-mono-≤; suc-pred; ≤ᵇ⇒≤ )
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Nullary.Decidable using (recompute)

open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.CAN.DLC using (mkDLC; dlcToBytes; dlcBytes)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; physicalBitPos; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Bounds using
  ( IsBoundedDBC; DBCMagnitudes; SignalMagnitudes; EnvVarMagnitudes; AttributeMagnitudes
  ; SmallKeys; SmallSelectors; SmallType; SmallValue )
open import Aletheia.DBC.DecRat using (mkDecRat; toℚ; 2^a·5^b-NonZero)
open import Aletheia.DBC.DecRat.Refinement using (intDecRatToℤ)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.DecRat.Magnitude using
  ( SmallNat; SmallInt; SmallDecRat; smallDecRat-components; smallNat-by-eval
  ; intDecRat-small; natDecRat-small )
open import Aletheia.DBC.Formatter using
  ( ℕtoJSON; ℤtoJSON; formatCANId; formatPresence; formatValueEntry
  ; formatDBCSignal; formatDBCMessage; formatSignalGroup; formatEnvironmentVar
  ; formatValueTable; formatRawValueDesc; formatNode; formatCommentTarget
  ; formatComment; formatAttrType; formatAttrValue; formatAttrTarget
  ; formatAttribute; formatDBC )
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; SignalPresence; Always; When
  ; EnvironmentVar; ValueTable; RawValueDesc; DBCComment
  ; VarType; IntVar; FloatVar; StringVar; varTypeToℕ
  ; CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign )
open import Aletheia.Limits using (max-rational-component-magnitude)
open import Aletheia.Protocol.JSON.Types using
  (JSON; JNumber; JString; NumbersWithin; ListNumbersWithin; FieldsNumbersWithin; Shallow; FieldsShallow)
open import Aletheia.Protocol.JSON.Shallow using (shallow-≤; map-shallow; fields-++)
open import Aletheia.DBC.Formatter using (identJSON)

-- ============================================================================
-- ARRAY LENGTHS
-- ============================================================================

private
  -- `length-map` as a bound: a list within `n` maps to a list within `n`.
  @0 bound-via-length-map : {A B : Set} (f : A → B) (xs : List A) (n : ℕ)
    → length xs ≤ n → length (map f xs) ≤ n
  bound-via-length-map f xs n bound =
    subst (_≤ n) (sym (length-map f xs)) bound

-- The "messages" array `formatDBC` writes has the length of `DBC.messages`,
-- so it is within `max-messages-per-file` when the DBC is.
@0 formatDBC-messages-bounded : ∀ (d : DBC) (n : ℕ)
  → length (DBC.messages d) ≤ n
  → length (map formatDBCMessage (DBC.messages d)) ≤ n
formatDBC-messages-bounded d n =
  bound-via-length-map formatDBCMessage (DBC.messages d) n

-- The "attributes" array has the length of `DBC.attributes`, so it is
-- within `max-attributes-per-file` when the DBC is.
@0 formatDBC-attributes-bounded : ∀ (d : DBC) (n : ℕ)
  → length (DBC.attributes d) ≤ n
  → length (map formatAttribute (DBC.attributes d)) ≤ n
formatDBC-attributes-bounded d n =
  bound-via-length-map formatAttribute (DBC.attributes d) n

-- A message's "signals" array has the length of `DBCMessage.signals`, so it
-- is within `max-signals-per-message` when the message is.  The formatter
-- maps `formatDBCSignal` applied to the DLC's byte count over the signals.
@0 formatDBCMessage-signals-bounded : ∀ (frameBytes : ℕ) (msg : DBCMessage) (n : ℕ)
  → length (DBCMessage.signals msg) ≤ n
  → length (map (formatDBCSignal frameBytes) (DBCMessage.signals msg)) ≤ n
formatDBCMessage-signals-bounded frameBytes msg n =
  bound-via-length-map (formatDBCSignal frameBytes) (DBCMessage.signals msg) n

-- ============================================================================
-- NUMBERS
-- ============================================================================

-- The claim at the kernel's component bound, for a value, an array's
-- elements and an object's fields.
@0 Within : JSON → Set
Within = NumbersWithin max-rational-component-magnitude

@0 ListWithin : List JSON → Set
ListWithin = ListNumbersWithin max-rational-component-magnitude

@0 FieldsWithin : List (String × JSON) → Set
FieldsWithin = FieldsNumbersWithin max-rational-component-magnitude

-- ---- Lists and field lists ----

-- A list whose every element the formatter writes within the bound.
@0 map-within : ∀ {A : Set} {f : A → JSON}
  → (∀ x → Within (f x)) → ∀ xs → ListWithin (map f xs)
map-within h []       = tt
map-within h (x ∷ xs) = h x , map-within h xs

-- The same, with a premise per element.
@0 mapAll-within : ∀ {A : Set} {f : A → JSON} {P : A → Set}
  → (∀ x → P x → Within (f x)) → ∀ xs → All P xs → ListWithin (map f xs)
mapAll-within h []       []       = tt
mapAll-within h (x ∷ xs) (p ∷ ps) = h x p , mapAll-within h xs ps

@0 ++-within : ∀ xs {ys} → FieldsWithin xs → FieldsWithin ys → FieldsWithin (xs ++ₗ ys)
++-within []       _        q = q
++-within (_ ∷ xs) (p , ps) q = p , ++-within xs ps q

-- ---- One number ----

-- A natural within the bound: numerator `n`, denominator 1.
@0 ℕtoJSON-within : ∀ n → SmallNat n → Within (ℕtoJSON n)
ℕtoJSON-within _ small = small , smallNat-by-eval 1 tt

-- An integer within the bound: numerator `z`, denominator 1.
@0 ℤtoJSON-within : ∀ z → SmallInt z → Within (ℤtoJSON z)
ℤtoJSON-within _ small = small , smallNat-by-eval 1 tt

-- A small `DecRat`: `toℚ` keeps its numerator and its denominator 2^a·5^b,
-- the two components `SmallDecRat` bounds.
@0 toℚ-within : ∀ d → SmallDecRat d → Within (JNumber (toℚ d))
toℚ-within (mkDecRat num a b c) small =
  let parts = smallDecRat-components (mkDecRat num a b c) small
  in proj₁ parts
   , subst (_≤ max-rational-component-magnitude)
           (sym (suc-pred (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄))
           (proj₂ parts)

-- ---- Numbers small by construction ----

-- A CAN id is below its constructor's maximum, 2^11 or 2^29; the witness is
-- irrelevant, so it is recomputed from the decidable test.
@0 canId-within : ∀ cid → FieldsWithin (formatCANId cid)
canId-within (Standard n p) =
  ℕtoJSON-within n
    (≤-trans (<⇒≤ (<ᵇ⇒< n standard-can-id-max (recompute (T? (n <ᵇ standard-can-id-max)) p)))
             (smallNat-by-eval standard-can-id-max tt))
  , tt
canId-within (Extended n p) =
  ℕtoJSON-within n
    (≤-trans (<⇒≤ (<ᵇ⇒< n extended-can-id-max (recompute (T? (n <ᵇ extended-can-id-max)) p)))
             (smallNat-by-eval extended-can-id-max tt))
  , tt , tt

-- A DLC code below 16 maps to at most 64 bytes.
@0 dlcToBytes-≤64 : ∀ c → c ≤ 15 → dlcToBytes c ≤ 64
dlcToBytes-≤64  0 _ = z≤n
dlcToBytes-≤64  1 _ = m≤m+n 1 63
dlcToBytes-≤64  2 _ = m≤m+n 2 62
dlcToBytes-≤64  3 _ = m≤m+n 3 61
dlcToBytes-≤64  4 _ = m≤m+n 4 60
dlcToBytes-≤64  5 _ = m≤m+n 5 59
dlcToBytes-≤64  6 _ = m≤m+n 6 58
dlcToBytes-≤64  7 _ = m≤m+n 7 57
dlcToBytes-≤64  8 _ = m≤m+n 8 56
dlcToBytes-≤64  9 _ = m≤m+n 12 52
dlcToBytes-≤64 10 _ = m≤m+n 16 48
dlcToBytes-≤64 11 _ = m≤m+n 20 44
dlcToBytes-≤64 12 _ = m≤m+n 24 40
dlcToBytes-≤64 13 _ = m≤m+n 32 32
dlcToBytes-≤64 14 _ = m≤m+n 48 16
dlcToBytes-≤64 15 _ = ≤-refl
dlcToBytes-≤64 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))))))))) c≤15 =
  ⊥-elim (1+n≰n (≤-trans c≤15 (m≤m+n 15 k)))

-- A validated DLC's byte count, through its erased bound.
@0 dlcBytes-≤64 : ∀ d → dlcBytes d ≤ 64
dlcBytes-≤64 (mkDLC code bounded) = dlcToBytes-≤64 code (≤-pred (<ᵇ⇒< code 16 bounded))

-- A Motorola bit position in a frame of at most 64 bytes is below 512.
@0 physicalBitPos-≤ : ∀ fb b → fb ≤ 64 → physicalBitPos fb BigEndian b ≤ 511
physicalBitPos-≤ fb b fb≤64 =
  let bytes : ((fb ∸ 1) ∸ (b / 8)) * 8 ≤ 504
      bytes = *-monoˡ-≤ 8 (≤-trans (m∸n≤m (fb ∸ 1) (b / 8)) (∸-monoˡ-≤ 1 fb≤64))
      bit : b % 8 ≤ 7
      bit = ≤-pred (m%n<n b 8)
  in +-mono-≤ bytes bit

-- The start bit the formatter writes: the stored one for little endian, a
-- position in the frame for big endian.
@0 unconvertStartBit-small : ∀ fb bo s l → fb ≤ 64 → SmallNat s
  → SmallNat (unconvertStartBit fb bo s l)
unconvertStartBit-small _  LittleEndian s _ _     small = small
unconvertStartBit-small fb BigEndian    s l fb≤64 _     =
  ≤-trans (physicalBitPos-≤ fb (s + l ∸ 1) fb≤64) (smallNat-by-eval 511 tt)

@0 varType-small : ∀ t → SmallNat (varTypeToℕ t)
varType-small IntVar    = z≤n
varType-small FloatVar  = smallNat-by-eval 1 tt
varType-small StringVar = smallNat-by-eval 2 tt

-- ---- The formatter's helpers ----

@0 presence-within : ∀ p → SmallSelectors p → FieldsWithin (formatPresence p)
presence-within Always      _   = tt , tt
presence-within (When _ vs) sel = tt , tt , mapAll-within ℕtoJSON-within (List⁺.toList vs) sel , tt

@0 entry-within : ∀ e → SmallNat (proj₁ e) → Within (formatValueEntry e)
entry-within (n , _) small = ℕtoJSON-within n small , tt , tt

@0 entries-within : ∀ es → SmallKeys es → ListWithin (map formatValueEntry es)
entries-within = mapAll-within entry-within

@0 signal-within : ∀ fb → fb ≤ 64 → ∀ sig → SignalMagnitudes sig
  → Within (formatDBCSignal fb sig)
signal-within fb fb≤64 sig m =
  let def = DBCSignal.signalDef sig in
  tt
  , ℕtoJSON-within _ (unconvertStartBit-small fb (DBCSignal.byteOrder sig) _ _ fb≤64
                        (SignalMagnitudes.startBit m))
  , ℕtoJSON-within _ (SignalMagnitudes.bitLength m)
  , tt
  , tt
  , toℚ-within (SignalDef.factor def) (SignalMagnitudes.factor m)
  , toℚ-within (SignalDef.offset def) (SignalMagnitudes.offset m)
  , toℚ-within (SignalDef.minimum def) (SignalMagnitudes.minimum m)
  , toℚ-within (SignalDef.maximum def) (SignalMagnitudes.maximum m)
  , tt
  , map-within (λ _ → tt) _
  , entries-within _ (SignalMagnitudes.keys m)
  , presence-within _ (SignalMagnitudes.selectors m)

@0 message-within : ∀ msg → All SignalMagnitudes (DBCMessage.signals msg)
  → Within (formatDBCMessage msg)
message-within msg ms =
  ++-within _ (canId-within (DBCMessage.id msg))
    ( tt
    , ℕtoJSON-within _ (≤-trans (dlcBytes-≤64 (DBCMessage.dlc msg)) (smallNat-by-eval 64 tt))
    , tt
    , map-within (λ _ → tt) _
    , mapAll-within (signal-within _ (dlcBytes-≤64 (DBCMessage.dlc msg))) _ ms
    , tt )

@0 signalGroup-within : ∀ sg → Within (formatSignalGroup sg)
signalGroup-within _ = tt , map-within (λ _ → tt) _ , tt

@0 envVar-within : ∀ ev → EnvVarMagnitudes ev → Within (formatEnvironmentVar ev)
envVar-within ev m =
  tt
  , ℕtoJSON-within _ (varType-small (EnvironmentVar.varType ev))
  , toℚ-within (EnvironmentVar.initial ev) (EnvVarMagnitudes.initial m)
  , toℚ-within (EnvironmentVar.minimum ev) (EnvVarMagnitudes.minimum m)
  , toℚ-within (EnvironmentVar.maximum ev) (EnvVarMagnitudes.maximum m)
  , tt

@0 valueTable-within : ∀ vt → SmallKeys (ValueTable.entries vt) → Within (formatValueTable vt)
valueTable-within _ ks = tt , entries-within _ ks , tt

@0 rawValueDesc-within : ∀ rvd → SmallKeys (RawValueDesc.entries rvd)
  → Within (formatRawValueDesc rvd)
rawValueDesc-within rvd ks =
  ++-within _ (canId-within (RawValueDesc.canId rvd)) (tt , entries-within _ ks , tt)

@0 node-within : ∀ n → Within (formatNode n)
node-within _ = tt , tt

@0 commentTarget-within : ∀ t → FieldsWithin (formatCommentTarget t)
commentTarget-within CTNetwork       = tt , tt
commentTarget-within (CTNode _)      = tt , tt , tt
commentTarget-within (CTMessage id)  = tt , canId-within id
commentTarget-within (CTSignal id _) = tt , ++-within _ (canId-within id) (tt , tt)
commentTarget-within (CTEnvVar _)    = tt , tt , tt

@0 comment-within : ∀ c → Within (formatComment c)
comment-within c = commentTarget-within (DBCComment.target c) , tt , tt

@0 attrType-within : ∀ t → SmallType t → FieldsWithin (formatAttrType t)
attrType-within (ATInt mn mx) (l , h) =
  tt , ℤtoJSON-within (intDecRatToℤ mn) (intDecRat-small mn l) , ℤtoJSON-within (intDecRatToℤ mx) (intDecRat-small mx h) , tt
attrType-within (ATFloat mn mx) (l , h) = tt , toℚ-within mn l , toℚ-within mx h , tt
attrType-within ATString _ = tt , tt
attrType-within (ATEnum labels) _ = tt , map-within (λ _ → tt) labels , tt
attrType-within (ATHex mn mx) (l , h) =
  tt , ℕtoJSON-within _ (natDecRat-small mn l) , ℕtoJSON-within _ (natDecRat-small mx h) , tt

@0 attrValue-within : ∀ v → SmallValue v → FieldsWithin (formatAttrValue v)
attrValue-within (AVInt v)    s = tt , ℤtoJSON-within (intDecRatToℤ v) (intDecRat-small v s) , tt
attrValue-within (AVFloat v)  s = tt , toℚ-within v s , tt
attrValue-within (AVString _) _ = tt , tt , tt
attrValue-within (AVEnum v)   s = tt , ℕtoJSON-within _ (natDecRat-small v s) , tt
attrValue-within (AVHex v)    s = tt , ℕtoJSON-within _ (natDecRat-small v s) , tt

@0 attrTarget-within : ∀ t → FieldsWithin (formatAttrTarget t)
attrTarget-within ATgtNetwork          = tt , tt
attrTarget-within (ATgtNode _)         = tt , tt , tt
attrTarget-within (ATgtMessage id)     = tt , canId-within id
attrTarget-within (ATgtSignal id _)    = tt , ++-within _ (canId-within id) (tt , tt)
attrTarget-within (ATgtEnvVar _)       = tt , tt , tt
attrTarget-within (ATgtNodeMsg _ id)   = tt , tt , canId-within id
attrTarget-within (ATgtNodeSig _ id _) = tt , tt , ++-within _ (canId-within id) (tt , tt)

@0 attribute-within : ∀ a → AttributeMagnitudes a → Within (formatAttribute a)
attribute-within (DBCAttrDef d)     m = tt , tt , tt , attrType-within _ m , tt
attribute-within (DBCAttrDefault d) m = tt , tt , attrValue-within _ m , tt
attribute-within (DBCAttrAssign a)  m = tt , tt , attrTarget-within _ , attrValue-within _ m , tt

-- ---- The theorem ----

-- Every number `formatDBC` writes for a bounded DBC has both reduced
-- components within `max-rational-component-magnitude`.
@0 formatDBC-within : ∀ dbc → IsBoundedDBC dbc → Within (formatDBC dbc)
formatDBC-within dbc b =
  let m = IsBoundedDBC.magnitudes b
  in tt
   , mapAll-within message-within _ (DBCMagnitudes.signals m)
   , map-within signalGroup-within _
   , mapAll-within envVar-within _ (DBCMagnitudes.environmentVars m)
   , mapAll-within valueTable-within _ (DBCMagnitudes.valueTables m)
   , map-within node-within _
   , map-within comment-within _
   , mapAll-within attribute-within _ (DBCMagnitudes.attributes m)
   , mapAll-within rawValueDesc-within _ (DBCMagnitudes.unresolvedValueDescs m)
   , tt

-- ============================================================================
-- DEPTH
-- ============================================================================

-- `formatDBC` nests at most 7 deep: the DBC, its messages, a message, its
-- signals, a signal, its value descriptions, an entry.

@0 canId-shallow : ∀ k id → FieldsShallow k (formatCANId id)
canId-shallow k (Standard _ _) = tt , tt
canId-shallow k (Extended _ _) = tt , tt , tt

@0 valueEntry-shallow : ∀ e → Shallow 1 (formatValueEntry e)
valueEntry-shallow (n , s) = tt , tt , tt

@0 presence-shallow : ∀ k p → FieldsShallow (suc k) (formatPresence p)
presence-shallow k Always        = tt , tt
presence-shallow k (When mux vs) = tt , tt , map-shallow ℕtoJSON (λ _ → tt) (List⁺.toList vs) , tt

@0 signal-shallow : ∀ frameBytes sig → Shallow 3 (formatDBCSignal frameBytes sig)
signal-shallow frameBytes sig =
  tt , tt , tt , tt , tt , tt , tt , tt , tt , tt ,
  map-shallow identJSON (λ _ → tt) _ , map-shallow formatValueEntry valueEntry-shallow _ ,
  presence-shallow 1 (DBCSignal.presence sig)

@0 message-shallow : ∀ msg → Shallow 5 (formatDBCMessage msg)
message-shallow msg =
  fields-++ (formatCANId (DBCMessage.id msg)) _ (canId-shallow 4 (DBCMessage.id msg))
    (tt , tt , tt , map-shallow identJSON (λ _ → tt) _ ,
     map-shallow (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (signal-shallow (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg) , tt)

@0 signalGroup-shallow : ∀ sg → Shallow 2 (formatSignalGroup sg)
signalGroup-shallow sg = tt , map-shallow identJSON (λ _ → tt) _ , tt

@0 envVar-shallow : ∀ ev → Shallow 1 (formatEnvironmentVar ev)
envVar-shallow ev = tt , tt , tt , tt , tt , tt

@0 valueTable-shallow : ∀ vt → Shallow 3 (formatValueTable vt)
valueTable-shallow vt = tt , map-shallow formatValueEntry valueEntry-shallow _ , tt

@0 rawValueDesc-shallow : ∀ rvd → Shallow 3 (formatRawValueDesc rvd)
rawValueDesc-shallow rvd =
  fields-++ (formatCANId (RawValueDesc.canId rvd)) _ (canId-shallow 2 (RawValueDesc.canId rvd))
    (tt , map-shallow formatValueEntry valueEntry-shallow _ , tt)

@0 node-shallow : ∀ n → Shallow 1 (formatNode n)
node-shallow n = tt , tt

@0 commentTarget-shallow : ∀ k t → FieldsShallow k (formatCommentTarget t)
commentTarget-shallow k CTNetwork      = tt , tt
commentTarget-shallow k (CTNode _)     = tt , tt , tt
commentTarget-shallow k (CTMessage id) = tt , canId-shallow k id
commentTarget-shallow k (CTSignal id _) = tt , fields-++ (formatCANId id) _ (canId-shallow k id) (tt , tt)
commentTarget-shallow k (CTEnvVar _)   = tt , tt , tt

@0 comment-shallow : ∀ c → Shallow 2 (formatComment c)
comment-shallow c = commentTarget-shallow 0 (DBCComment.target c) , tt , tt

@0 attrType-shallow : ∀ k t → FieldsShallow (suc k) (formatAttrType t)
attrType-shallow k (ATInt _ _)    = tt , tt , tt , tt
attrType-shallow k (ATFloat _ _)  = tt , tt , tt , tt
attrType-shallow k ATString       = tt , tt
attrType-shallow k (ATEnum labels) = tt , map-shallow JString (λ _ → tt) labels , tt
attrType-shallow k (ATHex _ _)    = tt , tt , tt , tt

@0 attrValue-shallow : ∀ k v → FieldsShallow k (formatAttrValue v)
attrValue-shallow k (AVInt _)    = tt , tt , tt
attrValue-shallow k (AVFloat _)  = tt , tt , tt
attrValue-shallow k (AVString _) = tt , tt , tt
attrValue-shallow k (AVEnum _)   = tt , tt , tt
attrValue-shallow k (AVHex _)    = tt , tt , tt

@0 attrTarget-shallow : ∀ k t → FieldsShallow k (formatAttrTarget t)
attrTarget-shallow k ATgtNetwork          = tt , tt
attrTarget-shallow k (ATgtNode _)         = tt , tt , tt
attrTarget-shallow k (ATgtMessage id)     = tt , canId-shallow k id
attrTarget-shallow k (ATgtSignal id _)    = tt , fields-++ (formatCANId id) _ (canId-shallow k id) (tt , tt)
attrTarget-shallow k (ATgtEnvVar _)       = tt , tt , tt
attrTarget-shallow k (ATgtNodeMsg _ id)   = tt , tt , canId-shallow k id
attrTarget-shallow k (ATgtNodeSig _ id _) = tt , tt , fields-++ (formatCANId id) _ (canId-shallow k id) (tt , tt)

@0 attribute-shallow : ∀ a → Shallow 3 (formatAttribute a)
attribute-shallow (DBCAttrDef d)     = tt , tt , tt , attrType-shallow 0 _ , tt
attribute-shallow (DBCAttrDefault d) = tt , tt , attrValue-shallow 1 _ , tt
attribute-shallow (DBCAttrAssign a)  = tt , tt , attrTarget-shallow 1 _ , attrValue-shallow 1 _ , tt

-- Every value `formatDBC` writes nests at most 7 deep.
@0 formatDBC-shallow : ∀ dbc → Shallow 7 (formatDBC dbc)
formatDBC-shallow dbc =
  tt ,
  map-shallow formatDBCMessage message-shallow _ ,
  map-shallow formatSignalGroup (λ sg → shallow-≤ (formatSignalGroup sg) (≤ᵇ⇒≤ 2 5 tt) (signalGroup-shallow sg)) _ ,
  map-shallow formatEnvironmentVar (λ ev → shallow-≤ (formatEnvironmentVar ev) (≤ᵇ⇒≤ 1 5 tt) (envVar-shallow ev)) _ ,
  map-shallow formatValueTable (λ vt → shallow-≤ (formatValueTable vt) (≤ᵇ⇒≤ 3 5 tt) (valueTable-shallow vt)) _ ,
  map-shallow formatNode (λ n → shallow-≤ (formatNode n) (≤ᵇ⇒≤ 1 5 tt) (node-shallow n)) _ ,
  map-shallow formatComment (λ c → shallow-≤ (formatComment c) (≤ᵇ⇒≤ 2 5 tt) (comment-shallow c)) _ ,
  map-shallow formatAttribute (λ a → shallow-≤ (formatAttribute a) (≤ᵇ⇒≤ 3 5 tt) (attribute-shallow a)) _ ,
  map-shallow formatRawValueDesc (λ r → shallow-≤ (formatRawValueDesc r) (≤ᵇ⇒≤ 3 5 tt) (rawValueDesc-shallow r)) _ ,
  tt
