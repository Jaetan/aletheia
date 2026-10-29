-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What `formatDBC` writes for a bounded DBC stays within the bounds the DBC
-- met: an array it writes for a list has that list's length, and every
-- number it writes is in the range `replyRange` gives its place under a
-- reply's `dbc` key (`formatDBC-in-range`).  Every definition is erased, so
-- a runtime module can carry the proof beside the JSON it formats and
-- MAlonzo compiles none of it.
--
-- The length lemmas reduce to `length-map`, since every array the formatter
-- writes is `JArray (map format-… field)`.  The number proof walks the
-- formatter one helper at a time.  A signal's start bit, length, `DecRat`
-- fields, multiplex values and value keys, a value table's and an
-- unresolved description's keys, an environment variable's numbers and an
-- attribute's are in their rows' ranges by `IsBoundedDBC` (its
-- `DBCMagnitudes`); a big-endian start bit is a position in a frame of at
-- most 64 bytes.  The other numbers are in range by construction: a CAN id
-- is below its constructor's maximum (its witness), a DLC's byte count is
-- at most 64, and a variable type at most 2.
module Aletheia.DBC.Formatter.Bounded where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (∣_∣)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; map) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty as List⁺ using ()
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _^_; _≤_; _<ᵇ_; _/_; _%_; z≤n; s≤s)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using
  ( ≤-refl; ≤-trans; ≤-pred; <ᵇ⇒<; m≤m+n; 1+n≰n; m∸n≤m; ∸-monoˡ-≤
  ; *-monoˡ-≤; +-mono-≤; suc-pred; ≤ᵇ⇒≤ )
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Nullary.Decidable using (recompute)

open import Aletheia.CAN.Constants using
  (standard-can-id-max; extended-can-id-max; max-standard-can-id; max-extended-can-id)
open import Aletheia.CAN.DLC using (mkDLC; dlcToBytes; dlcBytes)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; physicalBitPos; unconvertStartBit)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Bounds using
  ( IsBoundedDBC; DBCMagnitudes; SignalMagnitudes; EnvVarMagnitudes; AttributeMagnitudes
  ; SmallKeys; SmallSelectors; SmallType; SmallValue )
open import Aletheia.DBC.DecRat using (mkDecRat; toℚ; 2^a·5^b-NonZero)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.DecRat.Magnitude using
  (SmallDecRat; smallDecRat-components; intDecRat-≤; natDecRat-≤)
open import Aletheia.DBC.Formatter using
  ( ℕtoJSON; formatCANId; formatPresence; formatValueEntry
  ; formatDBCSignal; formatDBCMessage; formatSignalGroup; formatEnvironmentVar
  ; formatValueTable; formatRawValueDesc; formatNode; formatCommentTarget
  ; formatComment; formatAttrType; formatAttrValue; formatAttrTarget
  ; formatAttribute; formatDBC; identJSON )
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; SignalPresence; Always; When
  ; EnvironmentVar; ValueTable; RawValueDesc; DBCComment
  ; VarType; IntVar; FloatVar; StringVar; varTypeToℕ
  ; CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign )
open import Aletheia.Limits using
  (max-rational-component-magnitude; max-start-bit; max-var-type; max-value-description-key-magnitude)
open import Aletheia.Prelude using (ℕtoℚ; fromℤ)
open import Aletheia.Protocol.JSON.Types using
  (JSON; JString; ComponentsWithin; Shallow; FieldsShallow)
open import Aletheia.Protocol.JSON.Shallow using (shallow-≤; map-shallow; fields-++)
open import Aletheia.Protocol.ReplyRange using
  ( NumbersAt; ListNumbersAt; FieldsNumbersAt; InRange; replyRange
  ; natural-in; integer-in; byteCount-in; map-at; mapAll-at )

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

-- Every number at its place under a reply's `dbc` key, for a value and an
-- object's fields.
@0 At : List String → Maybe String → JSON → Set
At = NumbersAt replyRange

@0 FieldsAt : List String → Maybe String → List (String × JSON) → Set
FieldsAt = FieldsNumbersAt replyRange

-- ---- One number ----

-- A small `DecRat`: `toℚ` keeps its numerator and its denominator 2^a·5^b,
-- the two components `SmallDecRat` bounds.
@0 toℚ-components : ∀ d → SmallDecRat d → ComponentsWithin max-rational-component-magnitude (toℚ d)
toℚ-components (mkDecRat num a b c) small =
  let parts = smallDecRat-components (mkDecRat num a b c) small
  in proj₁ parts
   , subst (_≤ max-rational-component-magnitude)
           (sym (suc-pred (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄))
           (proj₂ parts)

-- ---- Numbers small by construction ----

-- A CAN id is at most its width's largest: below its constructor's
-- maximum, 2^11 or 2^29, the witness recomputed from the decidable test
-- since it is irrelevant.
@0 stdCanId-≤ : ∀ {n} → .(T (n <ᵇ standard-can-id-max)) → n ≤ max-standard-can-id
stdCanId-≤ {n} p = ≤-pred (<ᵇ⇒< n standard-can-id-max (recompute (T? (n <ᵇ standard-can-id-max)) p))

@0 extCanId-≤ : ∀ {n} → .(T (n <ᵇ extended-can-id-max)) → n ≤ max-extended-can-id
extCanId-≤ {n} p = ≤-pred (<ᵇ⇒< n extended-can-id-max (recompute (T? (n <ᵇ extended-can-id-max)) p))

-- The type a CAN id's flag gives the fields written after it.
@0 widthTag : CANId → Maybe String
widthTag (Standard _ _) = just "standard"
widthTag (Extended _ _) = just "extended"

-- The ranges a place gives a standard and an extended CAN id.
@0 IdsAt : List String → Set
IdsAt p =
  (∀ n → n ≤ max-standard-can-id → InRange (replyRange (p ∷ʳ "id") (just "standard")) (ℕtoℚ n))
  × (∀ n → n ≤ max-extended-can-id → InRange (replyRange (p ∷ʳ "id") (just "extended")) (ℕtoℚ n))

-- A CAN id's fields, before others: its flag, then its `id` in its width's
-- range, the fields after typed by the width; and alone.
@0 canId-++ : ∀ p t cid {ys} → IdsAt p
  → FieldsAt p (widthTag cid) ys → FieldsAt p t (formatCANId cid ++ₗ ys)
canId-++ p t (Standard n q) (hs , _) rest = tt , hs n (stdCanId-≤ q) , rest
canId-++ p t (Extended n q) (_ , he) rest = tt , he n (extCanId-≤ q) , rest

@0 canId-at : ∀ p t cid → IdsAt p → FieldsAt p t (formatCANId cid)
canId-at p t (Standard n q) (hs , _) = tt , hs n (stdCanId-≤ q) , tt
canId-at p t (Extended n q) (_ , he) = tt , he n (extCanId-≤ q) , tt

-- A message's DLC as a byte count, at either width.
@0 dlc-in : ∀ cid d → InRange (replyRange ("dbc" ∷ "messages" ∷ "dlc" ∷ []) (widthTag cid)) (ℕtoℚ (dlcBytes d))
dlc-in (Standard _ _) d = byteCount-in d
dlc-in (Extended _ _) d = byteCount-in d

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
@0 physicalBitPos-≤ : ∀ fb b → fb ≤ 64 → physicalBitPos fb BigEndian b ≤ max-start-bit
physicalBitPos-≤ fb b fb≤64 =
  let bytes : ((fb ∸ 1) ∸ (b / 8)) * 8 ≤ 504
      bytes = *-monoˡ-≤ 8 (≤-trans (m∸n≤m (fb ∸ 1) (b / 8)) (∸-monoˡ-≤ 1 fb≤64))
      bit : b % 8 ≤ 7
      bit = ≤-pred (m%n<n b 8)
  in +-mono-≤ bytes bit

-- The start bit the formatter writes: the stored one for little endian, a
-- position in the frame for big endian.
@0 unconvertStartBit-≤ : ∀ fb bo s l → fb ≤ 64 → s ≤ max-start-bit
  → unconvertStartBit fb bo s l ≤ max-start-bit
unconvertStartBit-≤ _  LittleEndian _ _ _     s≤ = s≤
unconvertStartBit-≤ fb BigEndian    s l fb≤64 _  = physicalBitPos-≤ fb (s + l ∸ 1) fb≤64

@0 varType-≤ : ∀ t → varTypeToℕ t ≤ max-var-type
varType-≤ IntVar    = z≤n
varType-≤ FloatVar  = s≤s z≤n
varType-≤ StringVar = ≤-refl

-- ---- The formatter's helpers ----

@0 presence-at : ∀ p → SmallSelectors p
  → FieldsAt ("dbc" ∷ "messages" ∷ "signals" ∷ []) nothing (formatPresence p)
presence-at Always      _   = tt , tt
presence-at (When _ vs) sel = tt , tt , mapAll-at natural-in (List⁺.toList vs) sel , tt

-- A value-description entry at the place of the array holding it, of any
-- type, since each entry is an object of its own.
@0 entries-at : ∀ p t es
  → (∀ z → ∣ z ∣ ≤ max-value-description-key-magnitude → InRange (replyRange (p ∷ʳ "value") nothing) (fromℤ z))
  → SmallKeys es → ListNumbersAt replyRange p t (map formatValueEntry es)
entries-at p t es h = mapAll-at (λ { (z , _) small → h z small , tt , tt }) es

@0 signal-at : ∀ {t} fb → fb ≤ 64 → ∀ sig → SignalMagnitudes sig
  → At ("dbc" ∷ "messages" ∷ "signals" ∷ []) t (formatDBCSignal fb sig)
signal-at fb fb≤64 sig m =
  let def = DBCSignal.signalDef sig in
  tt
  , natural-in _ (unconvertStartBit-≤ fb (DBCSignal.byteOrder sig) _ _ fb≤64 (SignalMagnitudes.startBit m))
  , natural-in _ (SignalMagnitudes.bitLength m)
  , tt
  , tt
  , toℚ-components (SignalDef.factor def) (SignalMagnitudes.factor m)
  , toℚ-components (SignalDef.offset def) (SignalMagnitudes.offset m)
  , toℚ-components (SignalDef.minimum def) (SignalMagnitudes.minimum m)
  , toℚ-components (SignalDef.maximum def) (SignalMagnitudes.maximum m)
  , tt
  , map-at (λ _ → tt) _
  , entries-at _ _ _ integer-in (SignalMagnitudes.keys m)
  , presence-at _ (SignalMagnitudes.selectors m)

@0 message-at : ∀ msg → All SignalMagnitudes (DBCMessage.signals msg)
  → At ("dbc" ∷ "messages" ∷ []) nothing (formatDBCMessage msg)
message-at msg ms =
  canId-++ _ _ (DBCMessage.id msg) (natural-in , natural-in)
    ( tt
    , dlc-in (DBCMessage.id msg) (DBCMessage.dlc msg)
    , tt
    , map-at (λ _ → tt) _
    , mapAll-at (signal-at {widthTag (DBCMessage.id msg)} _ (dlcBytes-≤64 (DBCMessage.dlc msg))) _ ms
    , tt )

@0 signalGroup-at : ∀ sg → At ("dbc" ∷ "signalGroups" ∷ []) nothing (formatSignalGroup sg)
signalGroup-at _ = tt , map-at (λ _ → tt) _ , tt

@0 envVar-at : ∀ ev → EnvVarMagnitudes ev → At ("dbc" ∷ "environmentVars" ∷ []) nothing (formatEnvironmentVar ev)
envVar-at ev m =
  tt
  , natural-in _ (varType-≤ (EnvironmentVar.varType ev))
  , toℚ-components (EnvironmentVar.initial ev) (EnvVarMagnitudes.initial m)
  , toℚ-components (EnvironmentVar.minimum ev) (EnvVarMagnitudes.minimum m)
  , toℚ-components (EnvironmentVar.maximum ev) (EnvVarMagnitudes.maximum m)
  , tt

@0 valueTable-at : ∀ vt → SmallKeys (ValueTable.entries vt) → At ("dbc" ∷ "valueTables" ∷ []) nothing (formatValueTable vt)
valueTable-at _ ks = tt , entries-at _ _ _ integer-in ks , tt

@0 rawValueDesc-at : ∀ rvd → SmallKeys (RawValueDesc.entries rvd)
  → At ("dbc" ∷ "unresolvedValueDescs" ∷ []) nothing (formatRawValueDesc rvd)
rawValueDesc-at rvd ks =
  canId-++ _ _ (RawValueDesc.canId rvd) (natural-in , natural-in) (tt , entries-at _ _ _ integer-in ks , tt)

@0 node-at : ∀ n → At ("dbc" ∷ "nodes" ∷ []) nothing (formatNode n)
node-at _ = tt , tt

@0 commentTarget-at : ∀ t → FieldsAt ("dbc" ∷ "comments" ∷ "target" ∷ []) nothing (formatCommentTarget t)
commentTarget-at CTNetwork       = tt , tt
commentTarget-at (CTNode _)      = tt , tt , tt
commentTarget-at (CTMessage id)  = tt , canId-at _ _ id (natural-in , natural-in)
commentTarget-at (CTSignal id _) = tt , canId-++ _ _ id (natural-in , natural-in) (tt , tt)
commentTarget-at (CTEnvVar _)    = tt , tt , tt

@0 comment-at : ∀ c → At ("dbc" ∷ "comments" ∷ []) nothing (formatComment c)
comment-at c = commentTarget-at (DBCComment.target c) , tt , tt

@0 attrType-at : ∀ t → SmallType t → FieldsAt ("dbc" ∷ "attributes" ∷ "attrType" ∷ []) nothing (formatAttrType t)
attrType-at (ATInt mn mx) (l , h) =
  tt , integer-in _ (intDecRat-≤ mn l) , integer-in _ (intDecRat-≤ mx h) , tt
attrType-at (ATFloat mn mx) (l , h) = tt , toℚ-components mn l , toℚ-components mx h , tt
attrType-at ATString _ = tt , tt
attrType-at (ATEnum labels) _ = tt , map-at (λ _ → tt) labels , tt
attrType-at (ATHex mn mx) (l , h) =
  tt , natural-in _ (natDecRat-≤ mn l) , natural-in _ (natDecRat-≤ mx h) , tt

@0 attrValue-at : ∀ v → SmallValue v → FieldsAt ("dbc" ∷ "attributes" ∷ "value" ∷ []) nothing (formatAttrValue v)
attrValue-at (AVInt v)    s = tt , integer-in _ (intDecRat-≤ v s) , tt
attrValue-at (AVFloat v)  s = tt , toℚ-components v s , tt
attrValue-at (AVString _) _ = tt , tt , tt
attrValue-at (AVEnum v)   s = tt , natural-in _ (natDecRat-≤ v s) , tt
attrValue-at (AVHex v)    s = tt , natural-in _ (natDecRat-≤ v s) , tt

@0 attrTarget-at : ∀ t → FieldsAt ("dbc" ∷ "attributes" ∷ "target" ∷ []) nothing (formatAttrTarget t)
attrTarget-at ATgtNetwork          = tt , tt
attrTarget-at (ATgtNode _)         = tt , tt , tt
attrTarget-at (ATgtMessage id)     = tt , canId-at _ _ id (natural-in , natural-in)
attrTarget-at (ATgtSignal id _)    = tt , canId-++ _ _ id (natural-in , natural-in) (tt , tt)
attrTarget-at (ATgtEnvVar _)       = tt , tt , tt
attrTarget-at (ATgtNodeMsg _ id)   = tt , tt , canId-at _ _ id (natural-in , natural-in)
attrTarget-at (ATgtNodeSig _ id _) = tt , tt , canId-++ _ _ id (natural-in , natural-in) (tt , tt)

@0 attribute-at : ∀ a → AttributeMagnitudes a → At ("dbc" ∷ "attributes" ∷ []) nothing (formatAttribute a)
attribute-at (DBCAttrDef d)     m = tt , tt , tt , attrType-at _ m , tt
attribute-at (DBCAttrDefault d) m = tt , tt , attrValue-at _ m , tt
attribute-at (DBCAttrAssign a)  m = tt , tt , attrTarget-at _ , attrValue-at _ m , tt

-- ---- The theorem ----

-- Every number `formatDBC` writes for a bounded DBC is in the range of its
-- place under a reply's `dbc` key.
@0 formatDBC-in-range : ∀ dbc → IsBoundedDBC dbc → At ("dbc" ∷ []) nothing (formatDBC dbc)
formatDBC-in-range dbc b =
  let m = IsBoundedDBC.magnitudes b
  in tt
   , mapAll-at message-at _ (DBCMagnitudes.signals m)
   , map-at signalGroup-at _
   , mapAll-at envVar-at _ (DBCMagnitudes.environmentVars m)
   , mapAll-at valueTable-at _ (DBCMagnitudes.valueTables m)
   , map-at node-at _
   , map-at comment-at _
   , mapAll-at attribute-at _ (DBCMagnitudes.attributes m)
   , mapAll-at rawValueDesc-at _ (DBCMagnitudes.unresolvedValueDescs m)
   , tt

-- ============================================================================
-- DEPTH
-- ============================================================================

-- `formatDBC` nests at most 7 deep: the DBC, its messages, a message, its
-- signals, a signal, its value descriptions, an entry.

@0 canId-shallow : ∀ k id → FieldsShallow k (formatCANId id)
canId-shallow k (Standard _ _) = tt , tt , tt
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
