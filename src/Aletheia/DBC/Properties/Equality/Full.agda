-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Slice 2 (V2 exact check) decidable-equality tower — the `_≟-*_` instances
-- missing from `Aletheia.DBC.Properties.Equality`, built up to `_≟-DBC_`
-- (E2_ROUTE_B.md §6.1), so the round-trip check can deep-compare `parseText
-- (formatText d)` with `d`.
--
-- S2.1 (this first chunk): `_≟-DLC_` over the `@0`-witness `DLC` record (§6.2),
-- the one step with any residual novelty — spiked first as cheap insurance.
module Aletheia.DBC.Properties.Equality.Full where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Properties using (≡-dec)
open import Data.Char using () renaming (_≟_ to _≟ᶜ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Aletheia.CAN.DLC using (DLC; mkDLC)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (_≟ᴵ_)
open import Aletheia.DBC.DecRat using (_≟ᵈ_)
open import Aletheia.DBC.DecRat.Refinement using (IntDecRat; mkIntDecRat; NatDecRat; mkNatDecRat)
open import Aletheia.DBC.Types using
  ( VarType; IntVar; FloatVar; StringVar
  ; AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar; ASNodeMsg; ASNodeSig
  ; CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; Node; ValueTable; EnvironmentVar; SignalGroup; DBCComment; RawValueDesc
  ; AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; DBCMessage; DBC )
open import Aletheia.DBC.Properties.Equality using (_≟-DBCSignal_; _≟-vd_)

-- ── _≟-DLC_ (§6.2) ───────────────────────────────────────────────────────────
--
-- `DLC` carries `@0 bounded : T (code <ᵇ 16)`.  A generic Dec-≡ over the record
-- is blocked: `@0` fields are runtime-erased but NOT definitionally irrelevant,
-- and `--without-K` blocks the K-style congruence over the witness.  The closed-
-- code enumeration sidesteps it — for codes 0..15 the bound reduces to `T true =
-- ⊤`, whose η makes the two erased witnesses convertible WITHOUT inspecting them
-- (`refl` closes each clause); code ≥ 16 makes the bound `T false = ⊥`, closed by
-- an absurd pattern on the erased field.  Same 16-clause shape as the in-tree
-- precedent `dlcBytes-bounded` (JSONParser/MessageWF.agda), which type-checks
-- under `--safe --without-K` today.

dlc-code-inj : ∀ (d₁ d₂ : DLC) → DLC.code d₁ ≡ DLC.code d₂ → d₁ ≡ d₂
dlc-code-inj (mkDLC 0  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 1  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 2  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 3  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 4  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 5  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 6  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 7  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 8  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 9  _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 10 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 11 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 12 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 13 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 14 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC 15 _) (mkDLC _ _) refl = refl
dlc-code-inj (mkDLC (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) ()) _ _

_≟-DLC_ : (d₁ d₂ : DLC) → Dec (d₁ ≡ d₂)
d₁ ≟-DLC d₂ with DLC.code d₁ ≟ DLC.code d₂
... | yes eq = yes (dlc-code-inj d₁ d₂ eq)
... | no ¬p  = no (λ eq → ¬p (cong DLC.code eq))

-- ── S2.2a: a nullary enum + the refinement records ──────────────────────────

-- VarType (3 nullary ctors): diagonal `refl`, off-diagonal `λ ()` (concrete
-- ctors make the mismatch syntactically empty; no catch-all is possible).
_≟-VarType_ : (x y : VarType) → Dec (x ≡ y)
IntVar    ≟-VarType IntVar    = yes refl
FloatVar  ≟-VarType FloatVar  = yes refl
StringVar ≟-VarType StringVar = yes refl
IntVar    ≟-VarType FloatVar  = no (λ ())
IntVar    ≟-VarType StringVar = no (λ ())
FloatVar  ≟-VarType IntVar    = no (λ ())
FloatVar  ≟-VarType StringVar = no (λ ())
StringVar ≟-VarType IntVar    = no (λ ())
StringVar ≟-VarType FloatVar  = no (λ ())

-- IntDecRat / NatDecRat — refinement records `{ value : DecRat ; .witness }`.
-- The witness is `.`-IRRELEVANT, so two records with equal `value` are
-- definitionally equal by proof-irrelevance: `refl` closes it directly.  (§6.1's
-- note to use `T-irrelevant` applies to the RELEVANT-witness `_≟ᴵ_`; here the
-- field is irrelevant, so `T-irrelevant` is neither needed nor usable.)
_≟-IntDecRat_ : (x y : IntDecRat) → Dec (x ≡ y)
mkIntDecRat v₁ _ ≟-IntDecRat mkIntDecRat v₂ _ with v₁ ≟ᵈ v₂
... | yes refl = yes refl
... | no ¬eq  = no (λ { refl → ¬eq refl })

_≟-NatDecRat_ : (x y : NatDecRat) → Dec (x ≡ y)
mkNatDecRat v₁ _ ≟-NatDecRat mkNatDecRat v₂ _ with v₁ ≟ᵈ v₂
... | yes refl = yes refl
... | no ¬eq  = no (λ { refl → ¬eq refl })

-- ── S2.2b: the enums ────────────────────────────────────────────────────────

-- AttrScope (7 nullary ctors): retraction encoding (`asᴺ`/`asⁱ` round-trip ⇒
-- injective) — O(N) clauses instead of the 49 explicit ones.
private
  asᴺ : AttrScope → ℕ
  asᴺ ASNetwork = 0
  asᴺ ASNode    = 1
  asᴺ ASMessage = 2
  asᴺ ASSignal  = 3
  asᴺ ASEnvVar  = 4
  asᴺ ASNodeMsg = 5
  asᴺ ASNodeSig = 6

  asⁱ : ℕ → AttrScope
  asⁱ 0 = ASNetwork
  asⁱ 1 = ASNode
  asⁱ 2 = ASMessage
  asⁱ 3 = ASSignal
  asⁱ 4 = ASEnvVar
  asⁱ 5 = ASNodeMsg
  asⁱ _ = ASNodeSig

  as-rt : ∀ (x : AttrScope) → asⁱ (asᴺ x) ≡ x
  as-rt ASNetwork = refl
  as-rt ASNode    = refl
  as-rt ASMessage = refl
  as-rt ASSignal  = refl
  as-rt ASEnvVar  = refl
  as-rt ASNodeMsg = refl
  as-rt ASNodeSig = refl

_≟-AttrScope_ : (x y : AttrScope) → Dec (x ≡ y)
x ≟-AttrScope y with asᴺ x ≟ asᴺ y
... | yes eq = yes (trans (sym (as-rt x)) (trans (cong asⁱ eq) (as-rt y)))
... | no ¬p  = no (λ e → ¬p (cong asᴺ e))

-- CommentTarget (5 ctors, some carry args): diagonal compares args, off-diagonal
-- `no (λ ())` (concrete distinct ctors ARE syntactically empty).
_≟-CommentTarget_ : (x y : CommentTarget) → Dec (x ≡ y)
CTNetwork     ≟-CommentTarget CTNetwork     = yes refl
CTNode n₁     ≟-CommentTarget CTNode n₂     with n₁ ≟ᴵ n₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
CTMessage m₁  ≟-CommentTarget CTMessage m₂  with m₁ ≟-CANId m₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
CTSignal m₁ s₁ ≟-CommentTarget CTSignal m₂ s₂ with m₁ ≟-CANId m₂ | s₁ ≟ᴵ s₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
CTEnvVar e₁   ≟-CommentTarget CTEnvVar e₂   with e₁ ≟ᴵ e₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
CTNetwork    ≟-CommentTarget CTNode _     = no (λ ())
CTNetwork    ≟-CommentTarget CTMessage _  = no (λ ())
CTNetwork    ≟-CommentTarget CTSignal _ _ = no (λ ())
CTNetwork    ≟-CommentTarget CTEnvVar _   = no (λ ())
CTNode _     ≟-CommentTarget CTNetwork    = no (λ ())
CTNode _     ≟-CommentTarget CTMessage _  = no (λ ())
CTNode _     ≟-CommentTarget CTSignal _ _ = no (λ ())
CTNode _     ≟-CommentTarget CTEnvVar _   = no (λ ())
CTMessage _  ≟-CommentTarget CTNetwork    = no (λ ())
CTMessage _  ≟-CommentTarget CTNode _     = no (λ ())
CTMessage _  ≟-CommentTarget CTSignal _ _ = no (λ ())
CTMessage _  ≟-CommentTarget CTEnvVar _   = no (λ ())
CTSignal _ _ ≟-CommentTarget CTNetwork    = no (λ ())
CTSignal _ _ ≟-CommentTarget CTNode _     = no (λ ())
CTSignal _ _ ≟-CommentTarget CTMessage _  = no (λ ())
CTSignal _ _ ≟-CommentTarget CTEnvVar _   = no (λ ())
CTEnvVar _   ≟-CommentTarget CTNetwork    = no (λ ())
CTEnvVar _   ≟-CommentTarget CTNode _     = no (λ ())
CTEnvVar _   ≟-CommentTarget CTMessage _  = no (λ ())
CTEnvVar _   ≟-CommentTarget CTSignal _ _ = no (λ ())

-- AttrType (5 ctors): ATInt/ATHex bounds via `_≟-IntDecRat_`/`_≟-NatDecRat_`,
-- ATFloat via `_≟ᵈ_`, ATEnum labels via `≡-dec (≡-dec _≟ᶜ_)`.
_≟-AttrType_ : (x y : AttrType) → Dec (x ≡ y)
ATInt mn₁ mx₁ ≟-AttrType ATInt mn₂ mx₂ with mn₁ ≟-IntDecRat mn₂ | mx₁ ≟-IntDecRat mx₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
ATFloat mn₁ mx₁ ≟-AttrType ATFloat mn₂ mx₂ with mn₁ ≟ᵈ mn₂ | mx₁ ≟ᵈ mx₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
ATString ≟-AttrType ATString = yes refl
ATEnum vs₁ ≟-AttrType ATEnum vs₂ with ≡-dec (≡-dec _≟ᶜ_) vs₁ vs₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
ATHex mn₁ mx₁ ≟-AttrType ATHex mn₂ mx₂ with mn₁ ≟-NatDecRat mn₂ | mx₁ ≟-NatDecRat mx₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
ATInt _ _   ≟-AttrType ATFloat _ _ = no (λ ())
ATInt _ _   ≟-AttrType ATString    = no (λ ())
ATInt _ _   ≟-AttrType ATEnum _    = no (λ ())
ATInt _ _   ≟-AttrType ATHex _ _   = no (λ ())
ATFloat _ _ ≟-AttrType ATInt _ _   = no (λ ())
ATFloat _ _ ≟-AttrType ATString    = no (λ ())
ATFloat _ _ ≟-AttrType ATEnum _    = no (λ ())
ATFloat _ _ ≟-AttrType ATHex _ _   = no (λ ())
ATString    ≟-AttrType ATInt _ _   = no (λ ())
ATString    ≟-AttrType ATFloat _ _ = no (λ ())
ATString    ≟-AttrType ATEnum _    = no (λ ())
ATString    ≟-AttrType ATHex _ _   = no (λ ())
ATEnum _    ≟-AttrType ATInt _ _   = no (λ ())
ATEnum _    ≟-AttrType ATFloat _ _ = no (λ ())
ATEnum _    ≟-AttrType ATString    = no (λ ())
ATEnum _    ≟-AttrType ATHex _ _   = no (λ ())
ATHex _ _   ≟-AttrType ATInt _ _   = no (λ ())
ATHex _ _   ≟-AttrType ATFloat _ _ = no (λ ())
ATHex _ _   ≟-AttrType ATString    = no (λ ())
ATHex _ _   ≟-AttrType ATEnum _    = no (λ ())

-- AttrValue (5 ctors).
_≟-AttrValue_ : (x y : AttrValue) → Dec (x ≡ y)
AVInt i₁    ≟-AttrValue AVInt i₂    with i₁ ≟-IntDecRat i₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
AVFloat d₁  ≟-AttrValue AVFloat d₂  with d₁ ≟ᵈ d₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
AVString s₁ ≟-AttrValue AVString s₂ with ≡-dec _≟ᶜ_ s₁ s₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
AVEnum n₁   ≟-AttrValue AVEnum n₂   with n₁ ≟-NatDecRat n₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
AVHex n₁    ≟-AttrValue AVHex n₂    with n₁ ≟-NatDecRat n₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
AVInt _    ≟-AttrValue AVFloat _  = no (λ ())
AVInt _    ≟-AttrValue AVString _ = no (λ ())
AVInt _    ≟-AttrValue AVEnum _   = no (λ ())
AVInt _    ≟-AttrValue AVHex _    = no (λ ())
AVFloat _  ≟-AttrValue AVInt _    = no (λ ())
AVFloat _  ≟-AttrValue AVString _ = no (λ ())
AVFloat _  ≟-AttrValue AVEnum _   = no (λ ())
AVFloat _  ≟-AttrValue AVHex _    = no (λ ())
AVString _ ≟-AttrValue AVInt _    = no (λ ())
AVString _ ≟-AttrValue AVFloat _  = no (λ ())
AVString _ ≟-AttrValue AVEnum _   = no (λ ())
AVString _ ≟-AttrValue AVHex _    = no (λ ())
AVEnum _   ≟-AttrValue AVInt _    = no (λ ())
AVEnum _   ≟-AttrValue AVFloat _  = no (λ ())
AVEnum _   ≟-AttrValue AVString _ = no (λ ())
AVEnum _   ≟-AttrValue AVHex _    = no (λ ())
AVHex _    ≟-AttrValue AVInt _    = no (λ ())
AVHex _    ≟-AttrValue AVFloat _  = no (λ ())
AVHex _    ≟-AttrValue AVString _ = no (λ ())
AVHex _    ≟-AttrValue AVEnum _   = no (λ ())

-- AttrTarget (7 ctors, args via `_≟ᴵ_` / `_≟-CANId_`).
_≟-AttrTarget_ : (x y : AttrTarget) → Dec (x ≡ y)
ATgtNetwork      ≟-AttrTarget ATgtNetwork      = yes refl
ATgtNode n₁      ≟-AttrTarget ATgtNode n₂      with n₁ ≟ᴵ n₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
ATgtMessage m₁   ≟-AttrTarget ATgtMessage m₂   with m₁ ≟-CANId m₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
ATgtSignal m₁ s₁ ≟-AttrTarget ATgtSignal m₂ s₂ with m₁ ≟-CANId m₂ | s₁ ≟ᴵ s₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
ATgtEnvVar e₁    ≟-AttrTarget ATgtEnvVar e₂    with e₁ ≟ᴵ e₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
ATgtNodeMsg n₁ m₁ ≟-AttrTarget ATgtNodeMsg n₂ m₂ with n₁ ≟ᴵ n₂ | m₁ ≟-CANId m₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    = no (λ { refl → ¬p refl })
ATgtNodeSig n₁ m₁ s₁ ≟-AttrTarget ATgtNodeSig n₂ m₂ s₂ with n₁ ≟ᴵ n₂ | m₁ ≟-CANId m₂ | s₁ ≟ᴵ s₂
... | yes refl | yes refl | yes refl = yes refl
... | no ¬p    | _        | _        = no (λ { refl → ¬p refl })
... | _        | no ¬p    | _        = no (λ { refl → ¬p refl })
... | _        | _        | no ¬p    = no (λ { refl → ¬p refl })
ATgtNetwork    ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtNetwork    ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtNetwork    ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtNetwork    ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtNetwork    ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())
ATgtNetwork    ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())
ATgtNode _     ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())
ATgtMessage _  ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())
ATgtSignal _ _ ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())
ATgtEnvVar _   ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtNodeMsg _ _ ≟-AttrTarget ATgtNodeSig _ _ _ = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtNetwork      = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtNode _       = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtMessage _    = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtSignal _ _   = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtEnvVar _     = no (λ ())
ATgtNodeSig _ _ _ ≟-AttrTarget ATgtNodeMsg _ _  = no (λ ())

-- ── S2.2c: the records (accessor-style chain-`with`, like the ceiling) ───────

_≟-Node_ : (x y : Node) → Dec (x ≡ y)
x ≟-Node y with Node.name x ≟ᴵ Node.name y
... | no ¬p    = no (λ eq → ¬p (cong Node.name eq))
... | yes refl = yes refl

_≟-SignalGroup_ : (x y : SignalGroup) → Dec (x ≡ y)
x ≟-SignalGroup y
  with SignalGroup.name x ≟ᴵ SignalGroup.name y
... | no ¬p = no (λ eq → ¬p (cong SignalGroup.name eq))
... | yes refl
  with ≡-dec _≟ᴵ_ (SignalGroup.signals x) (SignalGroup.signals y)
... | no ¬p = no (λ eq → ¬p (cong SignalGroup.signals eq))
... | yes refl = yes refl

_≟-EnvVar_ : (x y : EnvironmentVar) → Dec (x ≡ y)
x ≟-EnvVar y
  with EnvironmentVar.name x ≟ᴵ EnvironmentVar.name y
... | no ¬p = no (λ eq → ¬p (cong EnvironmentVar.name eq))
... | yes refl
  with EnvironmentVar.varType x ≟-VarType EnvironmentVar.varType y
... | no ¬p = no (λ eq → ¬p (cong EnvironmentVar.varType eq))
... | yes refl
  with EnvironmentVar.initial x ≟ᵈ EnvironmentVar.initial y
... | no ¬p = no (λ eq → ¬p (cong EnvironmentVar.initial eq))
... | yes refl
  with EnvironmentVar.minimum x ≟ᵈ EnvironmentVar.minimum y
... | no ¬p = no (λ eq → ¬p (cong EnvironmentVar.minimum eq))
... | yes refl
  with EnvironmentVar.maximum x ≟ᵈ EnvironmentVar.maximum y
... | no ¬p = no (λ eq → ¬p (cong EnvironmentVar.maximum eq))
... | yes refl = yes refl

_≟-ValueTable_ : (x y : ValueTable) → Dec (x ≡ y)
x ≟-ValueTable y
  with ValueTable.name x ≟ᴵ ValueTable.name y
... | no ¬p = no (λ eq → ¬p (cong ValueTable.name eq))
... | yes refl
  with ≡-dec _≟-vd_ (ValueTable.entries x) (ValueTable.entries y)
... | no ¬p = no (λ eq → ¬p (cong ValueTable.entries eq))
... | yes refl = yes refl

_≟-DBCComment_ : (x y : DBCComment) → Dec (x ≡ y)
x ≟-DBCComment y
  with DBCComment.target x ≟-CommentTarget DBCComment.target y
... | no ¬p = no (λ eq → ¬p (cong DBCComment.target eq))
... | yes refl
  with ≡-dec _≟ᶜ_ (DBCComment.text x) (DBCComment.text y)
... | no ¬p = no (λ eq → ¬p (cong DBCComment.text eq))
... | yes refl = yes refl

_≟-AttrDef_ : (x y : AttrDef) → Dec (x ≡ y)
x ≟-AttrDef y
  with ≡-dec _≟ᶜ_ (AttrDef.name x) (AttrDef.name y)
... | no ¬p = no (λ eq → ¬p (cong AttrDef.name eq))
... | yes refl
  with AttrDef.scope x ≟-AttrScope AttrDef.scope y
... | no ¬p = no (λ eq → ¬p (cong AttrDef.scope eq))
... | yes refl
  with AttrDef.attrType x ≟-AttrType AttrDef.attrType y
... | no ¬p = no (λ eq → ¬p (cong AttrDef.attrType eq))
... | yes refl = yes refl

_≟-AttrDefault_ : (x y : AttrDefault) → Dec (x ≡ y)
x ≟-AttrDefault y
  with ≡-dec _≟ᶜ_ (AttrDefault.name x) (AttrDefault.name y)
... | no ¬p = no (λ eq → ¬p (cong AttrDefault.name eq))
... | yes refl
  with AttrDefault.value x ≟-AttrValue AttrDefault.value y
... | no ¬p = no (λ eq → ¬p (cong AttrDefault.value eq))
... | yes refl = yes refl

_≟-AttrAssign_ : (x y : AttrAssign) → Dec (x ≡ y)
x ≟-AttrAssign y
  with ≡-dec _≟ᶜ_ (AttrAssign.name x) (AttrAssign.name y)
... | no ¬p = no (λ eq → ¬p (cong AttrAssign.name eq))
... | yes refl
  with AttrAssign.target x ≟-AttrTarget AttrAssign.target y
... | no ¬p = no (λ eq → ¬p (cong AttrAssign.target eq))
... | yes refl
  with AttrAssign.value x ≟-AttrValue AttrAssign.value y
... | no ¬p = no (λ eq → ¬p (cong AttrAssign.value eq))
... | yes refl = yes refl

_≟-DBCAttribute_ : (x y : DBCAttribute) → Dec (x ≡ y)
DBCAttrDef a₁     ≟-DBCAttribute DBCAttrDef a₂     with a₁ ≟-AttrDef a₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
DBCAttrDefault a₁ ≟-DBCAttribute DBCAttrDefault a₂ with a₁ ≟-AttrDefault a₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
DBCAttrAssign a₁  ≟-DBCAttribute DBCAttrAssign a₂  with a₁ ≟-AttrAssign a₂
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
DBCAttrDef _     ≟-DBCAttribute DBCAttrDefault _ = no (λ ())
DBCAttrDef _     ≟-DBCAttribute DBCAttrAssign _  = no (λ ())
DBCAttrDefault _ ≟-DBCAttribute DBCAttrDef _     = no (λ ())
DBCAttrDefault _ ≟-DBCAttribute DBCAttrAssign _  = no (λ ())
DBCAttrAssign _  ≟-DBCAttribute DBCAttrDef _     = no (λ ())
DBCAttrAssign _  ≟-DBCAttribute DBCAttrDefault _ = no (λ ())

_≟-RawValueDesc_ : (x y : RawValueDesc) → Dec (x ≡ y)
x ≟-RawValueDesc y
  with RawValueDesc.canId x ≟-CANId RawValueDesc.canId y
... | no ¬p = no (λ eq → ¬p (cong RawValueDesc.canId eq))
... | yes refl
  with RawValueDesc.signalName x ≟ᴵ RawValueDesc.signalName y
... | no ¬p = no (λ eq → ¬p (cong RawValueDesc.signalName eq))
... | yes refl
  with ≡-dec _≟-vd_ (RawValueDesc.entries x) (RawValueDesc.entries y)
... | no ¬p = no (λ eq → ¬p (cong RawValueDesc.entries eq))
... | yes refl = yes refl

-- ── S2.2d: the top — DBCMessage (6 fields) and DBC (9 fields) ────────────────

_≟-DBCMessage_ : (x y : DBCMessage) → Dec (x ≡ y)
x ≟-DBCMessage y
  with DBCMessage.id x ≟-CANId DBCMessage.id y
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.id eq))
... | yes refl
  with DBCMessage.name x ≟ᴵ DBCMessage.name y
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.name eq))
... | yes refl
  with DBCMessage.dlc x ≟-DLC DBCMessage.dlc y
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.dlc eq))
... | yes refl
  with DBCMessage.sender x ≟ᴵ DBCMessage.sender y
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.sender eq))
... | yes refl
  with ≡-dec _≟ᴵ_ (DBCMessage.senders x) (DBCMessage.senders y)
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.senders eq))
... | yes refl
  with ≡-dec _≟-DBCSignal_ (DBCMessage.signals x) (DBCMessage.signals y)
... | no ¬p = no (λ eq → ¬p (cong DBCMessage.signals eq))
... | yes refl = yes refl

_≟-DBC_ : (x y : DBC) → Dec (x ≡ y)
x ≟-DBC y
  with ≡-dec _≟ᶜ_ (DBC.version x) (DBC.version y)
... | no ¬p = no (λ eq → ¬p (cong DBC.version eq))
... | yes refl
  with ≡-dec _≟-DBCMessage_ (DBC.messages x) (DBC.messages y)
... | no ¬p = no (λ eq → ¬p (cong DBC.messages eq))
... | yes refl
  with ≡-dec _≟-SignalGroup_ (DBC.signalGroups x) (DBC.signalGroups y)
... | no ¬p = no (λ eq → ¬p (cong DBC.signalGroups eq))
... | yes refl
  with ≡-dec _≟-EnvVar_ (DBC.environmentVars x) (DBC.environmentVars y)
... | no ¬p = no (λ eq → ¬p (cong DBC.environmentVars eq))
... | yes refl
  with ≡-dec _≟-ValueTable_ (DBC.valueTables x) (DBC.valueTables y)
... | no ¬p = no (λ eq → ¬p (cong DBC.valueTables eq))
... | yes refl
  with ≡-dec _≟-Node_ (DBC.nodes x) (DBC.nodes y)
... | no ¬p = no (λ eq → ¬p (cong DBC.nodes eq))
... | yes refl
  with ≡-dec _≟-DBCComment_ (DBC.comments x) (DBC.comments y)
... | no ¬p = no (λ eq → ¬p (cong DBC.comments eq))
... | yes refl
  with ≡-dec _≟-DBCAttribute_ (DBC.attributes x) (DBC.attributes y)
... | no ¬p = no (λ eq → ¬p (cong DBC.attributes eq))
... | yes refl
  with ≡-dec _≟-RawValueDesc_ (DBC.unresolvedValueDescs x) (DBC.unresolvedValueDescs y)
... | no ¬p = no (λ eq → ¬p (cong DBC.unresolvedValueDescs eq))
... | yes refl = yes refl
