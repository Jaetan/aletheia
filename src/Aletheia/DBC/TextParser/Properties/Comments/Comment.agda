{-# OPTIONS --without-K #-}

-- `parseComment-roundtrip` — per-line-construct roundtrip for the DBC
-- `CM_ [<target>] "<text>";\n` line (B.3.d Layer 3 Commit 3b).
--
-- Grammar slice (BNF section E from `Aletheia.DBC.TextParser`):
--   comment        ::= "CM_" (ws comment-target)? ws string-lit
--                      ws? ";" newline
--   comment-target ::= "BU_" ws identifier
--                    | "BO_" ws nat
--                    | "SG_" ws nat ws identifier
--                    | "EV_" ws identifier
--
-- Bind chain (matches `Aletheia.DBC.TextParser.Comments.parseComment`):
--
--   string "CM_" *> parseWS *>
--   (parseCommentTarget <|> pure CTNetwork) >>= λ target →
--   parseStringLit                          >>= λ text →
--   parseWSOpt *> char ';' *> parseNewline *>
--   many parseNewline *>
--   pure (mkComment target text)
--
-- The `<|>` fall-through encodes the network-vs-target dispatch: each of
-- the four target-keyword branches (BU_/BO_/SG_/EV_) must either succeed
-- *whole* (consuming its trailing parseWS) or fail *cleanly* (with the
-- parser cursor unmoved) before `pure CTNetwork` fires.  When the target
-- is `CTNetwork`, the four branches all fail at the very first `char`
-- step (the cursor sits on `'"'` from the upcoming `parseStringLit`),
-- so the alt chain reduces by closed-Char comparison.
--
-- CAN-ID roundtrip: `wrapCTMessage` and `wrapCTSignal` route the parsed
-- raw ℕ through `buildCANId` (cantools bit-31 flag).  We discharge
-- `buildCANId (rawCanIdℕ cid) ≡ just cid` here as a private lemma —
-- it's a universal CANId fact that doesn't depend on the construct, so
-- it could equally well live in a CANId properties module; placed here
-- for now since CM_ is the first call site.
module Aletheia.DBC.TextParser.Properties.Comments.Comment where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Properties using (length-++; ++-identityʳ) renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _<ᵇ_; _+_; _∸_; _^_;
                            s≤s; z≤n)
open import Data.Nat.Properties using
  (≤-trans; ≤-refl; n≤1+n; m≤m+n; m≤n+m; <-trans;
   <ᵇ⇒<; <⇒<ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; <⇒≱; m+n∸n≡m)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
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
open import Aletheia.DBC.TextParser.Comments using
  (parseComment; parseCommentTarget;
   parseBUTgt; parseBOTgt; parseSGTgt; parseEVTgt;
   wrapCTMessage; wrapCTSignal)
open import Aletheia.DBC.TextParser.Topology using (buildCANId; extFlagBit)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.DBC.TextFormatter.Comments using (emitComment-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (digitChar; showℕ-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment; mkComment
  )

open import Aletheia.Prelude using (ifᵀ_then_else_; ifᵀ-witness)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; []-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; advancePositions-++;
   parseNatural-showNat-chars; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; char-matches; parseWS-one-space;
   alt-right-nothing; alt-left-just; bind-nothing;
   parseIdentifier-roundtrip; parseStringLit-roundtrip;
   quoteStringLit-chars-shape; parseCharsSeq-success; escape-body-chars)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF;
   manyHelper-parseNewline-exhaust)

-- ============================================================================
-- Per-name precondition (Identifier-level)
-- ============================================================================

-- Each Identifier-typed comment-target field decomposes its `name`
-- string as `c ∷ cs` with `isHSpace c ≡ false`, so the `parseWS`
-- before the identifier stops cleanly after consuming the single
-- separator space.  Layer 4 will discharge this universally from
-- `validIdentifierᵇ` via the `isIdentStart→¬isHSpace` bridge (see
-- `project_b3d_layer4_owed_lemmas.md`).
NameStop : Identifier → Set
NameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (toList (Identifier.name n) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- Per-target precondition (DBCComment-level)
-- ============================================================================

-- Discharge the per-target name preconditions; the network/message
-- targets carry no per-name precondition (CTNetwork has no identifier;
-- CTMessage's payload is a numeric CAN ID).  Pattern-matching on the
-- target constructor reduces to the relevant per-name shape.
CommentTargetStop : DBCComment → Set
CommentTargetStop c with DBCComment.target c
... | CTNetwork    = ⊤
... | CTNode n     = NameStop n
... | CTMessage _  = ⊤
... | CTSignal _ s = NameStop s
... | CTEnvVar ev  = NameStop ev

-- ============================================================================
-- Bool/arithmetic helpers (private)
-- ============================================================================

private
  -- `b ≡ false` from `¬ T b`; used to drive the `else` branch of an
  -- `ifᵀ_then_else_`.
  not-T⇒false : ∀ {b : Bool} → ¬ T b → b ≡ false
  not-T⇒false {true}  ¬tt = ⊥-elim (¬tt tt)
  not-T⇒false {false} _   = refl

  -- `(m ≤ᵇ n) ≡ false` from `n < m`; drives the outer `ifᵀ` to its
  -- `else` branch in the Standard buildCANId case.
  n<m⇒m≤ᵇn≡false : ∀ {m n : ℕ} → n < m → (m ≤ᵇ n) ≡ false
  n<m⇒m≤ᵇn≡false {m} {n} n<m = not-T⇒false ¬T-m≤ᵇn
    where
      ¬T-m≤ᵇn : ¬ T (m ≤ᵇ n)
      ¬T-m≤ᵇn pf = <⇒≱ n<m (≤ᵇ⇒≤ m n pf)

  -- `ifᵀ b then f else e ≡ e` when `b ≡ false`.  Mirror of `ifᵀ-witness`
  -- (which handles the true branch).
  ifᵀ-witness-false : ∀ {A : Set} {b : Bool} (f : T b → A) (e : A)
    → b ≡ false → ifᵀ b then f else e ≡ e
  ifᵀ-witness-false {b = false} f e refl = refl

  -- 2048 < 2^31 — closed-ℕ comparison; `<ᵇ` is a builtin so the
  -- bool-valued comparison reduces in O(1).  Used to chain
  -- `n < 2048 ⟹ n < 2^31` in the Standard buildCANId case.
  2048<extFlagBit : 2048 < extFlagBit
  2048<extFlagBit = <ᵇ⇒< 2048 extFlagBit tt

-- ============================================================================
-- buildCANId roundtrip
-- ============================================================================

-- `buildCANId (rawCanIdℕ cid) ≡ just cid` for every CANId.  Two cases:
--   * Standard n pf: rawCanIdℕ = n; outer ifᵀ on `2^31 ≤ᵇ n` is false
--     (n < 2048 < 2^31); inner ifᵀ on `n <ᵇ 2048` is true via the
--     existing pf — `ifᵀ-witness pf` gives the result with the *original*
--     pf, no proof-irrelevance needed.
--   * Extended n pf: rawCanIdℕ = n + 2^31; outer ifᵀ is true
--     (2^31 ≤ n + 2^31); subtraction `(n + 2^31) ∸ 2^31 ≡ n` rewrites
--     the inner ifᵀ's domain to `n <ᵇ 2^29`, and `ifᵀ-witness pf` lands.
buildCANId-rawCanIdℕ : ∀ (cid : CANId) → buildCANId (rawCanIdℕ cid) ≡ just cid
buildCANId-rawCanIdℕ (Standard n pf) =
  trans
    (ifᵀ-witness-false {b = extFlagBit ≤ᵇ n}
       (λ _ →
         let m = n ∸ extFlagBit
         in ifᵀ m <ᵇ extended-can-id-max
              then (λ pf' → just (Extended m pf'))
              else nothing)
       (ifᵀ n <ᵇ standard-can-id-max
          then (λ pf' → just (Standard n pf'))
          else nothing)
       (n<m⇒m≤ᵇn≡false n<extFlagBit))
    (ifᵀ-witness {b = n <ᵇ standard-can-id-max}
       (λ pf' → just (Standard n pf')) nothing pf)
  where
    n<extFlagBit : n < extFlagBit
    n<extFlagBit = <-trans (<ᵇ⇒< n standard-can-id-max pf) 2048<extFlagBit
buildCANId-rawCanIdℕ (Extended n pf) =
  trans
    (ifᵀ-witness {b = extFlagBit ≤ᵇ n + extFlagBit}
       (λ _ →
         let m = (n + extFlagBit) ∸ extFlagBit
         in ifᵀ m <ᵇ extended-can-id-max
              then (λ pf' → just (Extended m pf'))
              else nothing)
       (ifᵀ (n + extFlagBit) <ᵇ standard-can-id-max
          then (λ pf' → just (Standard (n + extFlagBit) pf'))
          else nothing)
       outer-pf)
    inner-eq
  where
    outer-pf : T (extFlagBit ≤ᵇ n + extFlagBit)
    outer-pf = ≤⇒≤ᵇ (m≤n+m extFlagBit n)

    n+ext∸ext≡n : (n + extFlagBit) ∸ extFlagBit ≡ n
    n+ext∸ext≡n = m+n∸n≡m n extFlagBit

    -- `subst` chain instead of `rewrite n+ext∸ext≡n`.  The `rewrite`
    -- form desugars to a `with f x in eq` whose with-abstraction
    -- generalises over the entire goal type — which here contains a
    -- nested `ifᵀ` whose then-branch is itself a complex lambda.  Under
    -- `--without-K` the abstraction blows up and the elaborator runs
    -- the heap to multi-GB scale (CM_ exhausts even -M48G with the
    -- rewrite form).  Pointwise `subst` on a single-occurrence target
    -- (the bool argument of the outer `ifᵀ`) leaves the surrounding
    -- shape intact.
    inner-eq :
        (ifᵀ (n + extFlagBit) ∸ extFlagBit <ᵇ extended-can-id-max
            then (λ pf' →
              just (Extended ((n + extFlagBit) ∸ extFlagBit) pf'))
            else nothing)
      ≡ just (Extended n pf)
    inner-eq =
      subst
        (λ k →
          (ifᵀ k <ᵇ extended-can-id-max
              then (λ pf' → just (Extended k pf'))
              else nothing)
          ≡ just (Extended n pf))
        (sym n+ext∸ext≡n)
        (ifᵀ-witness {b = n <ᵇ extended-can-id-max}
          (λ pf' → just (Extended n pf')) nothing pf)

-- ============================================================================
-- Char-class disjointness helpers — duplicated from
-- `Properties/ValueTables/ValueTable.agda` (private there).  Lift to a
-- shared location once the third construct needs it.
-- ============================================================================

-- From `NameStop n` (decomposing `toList name = c ∷ cs` with
-- `isHSpace c ≡ false`), derive `SuffixStops isHSpace (toList name ++
-- rest)`.  Mirrors `Topology/Nodes.agda`'s `name-stop-extends`.
private
  name-stop-extends : ∀ (n : Identifier) (rest : List Char)
    → NameStop n
    → SuffixStops isHSpace (toList (Identifier.name n) ++ₗ rest)
  name-stop-extends n rest (c , cs , name-eq , c-non-hspace) =
    subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
          (sym name-eq)
          (∷-stop c-non-hspace)

-- `digitChar d` is one of `'0' .. '9'` for `d < 10`; the fallthrough
-- `digitChar _ = '0'` covers `d ≥ 10`.  Eleven cases mirror
-- `digitChar-≢-dash` in `DecRatParse.Properties`.
private
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

-- `SuffixStops isHSpace (showℕ-dec-chars n ++ rest)` from
-- `showNat-chars-head` + `digitChar-not-isHSpace`.  Used wherever a
-- `parseWS-one-space` precondition follows a digit run.
private
  showNat-chars-head-stop-isHSpace : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops isHSpace (showℕ-dec-chars n ++ₗ rest)
  showNat-chars-head-stop-isHSpace n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

-- `SuffixStops isHSpace (quoteStringLit-chars s ++ rest)` — head is
-- `'"'`, so its `isHSpace` reduces to `false`.
private
  quoteStringLit-chars-head-isHSpace : ∀ (s : String) (rest : List Char)
    → SuffixStops isHSpace (quoteStringLit-chars s ++ₗ rest)
  quoteStringLit-chars-head-isHSpace s rest =
    subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
          (sym (quoteStringLit-chars-shape s))
          (∷-stop refl)

-- ============================================================================
-- Per-target roundtrip: parseBUTgt
-- ============================================================================

-- `parseBUTgt = string "BU_" *> parseWS *> parseIdentifier *> parseWS *>
-- pure (CTNode n)`.  On input `"BU_" ++ ' ' ∷ name ++ ' ' ∷ rest` with
-- a non-hspace head on `rest`, it consumes the keyword + 1 space + name
-- + 1 space and returns `CTNode n`.  Four `bind-just-step`s chained.
parseBUTgt-roundtrip :
    ∀ (pos : Position) (n : Identifier) (rest : List Char)
  → NameStop n
  → SuffixStops isHSpace rest
  → parseBUTgt pos
      (toList "BU_" ++ₗ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ rest)
    ≡ just (mkResult (CTNode n)
             (advancePosition
               (advancePositions
                 (advancePosition
                   (advancePositions pos (toList "BU_")) ' ')
                 (toList (Identifier.name n))) ' ')
             rest)
parseBUTgt-roundtrip pos n rest name-stop rest-stop =
  trans step-string-BU
    (trans step-parseWS-1
      (trans step-parseIdentifier
        step-parseWS-2))
  where
    pos1 : Position
    pos1 = advancePositions pos (toList "BU_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos3 : Position
    pos3 = advancePositions pos2 (toList (Identifier.name n))

    pos4 : Position
    pos4 = advancePosition pos3 ' '

    rest1 : List Char
    rest1 = ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ rest

    rest2 : List Char
    rest2 = toList (Identifier.name n) ++ₗ ' ' ∷ rest

    rest3 : List Char
    rest3 = ' ' ∷ rest

    cont-after-string : String → Parser CommentTarget
    cont-after-string _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ n' →
      parseWS >>= λ _ →
      pure (CTNode n')

    cont-after-WS-1 : List Char → Parser CommentTarget
    cont-after-WS-1 _ =
      parseIdentifier >>= λ n' →
      parseWS >>= λ _ →
      pure (CTNode n')

    cont-after-ident : Identifier → Parser CommentTarget
    cont-after-ident n' =
      parseWS >>= λ _ →
      pure (CTNode n')

    step-string-BU :
      parseBUTgt pos (toList "BU_" ++ₗ rest1)
      ≡ cont-after-string "BU_" pos1 rest1
    step-string-BU =
      bind-just-step (string "BU_") cont-after-string
                     pos (toList "BU_" ++ₗ rest1)
                     "BU_" pos1 rest1
                     (string-success pos "BU_" rest1)

    step-parseWS-1 :
      cont-after-string "BU_" pos1 rest1
      ≡ cont-after-WS-1 (' ' ∷ []) pos2 rest2
    step-parseWS-1 =
      bind-just-step parseWS cont-after-WS-1
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2
                        (name-stop-extends n (' ' ∷ rest) name-stop))

    step-parseIdentifier :
      cont-after-WS-1 (' ' ∷ []) pos2 rest2
      ≡ cont-after-ident n pos3 rest3
    step-parseIdentifier =
      bind-just-step parseIdentifier cont-after-ident
                     pos2 rest2
                     n pos3 rest3
                     (parseIdentifier-roundtrip pos2 n (' ' ∷ rest)
                        (∷-stop refl))

    step-parseWS-2 :
      cont-after-ident n pos3 rest3
      ≡ just (mkResult (CTNode n) pos4 rest)
    step-parseWS-2 =
      bind-just-step parseWS (λ _ → pure (CTNode n))
                     pos3 rest3
                     (' ' ∷ []) pos4 rest
                     (parseWS-one-space pos3 rest rest-stop)

-- ============================================================================
-- Per-target roundtrip: parseEVTgt
-- ============================================================================

-- Same shape as `parseBUTgt-roundtrip` with `EV_` keyword and
-- `CTEnvVar` constructor.
parseEVTgt-roundtrip :
    ∀ (pos : Position) (n : Identifier) (rest : List Char)
  → NameStop n
  → SuffixStops isHSpace rest
  → parseEVTgt pos
      (toList "EV_" ++ₗ ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ rest)
    ≡ just (mkResult (CTEnvVar n)
             (advancePosition
               (advancePositions
                 (advancePosition
                   (advancePositions pos (toList "EV_")) ' ')
                 (toList (Identifier.name n))) ' ')
             rest)
parseEVTgt-roundtrip pos n rest name-stop rest-stop =
  trans step-string-EV
    (trans step-parseWS-1
      (trans step-parseIdentifier
        step-parseWS-2))
  where
    pos1 : Position
    pos1 = advancePositions pos (toList "EV_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos3 : Position
    pos3 = advancePositions pos2 (toList (Identifier.name n))

    pos4 : Position
    pos4 = advancePosition pos3 ' '

    rest1 : List Char
    rest1 = ' ' ∷ toList (Identifier.name n) ++ₗ ' ' ∷ rest

    rest2 : List Char
    rest2 = toList (Identifier.name n) ++ₗ ' ' ∷ rest

    rest3 : List Char
    rest3 = ' ' ∷ rest

    cont-after-string : String → Parser CommentTarget
    cont-after-string _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ n' →
      parseWS >>= λ _ →
      pure (CTEnvVar n')

    cont-after-WS-1 : List Char → Parser CommentTarget
    cont-after-WS-1 _ =
      parseIdentifier >>= λ n' →
      parseWS >>= λ _ →
      pure (CTEnvVar n')

    cont-after-ident : Identifier → Parser CommentTarget
    cont-after-ident n' =
      parseWS >>= λ _ →
      pure (CTEnvVar n')

    step-string-EV :
      parseEVTgt pos (toList "EV_" ++ₗ rest1)
      ≡ cont-after-string "EV_" pos1 rest1
    step-string-EV =
      bind-just-step (string "EV_") cont-after-string
                     pos (toList "EV_" ++ₗ rest1)
                     "EV_" pos1 rest1
                     (string-success pos "EV_" rest1)

    step-parseWS-1 :
      cont-after-string "EV_" pos1 rest1
      ≡ cont-after-WS-1 (' ' ∷ []) pos2 rest2
    step-parseWS-1 =
      bind-just-step parseWS cont-after-WS-1
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2
                        (name-stop-extends n (' ' ∷ rest) name-stop))

    step-parseIdentifier :
      cont-after-WS-1 (' ' ∷ []) pos2 rest2
      ≡ cont-after-ident n pos3 rest3
    step-parseIdentifier =
      bind-just-step parseIdentifier cont-after-ident
                     pos2 rest2
                     n pos3 rest3
                     (parseIdentifier-roundtrip pos2 n (' ' ∷ rest)
                        (∷-stop refl))

    step-parseWS-2 :
      cont-after-ident n pos3 rest3
      ≡ just (mkResult (CTEnvVar n) pos4 rest)
    step-parseWS-2 =
      bind-just-step parseWS (λ _ → pure (CTEnvVar n))
                     pos3 rest3
                     (' ' ∷ []) pos4 rest
                     (parseWS-one-space pos3 rest rest-stop)

-- ============================================================================
-- wrapCTMessage / wrapCTSignal roundtrip — discharge the inner with-aux
-- ============================================================================

-- The `wrapCTMessage` and `wrapCTSignal` helpers in
-- `TextParser.Comments` use a `with buildCANId r` to dispatch — out of
-- range IDs `fail`.  The roundtrip case has `r = rawCanIdℕ cid`, so by
-- `buildCANId-rawCanIdℕ` the with-branch is the `just cid` arm.  Outer
-- `with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid` lifts
-- the inner with-aux, and the `| refl` pattern unifies the with-result
-- with `just cid`.
wrapCTMessage-roundtrip : ∀ (cid : CANId) (pos : Position) (input : List Char)
  → wrapCTMessage (rawCanIdℕ cid) pos input
    ≡ just (mkResult (CTMessage cid) pos input)
wrapCTMessage-roundtrip cid pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

wrapCTSignal-roundtrip : ∀ (cid : CANId) (sig : Identifier)
                            (pos : Position) (input : List Char)
  → wrapCTSignal (rawCanIdℕ cid) sig pos input
    ≡ just (mkResult (CTSignal cid sig) pos input)
wrapCTSignal-roundtrip cid sig pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

-- ============================================================================
-- Per-target roundtrip: parseBOTgt
-- ============================================================================

-- `parseBOTgt = string "BO_" *> parseWS *> parseNatural *> parseWS *>
-- wrapCTMessage r`.  Five `bind-just-step`s where the last one chains
-- into `wrapCTMessage-roundtrip` instead of a literal `pure`.
parseBOTgt-roundtrip :
    ∀ (pos : Position) (cid : CANId) (rest : List Char)
  → SuffixStops isHSpace rest
  → parseBOTgt pos
      (toList "BO_" ++ₗ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ ' ' ∷ rest)
    ≡ just (mkResult (CTMessage cid)
             (advancePosition
               (advancePositions
                 (advancePosition
                   (advancePositions pos (toList "BO_")) ' ')
                 (showℕ-dec-chars (rawCanIdℕ cid))) ' ')
             rest)
parseBOTgt-roundtrip pos cid rest rest-stop =
  trans step-string-BO
    (trans step-parseWS-1
      (trans step-parseNatural
        (trans step-parseWS-2
          step-wrapCTMessage)))
  where
    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)

    pos1 : Position
    pos1 = advancePositions pos (toList "BO_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos3 : Position
    pos3 = advancePositions pos2 digits

    pos4 : Position
    pos4 = advancePosition pos3 ' '

    rest1 : List Char
    rest1 = ' ' ∷ digits ++ₗ ' ' ∷ rest

    rest2 : List Char
    rest2 = digits ++ₗ ' ' ∷ rest

    rest3 : List Char
    rest3 = ' ' ∷ rest

    cont-after-string : String → Parser CommentTarget
    cont-after-string _ =
      parseWS >>= λ _ →
      parseNatural >>= λ r →
      parseWS >>= λ _ →
      wrapCTMessage r

    cont-after-WS-1 : List Char → Parser CommentTarget
    cont-after-WS-1 _ =
      parseNatural >>= λ r →
      parseWS >>= λ _ →
      wrapCTMessage r

    cont-after-natural : ℕ → Parser CommentTarget
    cont-after-natural r =
      parseWS >>= λ _ →
      wrapCTMessage r

    digits-non-hspace : SuffixStops isHSpace (digits ++ₗ ' ' ∷ rest)
    digits-non-hspace =
      showNat-chars-head-stop-isHSpace (rawCanIdℕ cid) (' ' ∷ rest)

    step-string-BO :
      parseBOTgt pos (toList "BO_" ++ₗ rest1)
      ≡ cont-after-string "BO_" pos1 rest1
    step-string-BO =
      bind-just-step (string "BO_") cont-after-string
                     pos (toList "BO_" ++ₗ rest1)
                     "BO_" pos1 rest1
                     (string-success pos "BO_" rest1)

    step-parseWS-1 :
      cont-after-string "BO_" pos1 rest1
      ≡ cont-after-WS-1 (' ' ∷ []) pos2 rest2
    step-parseWS-1 =
      bind-just-step parseWS cont-after-WS-1
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 digits-non-hspace)

    step-parseNatural :
      cont-after-WS-1 (' ' ∷ []) pos2 rest2
      ≡ cont-after-natural (rawCanIdℕ cid) pos3 rest3
    step-parseNatural =
      bind-just-step parseNatural cont-after-natural
                     pos2 rest2
                     (rawCanIdℕ cid) pos3 rest3
                     (parseNatural-showNat-chars pos2 (rawCanIdℕ cid)
                        (' ' ∷ rest) (∷-stop refl))

    step-parseWS-2 :
      cont-after-natural (rawCanIdℕ cid) pos3 rest3
      ≡ wrapCTMessage (rawCanIdℕ cid) pos4 rest
    step-parseWS-2 =
      bind-just-step parseWS (λ _ → wrapCTMessage (rawCanIdℕ cid))
                     pos3 rest3
                     (' ' ∷ []) pos4 rest
                     (parseWS-one-space pos3 rest rest-stop)

    step-wrapCTMessage :
      wrapCTMessage (rawCanIdℕ cid) pos4 rest
      ≡ just (mkResult (CTMessage cid) pos4 rest)
    step-wrapCTMessage = wrapCTMessage-roundtrip cid pos4 rest

-- ============================================================================
-- Per-target roundtrip: parseSGTgt
-- ============================================================================

-- `parseSGTgt = string "SG_" *> parseWS *> parseNatural *> parseWS *>
-- parseIdentifier *> parseWS *> wrapCTSignal r sig`.  Seven steps:
-- six `bind-just-step`s + final `wrapCTSignal-roundtrip`.
parseSGTgt-roundtrip :
    ∀ (pos : Position) (cid : CANId) (sig : Identifier) (rest : List Char)
  → NameStop sig
  → SuffixStops isHSpace rest
  → parseSGTgt pos
      (toList "SG_" ++ₗ ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ rest)
    ≡ just (mkResult (CTSignal cid sig)
             (advancePosition
               (advancePositions
                 (advancePosition
                   (advancePositions
                     (advancePosition
                       (advancePositions pos (toList "SG_")) ' ')
                     (showℕ-dec-chars (rawCanIdℕ cid))) ' ')
                 (toList (Identifier.name sig))) ' ')
             rest)
parseSGTgt-roundtrip pos cid sig rest name-stop rest-stop =
  trans step-string-SG
    (trans step-parseWS-1
      (trans step-parseNatural
        (trans step-parseWS-2
          (trans step-parseIdentifier
            (trans step-parseWS-3
              step-wrapCTSignal)))))
  where
    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)

    name : List Char
    name = toList (Identifier.name sig)

    pos1 : Position
    pos1 = advancePositions pos (toList "SG_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos3 : Position
    pos3 = advancePositions pos2 digits

    pos4 : Position
    pos4 = advancePosition pos3 ' '

    pos5 : Position
    pos5 = advancePositions pos4 name

    pos6 : Position
    pos6 = advancePosition pos5 ' '

    rest1 : List Char
    rest1 = ' ' ∷ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ rest

    rest2 : List Char
    rest2 = digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ rest

    rest3 : List Char
    rest3 = ' ' ∷ name ++ₗ ' ' ∷ rest

    rest4 : List Char
    rest4 = name ++ₗ ' ' ∷ rest

    rest5 : List Char
    rest5 = ' ' ∷ rest

    cont-after-string : String → Parser CommentTarget
    cont-after-string _ =
      parseWS >>= λ _ →
      parseNatural >>= λ r →
      parseWS >>= λ _ →
      parseIdentifier >>= λ s →
      parseWS >>= λ _ →
      wrapCTSignal r s

    cont-after-WS-1 : List Char → Parser CommentTarget
    cont-after-WS-1 _ =
      parseNatural >>= λ r →
      parseWS >>= λ _ →
      parseIdentifier >>= λ s →
      parseWS >>= λ _ →
      wrapCTSignal r s

    cont-after-natural : ℕ → Parser CommentTarget
    cont-after-natural r =
      parseWS >>= λ _ →
      parseIdentifier >>= λ s →
      parseWS >>= λ _ →
      wrapCTSignal r s

    cont-after-WS-2 : List Char → Parser CommentTarget
    cont-after-WS-2 _ =
      parseIdentifier >>= λ s →
      parseWS >>= λ _ →
      wrapCTSignal (rawCanIdℕ cid) s

    cont-after-ident : Identifier → Parser CommentTarget
    cont-after-ident s =
      parseWS >>= λ _ →
      wrapCTSignal (rawCanIdℕ cid) s

    digits-non-hspace : SuffixStops isHSpace (digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ rest)
    digits-non-hspace =
      showNat-chars-head-stop-isHSpace (rawCanIdℕ cid)
        (' ' ∷ name ++ₗ ' ' ∷ rest)

    step-string-SG :
      parseSGTgt pos (toList "SG_" ++ₗ rest1)
      ≡ cont-after-string "SG_" pos1 rest1
    step-string-SG =
      bind-just-step (string "SG_") cont-after-string
                     pos (toList "SG_" ++ₗ rest1)
                     "SG_" pos1 rest1
                     (string-success pos "SG_" rest1)

    step-parseWS-1 :
      cont-after-string "SG_" pos1 rest1
      ≡ cont-after-WS-1 (' ' ∷ []) pos2 rest2
    step-parseWS-1 =
      bind-just-step parseWS cont-after-WS-1
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 digits-non-hspace)

    step-parseNatural :
      cont-after-WS-1 (' ' ∷ []) pos2 rest2
      ≡ cont-after-natural (rawCanIdℕ cid) pos3 rest3
    step-parseNatural =
      bind-just-step parseNatural cont-after-natural
                     pos2 rest2
                     (rawCanIdℕ cid) pos3 rest3
                     (parseNatural-showNat-chars pos2 (rawCanIdℕ cid)
                        (' ' ∷ name ++ₗ ' ' ∷ rest) (∷-stop refl))

    step-parseWS-2 :
      cont-after-natural (rawCanIdℕ cid) pos3 rest3
      ≡ cont-after-WS-2 (' ' ∷ []) pos4 rest4
    step-parseWS-2 =
      bind-just-step parseWS cont-after-WS-2
                     pos3 rest3
                     (' ' ∷ []) pos4 rest4
                     (parseWS-one-space pos3 rest4
                        (name-stop-extends sig (' ' ∷ rest) name-stop))

    step-parseIdentifier :
      cont-after-WS-2 (' ' ∷ []) pos4 rest4
      ≡ cont-after-ident sig pos5 rest5
    step-parseIdentifier =
      bind-just-step parseIdentifier cont-after-ident
                     pos4 rest4
                     sig pos5 rest5
                     (parseIdentifier-roundtrip pos4 sig (' ' ∷ rest)
                        (∷-stop refl))

    step-parseWS-3 :
      cont-after-ident sig pos5 rest5
      ≡ wrapCTSignal (rawCanIdℕ cid) sig pos6 rest
    step-parseWS-3 =
      bind-just-step parseWS (λ _ → wrapCTSignal (rawCanIdℕ cid) sig)
                     pos5 rest5
                     (' ' ∷ []) pos6 rest
                     (parseWS-one-space pos5 rest rest-stop)

    step-wrapCTSignal :
      wrapCTSignal (rawCanIdℕ cid) sig pos6 rest
      ≡ just (mkResult (CTSignal cid sig) pos6 rest)
    step-wrapCTSignal = wrapCTSignal-roundtrip cid sig pos6 rest

-- ============================================================================
-- Alt-fail lemmas
-- ============================================================================
--
-- Each `parseXTgt` is `string "XX_" >>= ...`.  When the input doesn't
-- start with the keyword's first char (or diverges at position 1/2 of
-- the keyword), `string "XX_"` returns `nothing` and `bind-nothing`
-- propagates.  Closed-Char `_≈ᵇ_` reduces by primitive `toℕ`
-- comparison, so the proof is `refl` modulo the bind plumbing.

-- Helper: any parseXTgt with `string "XX_"` head fails when the input
-- starts with a char that isn't the keyword's first char.  Specialised
-- below per keyword pair (the first char of every CommentTarget keyword
-- is one of `B / S / E`, so 4 specialisations cover all crossings).
private
  -- `string "BU_"` fails on input starting with `'"'` (the leading
  -- char of every quoteStringLit-chars output).
  string-BU-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → string "BU_" pos ('"' ∷ rest) ≡ nothing
  string-BU-fail-on-quote _ _ = refl

  string-BO-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → string "BO_" pos ('"' ∷ rest) ≡ nothing
  string-BO-fail-on-quote _ _ = refl

  string-SG-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → string "SG_" pos ('"' ∷ rest) ≡ nothing
  string-SG-fail-on-quote _ _ = refl

  string-EV-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → string "EV_" pos ('"' ∷ rest) ≡ nothing
  string-EV-fail-on-quote _ _ = refl

  -- `string "BU_"` fails on input starting with `'B' ∷ 'O' ∷ ...`
  -- (BO_ keyword: first char matches, second diverges).
  string-BU-fail-on-BO : ∀ (pos : Position) (c2 : Char) (rest : List Char)
    → string "BU_" pos ('B' ∷ 'O' ∷ c2 ∷ rest) ≡ nothing
  string-BU-fail-on-BO _ _ _ = refl

  -- `string "BU_"` fails on input starting with `'S'`.
  string-BU-fail-on-S : ∀ (pos : Position) (rest : List Char)
    → string "BU_" pos ('S' ∷ rest) ≡ nothing
  string-BU-fail-on-S _ _ = refl

  -- `string "BO_"` fails on input starting with `'S'`.
  string-BO-fail-on-S : ∀ (pos : Position) (rest : List Char)
    → string "BO_" pos ('S' ∷ rest) ≡ nothing
  string-BO-fail-on-S _ _ = refl

  -- `string "BU_"` fails on input starting with `'E'`.
  string-BU-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "BU_" pos ('E' ∷ rest) ≡ nothing
  string-BU-fail-on-E _ _ = refl

  -- `string "BO_"` fails on input starting with `'E'`.
  string-BO-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "BO_" pos ('E' ∷ rest) ≡ nothing
  string-BO-fail-on-E _ _ = refl

  -- `string "SG_"` fails on input starting with `'E'`.
  string-SG-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "SG_" pos ('E' ∷ rest) ≡ nothing
  string-SG-fail-on-E _ _ = refl

-- Lift each `string-XX-fail-on-Y` to the corresponding `parseXTgt-fail-
-- on-Y` via `bind-nothing` on the keyword head.  The continuation is
-- the rest of the do-block — same shape every time, so the lemma body
-- is a one-liner.
private
  parseBUTgt-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → parseBUTgt pos ('"' ∷ rest) ≡ nothing
  parseBUTgt-fail-on-quote pos rest =
    bind-nothing (string "BU_")
                 (λ _ → parseWS >>= λ _ →
                        parseIdentifier >>= λ n →
                        parseWS >>= λ _ →
                        pure (CTNode n))
                 pos ('"' ∷ rest)
                 (string-BU-fail-on-quote pos rest)

  parseBOTgt-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → parseBOTgt pos ('"' ∷ rest) ≡ nothing
  parseBOTgt-fail-on-quote pos rest =
    bind-nothing (string "BO_")
                 (λ _ → parseWS >>= λ _ →
                        parseNatural >>= λ r →
                        parseWS >>= λ _ →
                        wrapCTMessage r)
                 pos ('"' ∷ rest)
                 (string-BO-fail-on-quote pos rest)

  parseSGTgt-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → parseSGTgt pos ('"' ∷ rest) ≡ nothing
  parseSGTgt-fail-on-quote pos rest =
    bind-nothing (string "SG_")
                 (λ _ → parseWS >>= λ _ →
                        parseNatural >>= λ r →
                        parseWS >>= λ _ →
                        parseIdentifier >>= λ s →
                        parseWS >>= λ _ →
                        wrapCTSignal r s)
                 pos ('"' ∷ rest)
                 (string-SG-fail-on-quote pos rest)

  parseEVTgt-fail-on-quote : ∀ (pos : Position) (rest : List Char)
    → parseEVTgt pos ('"' ∷ rest) ≡ nothing
  parseEVTgt-fail-on-quote pos rest =
    bind-nothing (string "EV_")
                 (λ _ → parseWS >>= λ _ →
                        parseIdentifier >>= λ n →
                        parseWS >>= λ _ →
                        pure (CTEnvVar n))
                 pos ('"' ∷ rest)
                 (string-EV-fail-on-quote pos rest)

  parseBUTgt-fail-on-BO : ∀ (pos : Position) (c2 : Char) (rest : List Char)
    → parseBUTgt pos ('B' ∷ 'O' ∷ c2 ∷ rest) ≡ nothing
  parseBUTgt-fail-on-BO pos c2 rest =
    bind-nothing (string "BU_")
                 (λ _ → parseWS >>= λ _ →
                        parseIdentifier >>= λ n →
                        parseWS >>= λ _ →
                        pure (CTNode n))
                 pos ('B' ∷ 'O' ∷ c2 ∷ rest)
                 (string-BU-fail-on-BO pos c2 rest)

  parseBUTgt-fail-on-S : ∀ (pos : Position) (rest : List Char)
    → parseBUTgt pos ('S' ∷ rest) ≡ nothing
  parseBUTgt-fail-on-S pos rest =
    bind-nothing (string "BU_")
                 (λ _ → parseWS >>= λ _ →
                        parseIdentifier >>= λ n →
                        parseWS >>= λ _ →
                        pure (CTNode n))
                 pos ('S' ∷ rest)
                 (string-BU-fail-on-S pos rest)

  parseBOTgt-fail-on-S : ∀ (pos : Position) (rest : List Char)
    → parseBOTgt pos ('S' ∷ rest) ≡ nothing
  parseBOTgt-fail-on-S pos rest =
    bind-nothing (string "BO_")
                 (λ _ → parseWS >>= λ _ →
                        parseNatural >>= λ r →
                        parseWS >>= λ _ →
                        wrapCTMessage r)
                 pos ('S' ∷ rest)
                 (string-BO-fail-on-S pos rest)

  parseBUTgt-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseBUTgt pos ('E' ∷ rest) ≡ nothing
  parseBUTgt-fail-on-E pos rest =
    bind-nothing (string "BU_")
                 (λ _ → parseWS >>= λ _ →
                        parseIdentifier >>= λ n →
                        parseWS >>= λ _ →
                        pure (CTNode n))
                 pos ('E' ∷ rest)
                 (string-BU-fail-on-E pos rest)

  parseBOTgt-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseBOTgt pos ('E' ∷ rest) ≡ nothing
  parseBOTgt-fail-on-E pos rest =
    bind-nothing (string "BO_")
                 (λ _ → parseWS >>= λ _ →
                        parseNatural >>= λ r →
                        parseWS >>= λ _ →
                        wrapCTMessage r)
                 pos ('E' ∷ rest)
                 (string-BO-fail-on-E pos rest)

  parseSGTgt-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseSGTgt pos ('E' ∷ rest) ≡ nothing
  parseSGTgt-fail-on-E pos rest =
    bind-nothing (string "SG_")
                 (λ _ → parseWS >>= λ _ →
                        parseNatural >>= λ r →
                        parseWS >>= λ _ →
                        parseIdentifier >>= λ s →
                        parseWS >>= λ _ →
                        wrapCTSignal r s)
                 pos ('E' ∷ rest)
                 (string-SG-fail-on-E pos rest)

-- ============================================================================
-- alt-fail-fail — both branches fail, alt fails
-- ============================================================================

-- Combine two `nothing` results across `_<|>_`: when both `p` and `q`
-- fail, so does `p <|> q`.  Cuts the CTSignal/CTEnvVar/CTNetwork
-- alt-chain proofs in half.
private
  alt-fail-fail : ∀ {A : Set} (p q : Parser A) (pos : Position) (input : List Char)
    → p pos input ≡ nothing → q pos input ≡ nothing
    → (p <|> q) pos input ≡ nothing
  alt-fail-fail p q pos input p-eq q-eq =
    trans (alt-right-nothing p q pos input p-eq) q-eq

-- ============================================================================
-- parseCommentTarget-fails-on-quote-prefix — alt-chain fall-through
-- ============================================================================

-- Generic shape of the CTNetwork dispatch failure: when the input
-- starts with `'"'`, every `parseXTgt` keyword head fails (their
-- first chars are `B / B / S / E`, never `'"'`), so the four-fold alt
-- chain returns `nothing`.  Used as the `subst` payload in the
-- CTNetwork branch of `parseComment-roundtrip` after rewriting
-- `quoteStringLit-chars text` into `'"' ∷ escape-body ++ '"' ∷ []`.
private
  parseCommentTarget-fails-on-quote-prefix :
      ∀ (pos : Position) (rest : List Char)
    → parseCommentTarget pos ('"' ∷ rest) ≡ nothing
  parseCommentTarget-fails-on-quote-prefix pos rest =
    alt-fail-fail (parseBUTgt <|> parseBOTgt <|> parseSGTgt) parseEVTgt
      pos ('"' ∷ rest)
      (alt-fail-fail (parseBUTgt <|> parseBOTgt) parseSGTgt
        pos ('"' ∷ rest)
        (alt-fail-fail parseBUTgt parseBOTgt
          pos ('"' ∷ rest)
          (parseBUTgt-fail-on-quote pos rest)
          (parseBOTgt-fail-on-quote pos rest))
        (parseSGTgt-fail-on-quote pos rest))
      (parseEVTgt-fail-on-quote pos rest)

-- ============================================================================
-- parseComment trailing chain: parseStringLit → ... → pure mkComment
-- ============================================================================

-- After the `target ← parseCommentTarget <|> pure CTNetwork` step,
-- every target case continues with the same five-bind chain:
--
--   parseStringLit >>= λ text →
--   parseWSOpt    >>= λ _ →
--   char ';'      >>= λ _ →
--   parseNewline  >>= λ _ →
--   many parseNewline >>= λ _ →
--   pure (mkComment target text)
--
-- This lemma factors that chain out — parametric in `target`, `text`,
-- and the outer `suffix`.  Five `bind-just-step`s + a final
-- `cong`-with-`pure`.
parseStringLit-to-pure-roundtrip :
    ∀ (pos : Position) (target : CommentTarget) (text : String)
        (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → (parseStringLit >>= λ t →
     parseWSOpt >>= λ _ →
     char ';' >>= λ _ →
     parseNewline >>= λ _ →
     many parseNewline >>= λ _ →
     pure (mkComment target t)) pos
      (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ suffix)
    ≡ just (mkResult (mkComment target text)
             (advancePosition
               (advancePosition
                 (advancePositions pos (quoteStringLit-chars text)) ';')
               '\n')
             suffix)
parseStringLit-to-pure-roundtrip pos target text suffix nl-stop =
  trans step-stringLit
    (trans step-WSOpt
      (trans step-char-semi
        (trans step-newline
          step-many-newline)))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos quoted

    pos-after-WSOpt : Position
    pos-after-WSOpt = pos-after-quoted

    pos-after-semi : Position
    pos-after-semi = advancePosition pos-after-WSOpt ';'

    pos-after-LF : Position
    pos-after-LF = advancePosition pos-after-semi '\n'

    rest-after-quoted : List Char
    rest-after-quoted = ';' ∷ '\n' ∷ suffix

    rest-after-WSOpt : List Char
    rest-after-WSOpt = rest-after-quoted

    rest-after-semi : List Char
    rest-after-semi = '\n' ∷ suffix

    rest-after-LF : List Char
    rest-after-LF = suffix

    -- After parseStringLit, all later binds use `text` (the bound
    -- variable).  The continuations capture `text` directly.
    cont-after-stringLit : String → Parser DBCComment
    cont-after-stringLit t =
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment target t)

    cont-after-WSOpt : List Char → Parser DBCComment
    cont-after-WSOpt _ =
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment target text)

    cont-after-semi : Char → Parser DBCComment
    cont-after-semi _ =
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment target text)

    cont-after-newline : Char → Parser DBCComment
    cont-after-newline _ =
      many parseNewline >>= λ _ →
      pure (mkComment target text)

    cont-after-many-newline : List Char → Parser DBCComment
    cont-after-many-newline _ =
      pure (mkComment target text)

    -- parseStringLit demands `SuffixStops (λ c → c ≈ᵇ '"') (';' ∷ '\n'
    -- ∷ suffix)` — head is `;`, which `≈ᵇ '"'` reduces to false.
    semi-not-quote : SuffixStops (λ c → c ≈ᵇ '"') rest-after-quoted
    semi-not-quote = ∷-stop refl

    step-stringLit :
      (parseStringLit >>= cont-after-stringLit) pos
        (quoted ++ₗ rest-after-quoted)
      ≡ cont-after-stringLit text pos-after-quoted rest-after-quoted
    step-stringLit =
      bind-just-step parseStringLit cont-after-stringLit
                     pos (quoted ++ₗ rest-after-quoted)
                     text pos-after-quoted rest-after-quoted
                     (parseStringLit-roundtrip pos text rest-after-quoted
                        semi-not-quote)

    step-WSOpt :
      cont-after-stringLit text pos-after-quoted rest-after-quoted
      ≡ cont-after-WSOpt [] pos-after-WSOpt rest-after-WSOpt
    step-WSOpt =
      bind-just-step parseWSOpt cont-after-WSOpt
                     pos-after-quoted rest-after-quoted
                     [] pos-after-WSOpt rest-after-WSOpt
                     (manyHelper-satisfy-exhaust-many isHSpace
                        pos-after-quoted [] rest-after-quoted All.[]
                        (∷-stop refl))

    step-char-semi :
      cont-after-WSOpt [] pos-after-WSOpt rest-after-WSOpt
      ≡ cont-after-semi ';' pos-after-semi rest-after-semi
    step-char-semi =
      bind-just-step (char ';') cont-after-semi
                     pos-after-WSOpt rest-after-WSOpt
                     ';' pos-after-semi rest-after-semi
                     (char-matches ';' pos-after-WSOpt rest-after-semi)

    step-newline :
      cont-after-semi ';' pos-after-semi rest-after-semi
      ≡ cont-after-newline '\n' pos-after-LF rest-after-LF
    step-newline =
      bind-just-step parseNewline cont-after-newline
                     pos-after-semi rest-after-semi
                     '\n' pos-after-LF rest-after-LF
                     (parseNewline-match-LF pos-after-semi suffix)

    step-many-newline :
      cont-after-newline '\n' pos-after-LF rest-after-LF
      ≡ just (mkResult (mkComment target text) pos-after-LF suffix)
    step-many-newline =
      bind-just-step (many parseNewline) cont-after-many-newline
                     pos-after-LF rest-after-LF
                     [] pos-after-LF rest-after-LF
                     (manyHelper-parseNewline-exhaust pos-after-LF suffix
                        (length suffix) nl-stop)

-- ============================================================================
-- Top-level: parseComment-roundtrip
-- ============================================================================
--
-- Five-case dispatch on the comment target.  Each branch has the same
-- top-level shape — `string "CM_" *> parseWS *> dispatch *> tail` — but
-- differs in (a) the input prefix between `parseWS` and the
-- `parseStringLit` step, (b) the dispatch evidence, and (c) the
-- per-target precondition.  Pattern-matching on `(mkComment target
-- text)` at the LHS — rather than `with target` — keeps each branch's
-- `tgt-stop` reduced (`⊤` for CTNetwork/CTMessage; `NameStop _` for the
-- identifier-bearing constructors) and avoids the `with`-aux
-- generalisation that triggered the heap blowup in
-- `buildCANId-rawCanIdℕ`.
--
-- Position fold: each branch carries its own `pos-fold` lemma to
-- reassemble the per-step `advancePosition` chain into the public
-- form `advancePositions pos (emitComment-chars c)`.  Built from
-- `advancePositions-++` `trans`/`sym` chains, never `rewrite`, again
-- to avoid the with-aux pattern.
parseComment-roundtrip :
    ∀ (pos : Position) (c : DBCComment) (suffix : List Char)
  → CommentTargetStop c
  → SuffixStops isNewlineStart suffix
  → parseComment pos (emitComment-chars c ++ₗ suffix)
    ≡ just (mkResult c
             (advancePositions pos (emitComment-chars c))
             suffix)

-- --------------------------------------------------------------------------
-- CTNetwork case — all four parseXTgt sub-alts fail on the leading `'"'`,
-- the outer `<|> pure CTNetwork` fall-through fires.
-- --------------------------------------------------------------------------
parseComment-roundtrip pos (mkComment CTNetwork text) suffix _ nl-stop =
  trans (cong (parseComment pos) input-shape)
    (trans step-string-CM
      (trans step-parseWS
        (trans step-dispatch
          (trans step-tail
            position-fold-step))))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    pos1 : Position
    pos1 = advancePositions pos (toList "CM_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos2 quoted

    pos-after-semi : Position
    pos-after-semi = advancePosition pos-after-quoted ';'

    pos-after-LF : Position
    pos-after-LF = advancePosition pos-after-semi '\n'

    rest1 : List Char
    rest1 = ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix

    rest2 : List Char
    rest2 = quoted ++ₗ ';' ∷ '\n' ∷ suffix

    cont-after-CM : String → Parser DBCComment
    cont-after-CM _ =
      parseWS >>= λ _ →
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-WS : List Char → Parser DBCComment
    cont-after-WS _ =
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-dispatch : CommentTarget → Parser DBCComment
    cont-after-dispatch tgt =
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    -- Reshape: `(toList "CM_ " ++ quoted ++ toList ";\n") ++ suffix`
    -- to `toList "CM_" ++ ' ' ∷ quoted ++ ';' ∷ '\n' ∷ suffix`.  The
    -- `toList "CM_ "` ↔ `toList "CM_" ++ ' ' ∷ []` and `toList ";\n"
    -- ++ suffix` ↔ `';' ∷ '\n' ∷ suffix` reductions are definitional
    -- on closed strings; the proof is just a single `++ₗ-assoc` step.
    input-shape :
      (toList "CM_ " ++ₗ quoted ++ₗ toList ";\n") ++ₗ suffix
      ≡ toList "CM_" ++ₗ rest1
    input-shape =
      cong (λ ys → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ ys)
           (++ₗ-assoc quoted (toList ";\n") suffix)

    rest2-non-hspace : SuffixStops isHSpace rest2
    rest2-non-hspace =
      quoteStringLit-chars-head-isHSpace text (';' ∷ '\n' ∷ suffix)

    step-string-CM :
      parseComment pos (toList "CM_" ++ₗ rest1)
      ≡ cont-after-CM "CM_" pos1 rest1
    step-string-CM =
      bind-just-step (string "CM_") cont-after-CM
                     pos (toList "CM_" ++ₗ rest1)
                     "CM_" pos1 rest1
                     (string-success pos "CM_" rest1)

    step-parseWS :
      cont-after-CM "CM_" pos1 rest1
      ≡ cont-after-WS (' ' ∷ []) pos2 rest2
    step-parseWS =
      bind-just-step parseWS cont-after-WS
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 rest2-non-hspace)

    -- All four parseXTgt sub-alts fail on `'"'`-headed input.  Subst
    -- transports the on-`'"'`-headed lemma across the
    -- `quoteStringLit-chars-shape` rewrite — the head of `quoted`
    -- decomposes to `'"'` followed by `escape-body-chars (toList text)
    -- ++ '"' ∷ []`, so the post-quote tail of `rest2` matches the
    -- generic-shape `'"' ∷ X` form.
    parseCommentTarget-fails-on-quote :
      parseCommentTarget pos2 rest2 ≡ nothing
    parseCommentTarget-fails-on-quote =
      subst (λ q → parseCommentTarget pos2 (q ++ₗ ';' ∷ '\n' ∷ suffix) ≡ nothing)
            (sym (quoteStringLit-chars-shape text))
            (parseCommentTarget-fails-on-quote-prefix pos2
               (escape-body-chars (toList text) ++ₗ '"' ∷ ';' ∷ '\n' ∷ suffix))

    dispatch-CTNetwork :
      (parseCommentTarget <|> pure CTNetwork) pos2 rest2
      ≡ just (mkResult CTNetwork pos2 rest2)
    dispatch-CTNetwork =
      trans (alt-right-nothing parseCommentTarget (pure CTNetwork)
              pos2 rest2 parseCommentTarget-fails-on-quote)
        refl

    step-dispatch :
      cont-after-WS (' ' ∷ []) pos2 rest2
      ≡ cont-after-dispatch CTNetwork pos2 rest2
    step-dispatch =
      bind-just-step (parseCommentTarget <|> pure CTNetwork) cont-after-dispatch
                     pos2 rest2
                     CTNetwork pos2 rest2
                     dispatch-CTNetwork

    step-tail :
      cont-after-dispatch CTNetwork pos2 rest2
      ≡ just (mkResult (mkComment CTNetwork text) pos-after-LF suffix)
    step-tail =
      parseStringLit-to-pure-roundtrip pos2 CTNetwork text suffix nl-stop

    -- Position fold: collapse the per-step advancePosition chain back
    -- into the public `advancePositions pos emit` form via four
    -- definitional bridges + two `sym (advancePositions-++)` steps.
    -- The `sym` direction is needed because `advancePositions-++`'s
    -- type is `advancePositions pos (xs ++ ys) ≡ advancePositions
    -- (advancePositions pos xs) ys` — distributing append outward,
    -- not collecting it.
    pos-fold : pos-after-LF ≡ advancePositions pos
                                (emitComment-chars (mkComment CTNetwork text))
    pos-fold = trans step1 (trans step2 step3)
      where
        step1 : pos-after-LF
              ≡ advancePositions (advancePositions pos2 quoted)
                                 (';' ∷ '\n' ∷ [])
        step1 = refl

        step2 : advancePositions (advancePositions pos2 quoted)
                                 (';' ∷ '\n' ∷ [])
              ≡ advancePositions pos2 (quoted ++ₗ ';' ∷ '\n' ∷ [])
        step2 = sym (advancePositions-++ pos2 quoted (';' ∷ '\n' ∷ []))

        step3 : advancePositions pos2 (quoted ++ₗ ';' ∷ '\n' ∷ [])
              ≡ advancePositions pos
                  (emitComment-chars (mkComment CTNetwork text))
        step3 = sym (advancePositions-++ pos (toList "CM_ ")
                                         (quoted ++ₗ ';' ∷ '\n' ∷ []))

    position-fold-step :
      just (mkResult (mkComment CTNetwork text) pos-after-LF suffix)
      ≡ just (mkResult (mkComment CTNetwork text)
               (advancePositions pos
                  (emitComment-chars (mkComment CTNetwork text)))
               suffix)
    position-fold-step =
      cong (λ p → just (mkResult (mkComment CTNetwork text) p suffix)) pos-fold

-- --------------------------------------------------------------------------
-- CTNode case — parseBUTgt fires (input starts with `"BU_"`); 3 nested
-- alt-left-justs lift through the four-fold parseCommentTarget chain,
-- then alt-left-just wraps with `pure CTNetwork`.
-- --------------------------------------------------------------------------
parseComment-roundtrip pos (mkComment (CTNode n) text) suffix name-stop nl-stop =
  trans (cong (parseComment pos) input-shape)
    (trans step-string-CM
      (trans step-parseWS
        (trans step-dispatch
          (trans step-tail
            position-fold-step))))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    nm : List Char
    nm = toList (Identifier.name n)

    pos1 : Position
    pos1 = advancePositions pos (toList "CM_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    -- Position after parseBUTgt: pos2 + "BU_" + ' ' + name + ' '.
    pos-after-target : Position
    pos-after-target =
      advancePosition (advancePositions
        (advancePosition (advancePositions pos2 (toList "BU_")) ' ') nm) ' '

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos-after-target quoted

    pos-after-LF : Position
    pos-after-LF =
      advancePosition (advancePosition pos-after-quoted ';') '\n'

    -- Input slices.
    rest1 : List Char
    rest1 = ' ' ∷ toList "BU_" ++ₗ ' ' ∷ nm ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    rest2 : List Char
    rest2 = toList "BU_" ++ₗ ' ' ∷ nm ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    -- After parseBUTgt: rest = quoted ++ ';' ∷ '\n' ∷ suffix.
    rest-after-target : List Char
    rest-after-target = quoted ++ₗ ';' ∷ '\n' ∷ suffix

    cont-after-CM : String → Parser DBCComment
    cont-after-CM _ =
      parseWS >>= λ _ →
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-WS : List Char → Parser DBCComment
    cont-after-WS _ =
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-dispatch : CommentTarget → Parser DBCComment
    cont-after-dispatch tgt =
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    -- Reshape: emit ++ suffix → toList "CM_" ++ rest1.
    -- emit = toList "CM_ BU_ " ++ name ++ ' ' ∷ quoted ++ toList ";\n".
    -- All the closed-string toList reductions and the trailing ++-assoc
    -- collapse the form into the form the bind chain expects.
    input-shape :
      (toList "CM_ BU_ " ++ₗ nm ++ₗ ' ' ∷ quoted ++ₗ toList ";\n") ++ₗ suffix
      ≡ toList "CM_" ++ₗ rest1
    input-shape =
      cong (λ ys → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ ys)
           (trans (++ₗ-assoc nm (' ' ∷ quoted ++ₗ toList ";\n") suffix)
                  (cong (nm ++ₗ_)
                        (cong (' ' ∷_)
                              (++ₗ-assoc quoted (toList ";\n") suffix))))

    rest2-non-hspace : SuffixStops isHSpace rest2
    rest2-non-hspace = ∷-stop refl

    step-string-CM :
      parseComment pos (toList "CM_" ++ₗ rest1)
      ≡ cont-after-CM "CM_" pos1 rest1
    step-string-CM =
      bind-just-step (string "CM_") cont-after-CM
                     pos (toList "CM_" ++ₗ rest1)
                     "CM_" pos1 rest1
                     (string-success pos "CM_" rest1)

    step-parseWS :
      cont-after-CM "CM_" pos1 rest1
      ≡ cont-after-WS (' ' ∷ []) pos2 rest2
    step-parseWS =
      bind-just-step parseWS cont-after-WS
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 rest2-non-hspace)

    -- Dispatch: parseBUTgt succeeds.  3 nested alt-left-justs lift it
    -- through ((BU <|> BO) <|> SG) <|> EV, then a 4th wraps with
    -- `pure CTNetwork`.
    parseBUTgt-rest-stop : SuffixStops isHSpace rest-after-target
    parseBUTgt-rest-stop =
      quoteStringLit-chars-head-isHSpace text (';' ∷ '\n' ∷ suffix)

    parseBUTgt-eq :
      parseBUTgt pos2 rest2
      ≡ just (mkResult (CTNode n) pos-after-target rest-after-target)
    parseBUTgt-eq =
      parseBUTgt-roundtrip pos2 n rest-after-target name-stop
        parseBUTgt-rest-stop

    parseCommentTarget-CTNode :
      parseCommentTarget pos2 rest2
      ≡ just (mkResult (CTNode n) pos-after-target rest-after-target)
    parseCommentTarget-CTNode =
      alt-left-just (parseBUTgt <|> parseBOTgt <|> parseSGTgt) parseEVTgt
        pos2 rest2 _
        (alt-left-just (parseBUTgt <|> parseBOTgt) parseSGTgt
          pos2 rest2 _
          (alt-left-just parseBUTgt parseBOTgt
            pos2 rest2 _
            parseBUTgt-eq))

    dispatch-CTNode :
      (parseCommentTarget <|> pure CTNetwork) pos2 rest2
      ≡ just (mkResult (CTNode n) pos-after-target rest-after-target)
    dispatch-CTNode =
      alt-left-just parseCommentTarget (pure CTNetwork)
        pos2 rest2 _
        parseCommentTarget-CTNode

    step-dispatch :
      cont-after-WS (' ' ∷ []) pos2 rest2
      ≡ cont-after-dispatch (CTNode n) pos-after-target rest-after-target
    step-dispatch =
      bind-just-step (parseCommentTarget <|> pure CTNetwork) cont-after-dispatch
                     pos2 rest2
                     (CTNode n) pos-after-target rest-after-target
                     dispatch-CTNode

    step-tail :
      cont-after-dispatch (CTNode n) pos-after-target rest-after-target
      ≡ just (mkResult (mkComment (CTNode n) text) pos-after-LF suffix)
    step-tail =
      parseStringLit-to-pure-roundtrip pos-after-target (CTNode n) text suffix nl-stop

    -- Position fold: pos-after-LF → advancePositions pos emit.  Bridge
    -- through the parseBUTgt-internal chain via the per-target helper
    -- `parseBUTgt-pos-eq`, then the outer `sym advancePositions-++`
    -- collapses CM_+space + BU_+space+name+space + quoted + ;\n.
    parseBUTgt-pos-eq :
      pos-after-target
      ≡ advancePositions pos2 (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ [])
    parseBUTgt-pos-eq =
      trans bu-step1 (trans bu-step2 bu-step3)
      where
        bu-step1 : pos-after-target
                 ≡ advancePositions
                     (advancePositions (advancePositions pos2 (toList "BU_ ")) nm)
                     (' ' ∷ [])
        bu-step1 = refl

        bu-step2 :
            advancePositions
              (advancePositions (advancePositions pos2 (toList "BU_ ")) nm)
              (' ' ∷ [])
          ≡ advancePositions (advancePositions pos2 (toList "BU_ "))
              (nm ++ₗ ' ' ∷ [])
        bu-step2 = sym (advancePositions-++ (advancePositions pos2 (toList "BU_ "))
                                            nm (' ' ∷ []))

        bu-step3 :
            advancePositions (advancePositions pos2 (toList "BU_ "))
              (nm ++ₗ ' ' ∷ [])
          ≡ advancePositions pos2 (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ [])
        bu-step3 = sym (advancePositions-++ pos2 (toList "BU_ ")
                                            (nm ++ₗ ' ' ∷ []))

    pos-fold : pos-after-LF ≡ advancePositions pos
                                (emitComment-chars (mkComment (CTNode n) text))
    pos-fold =
      trans step1 (trans step2 (trans step3 (trans step4
        (trans step5 step6))))
      where
        outer-tail : List Char
        outer-tail = quoted ++ₗ ';' ∷ '\n' ∷ []

        step1 : pos-after-LF
              ≡ advancePositions (advancePositions pos-after-target quoted)
                                 (';' ∷ '\n' ∷ [])
        step1 = refl

        step2 :
            advancePositions (advancePositions pos-after-target quoted)
                             (';' ∷ '\n' ∷ [])
          ≡ advancePositions pos-after-target outer-tail
        step2 = sym (advancePositions-++ pos-after-target quoted (';' ∷ '\n' ∷ []))

        step3 : advancePositions pos-after-target outer-tail
              ≡ advancePositions
                  (advancePositions pos2 (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []))
                  outer-tail
        step3 = cong (λ p → advancePositions p outer-tail) parseBUTgt-pos-eq

        step4 :
            advancePositions
              (advancePositions pos2 (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []))
              outer-tail
          ≡ advancePositions pos2
              ((toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail)
        step4 = sym (advancePositions-++ pos2
                       (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []) outer-tail)

        -- Reshape `(toList "BU_ " ++ nm ++ ' ' ∷ []) ++ outer-tail`
        -- into `toList "BU_ " ++ nm ++ ' ' ∷ outer-tail` via two ++ₗ-assoc
        -- applications.  Needed because `emitComment-chars (CTNode n)` emits
        -- `nm ++ (' ' ∷ outer-tail)`, not `(nm ++ ' ' ∷ []) ++ outer-tail`.
        chunk-reshape :
            (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail
          ≡ toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail
        chunk-reshape =
          trans (++ₗ-assoc (toList "BU_ ") (nm ++ₗ ' ' ∷ []) outer-tail)
                (cong (toList "BU_ " ++ₗ_)
                      (++ₗ-assoc nm (' ' ∷ []) outer-tail))

        step5 :
            advancePositions pos2
              ((toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail)
          ≡ advancePositions pos2
              (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail)
        step5 = cong (advancePositions pos2) chunk-reshape

        step6 :
            advancePositions pos2
              (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail)
          ≡ advancePositions pos
              (emitComment-chars (mkComment (CTNode n) text))
        step6 = sym (advancePositions-++ pos (toList "CM_ ")
                       (toList "BU_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail))

    position-fold-step :
      just (mkResult (mkComment (CTNode n) text) pos-after-LF suffix)
      ≡ just (mkResult (mkComment (CTNode n) text)
               (advancePositions pos
                  (emitComment-chars (mkComment (CTNode n) text)))
               suffix)
    position-fold-step =
      cong (λ p → just (mkResult (mkComment (CTNode n) text) p suffix)) pos-fold

-- --------------------------------------------------------------------------
-- CTMessage case — parseBUTgt fails on `'B' ∷ 'O' ∷ ...`; parseBOTgt
-- succeeds.  Outer alt: alt-right-nothing for BU, alt-left-just for BO
-- through the inner three-fold alt.
-- --------------------------------------------------------------------------
parseComment-roundtrip pos (mkComment (CTMessage cid) text) suffix _ nl-stop =
  trans (cong (parseComment pos) input-shape)
    (trans step-string-CM
      (trans step-parseWS
        (trans step-dispatch
          (trans step-tail
            position-fold-step))))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)

    pos1 : Position
    pos1 = advancePositions pos (toList "CM_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    -- Position after parseBOTgt: pos2 + "BO_" + ' ' + digits + ' '.
    pos-after-target : Position
    pos-after-target =
      advancePosition (advancePositions
        (advancePosition (advancePositions pos2 (toList "BO_")) ' ') digits) ' '

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos-after-target quoted

    pos-after-LF : Position
    pos-after-LF =
      advancePosition (advancePosition pos-after-quoted ';') '\n'

    rest1 : List Char
    rest1 = ' ' ∷ toList "BO_" ++ₗ ' ' ∷ digits ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    rest2 : List Char
    rest2 = toList "BO_" ++ₗ ' ' ∷ digits ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    rest-after-target : List Char
    rest-after-target = quoted ++ₗ ';' ∷ '\n' ∷ suffix

    cont-after-CM : String → Parser DBCComment
    cont-after-CM _ =
      parseWS >>= λ _ →
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-WS : List Char → Parser DBCComment
    cont-after-WS _ =
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-dispatch : CommentTarget → Parser DBCComment
    cont-after-dispatch tgt =
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    -- Reshape: emit ++ suffix → toList "CM_" ++ rest1.
    -- emit = toList "CM_ BO_ " ++ digits ++ ' ' ∷ quoted ++ toList ";\n".
    input-shape :
      (toList "CM_ BO_ " ++ₗ digits ++ₗ ' ' ∷ quoted ++ₗ toList ";\n") ++ₗ suffix
      ≡ toList "CM_" ++ₗ rest1
    input-shape =
      cong (λ ys → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ ys)
           (trans (++ₗ-assoc digits (' ' ∷ quoted ++ₗ toList ";\n") suffix)
                  (cong (digits ++ₗ_)
                        (cong (' ' ∷_)
                              (++ₗ-assoc quoted (toList ";\n") suffix))))

    rest2-non-hspace : SuffixStops isHSpace rest2
    rest2-non-hspace = ∷-stop refl

    step-string-CM :
      parseComment pos (toList "CM_" ++ₗ rest1)
      ≡ cont-after-CM "CM_" pos1 rest1
    step-string-CM =
      bind-just-step (string "CM_") cont-after-CM
                     pos (toList "CM_" ++ₗ rest1)
                     "CM_" pos1 rest1
                     (string-success pos "CM_" rest1)

    step-parseWS :
      cont-after-CM "CM_" pos1 rest1
      ≡ cont-after-WS (' ' ∷ []) pos2 rest2
    step-parseWS =
      bind-just-step parseWS cont-after-WS
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 rest2-non-hspace)

    -- Dispatch: parseBOTgt succeeds.  Outer alt: BU fails, then 2 nested
    -- alt-left-justs lift parseBOTgt-eq through (BO <|> SG) <|> EV, then
    -- a final alt-left-just wraps with `pure CTNetwork`.
    parseBOTgt-rest-stop : SuffixStops isHSpace rest-after-target
    parseBOTgt-rest-stop =
      quoteStringLit-chars-head-isHSpace text (';' ∷ '\n' ∷ suffix)

    parseBOTgt-eq :
      parseBOTgt pos2 rest2
      ≡ just (mkResult (CTMessage cid) pos-after-target rest-after-target)
    parseBOTgt-eq =
      parseBOTgt-roundtrip pos2 cid rest-after-target parseBOTgt-rest-stop

    parseBUTgt-fails : parseBUTgt pos2 rest2 ≡ nothing
    parseBUTgt-fails =
      parseBUTgt-fail-on-BO pos2 '_'
        (' ' ∷ digits ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix)

    -- `_<|>_` is left-associative (infixl 3), so parseCommentTarget
    -- parses as `((parseBUTgt <|> parseBOTgt) <|> parseSGTgt) <|> parseEVTgt`.
    -- Build BO success bottom-up: BU fails / BO succeeds → (BU <|> BO);
    -- lift through alt-left-just twice for the outer SG / EV branches.
    bu-or-bo-eq :
      (parseBUTgt <|> parseBOTgt) pos2 rest2
      ≡ just (mkResult (CTMessage cid) pos-after-target rest-after-target)
    bu-or-bo-eq =
      trans
        (alt-right-nothing parseBUTgt parseBOTgt pos2 rest2 parseBUTgt-fails)
        parseBOTgt-eq

    parseCommentTarget-CTMessage :
      parseCommentTarget pos2 rest2
      ≡ just (mkResult (CTMessage cid) pos-after-target rest-after-target)
    parseCommentTarget-CTMessage =
      alt-left-just (parseBUTgt <|> parseBOTgt <|> parseSGTgt) parseEVTgt
        pos2 rest2 _
        (alt-left-just (parseBUTgt <|> parseBOTgt) parseSGTgt
          pos2 rest2 _
          bu-or-bo-eq)

    dispatch-CTMessage :
      (parseCommentTarget <|> pure CTNetwork) pos2 rest2
      ≡ just (mkResult (CTMessage cid) pos-after-target rest-after-target)
    dispatch-CTMessage =
      alt-left-just parseCommentTarget (pure CTNetwork)
        pos2 rest2 _
        parseCommentTarget-CTMessage

    step-dispatch :
      cont-after-WS (' ' ∷ []) pos2 rest2
      ≡ cont-after-dispatch (CTMessage cid) pos-after-target rest-after-target
    step-dispatch =
      bind-just-step (parseCommentTarget <|> pure CTNetwork) cont-after-dispatch
                     pos2 rest2
                     (CTMessage cid) pos-after-target rest-after-target
                     dispatch-CTMessage

    step-tail :
      cont-after-dispatch (CTMessage cid) pos-after-target rest-after-target
      ≡ just (mkResult (mkComment (CTMessage cid) text) pos-after-LF suffix)
    step-tail =
      parseStringLit-to-pure-roundtrip pos-after-target (CTMessage cid)
        text suffix nl-stop

    -- Position fold mirrors CTNode but with `digits` in place of `nm` and
    -- `BO_` in place of `BU_`.  Same chunk-reshape: collapse
    -- `(toList "BO_ " ++ digits ++ ' ' ∷ []) ++ outer-tail` into
    -- `toList "BO_ " ++ digits ++ ' ' ∷ outer-tail` via two ++ₗ-assoc.
    parseBOTgt-pos-eq :
      pos-after-target
      ≡ advancePositions pos2 (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ [])
    parseBOTgt-pos-eq =
      trans bo-step1 (trans bo-step2 bo-step3)
      where
        bo-step1 : pos-after-target
                 ≡ advancePositions
                     (advancePositions (advancePositions pos2 (toList "BO_ ")) digits)
                     (' ' ∷ [])
        bo-step1 = refl

        bo-step2 :
            advancePositions
              (advancePositions (advancePositions pos2 (toList "BO_ ")) digits)
              (' ' ∷ [])
          ≡ advancePositions (advancePositions pos2 (toList "BO_ "))
              (digits ++ₗ ' ' ∷ [])
        bo-step2 = sym (advancePositions-++ (advancePositions pos2 (toList "BO_ "))
                                            digits (' ' ∷ []))

        bo-step3 :
            advancePositions (advancePositions pos2 (toList "BO_ "))
              (digits ++ₗ ' ' ∷ [])
          ≡ advancePositions pos2 (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ [])
        bo-step3 = sym (advancePositions-++ pos2 (toList "BO_ ")
                                            (digits ++ₗ ' ' ∷ []))

    pos-fold : pos-after-LF ≡ advancePositions pos
                                (emitComment-chars (mkComment (CTMessage cid) text))
    pos-fold =
      trans step1 (trans step2 (trans step3 (trans step4
        (trans step5 step6))))
      where
        outer-tail : List Char
        outer-tail = quoted ++ₗ ';' ∷ '\n' ∷ []

        step1 : pos-after-LF
              ≡ advancePositions (advancePositions pos-after-target quoted)
                                 (';' ∷ '\n' ∷ [])
        step1 = refl

        step2 :
            advancePositions (advancePositions pos-after-target quoted)
                             (';' ∷ '\n' ∷ [])
          ≡ advancePositions pos-after-target outer-tail
        step2 = sym (advancePositions-++ pos-after-target quoted (';' ∷ '\n' ∷ []))

        step3 : advancePositions pos-after-target outer-tail
              ≡ advancePositions
                  (advancePositions pos2 (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []))
                  outer-tail
        step3 = cong (λ p → advancePositions p outer-tail) parseBOTgt-pos-eq

        step4 :
            advancePositions
              (advancePositions pos2 (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []))
              outer-tail
          ≡ advancePositions pos2
              ((toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []) ++ₗ outer-tail)
        step4 = sym (advancePositions-++ pos2
                       (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []) outer-tail)

        chunk-reshape :
            (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []) ++ₗ outer-tail
          ≡ toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ outer-tail
        chunk-reshape =
          trans (++ₗ-assoc (toList "BO_ ") (digits ++ₗ ' ' ∷ []) outer-tail)
                (cong (toList "BO_ " ++ₗ_)
                      (++ₗ-assoc digits (' ' ∷ []) outer-tail))

        step5 :
            advancePositions pos2
              ((toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ []) ++ₗ outer-tail)
          ≡ advancePositions pos2
              (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ outer-tail)
        step5 = cong (advancePositions pos2) chunk-reshape

        step6 :
            advancePositions pos2
              (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ outer-tail)
          ≡ advancePositions pos
              (emitComment-chars (mkComment (CTMessage cid) text))
        step6 = sym (advancePositions-++ pos (toList "CM_ ")
                       (toList "BO_ " ++ₗ digits ++ₗ ' ' ∷ outer-tail))

    position-fold-step :
      just (mkResult (mkComment (CTMessage cid) text) pos-after-LF suffix)
      ≡ just (mkResult (mkComment (CTMessage cid) text)
               (advancePositions pos
                  (emitComment-chars (mkComment (CTMessage cid) text)))
               suffix)
    position-fold-step =
      cong (λ p → just (mkResult (mkComment (CTMessage cid) text) p suffix)) pos-fold

-- --------------------------------------------------------------------------
-- CTSignal case — parseBUTgt fails on `'S' ∷ ...`, parseBOTgt fails on
-- `'S' ∷ ...`, parseSGTgt succeeds.  Outer alt: alt-fail-fail (BU,BO),
-- alt-right-nothing then parseSGTgt-eq for SG, alt-left-just for EV.
-- --------------------------------------------------------------------------
parseComment-roundtrip pos (mkComment (CTSignal cid s) text) suffix
                       name-stop nl-stop =
  trans (cong (parseComment pos) input-shape)
    (trans step-string-CM
      (trans step-parseWS
        (trans step-dispatch
          (trans step-tail
            position-fold-step))))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    digits : List Char
    digits = showℕ-dec-chars (rawCanIdℕ cid)

    name : List Char
    name = toList (Identifier.name s)

    pos1 : Position
    pos1 = advancePositions pos (toList "CM_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    -- Position after parseSGTgt: pos2 + "SG_" + ' ' + digits + ' ' + name + ' '.
    pos-after-target : Position
    pos-after-target =
      advancePosition (advancePositions
        (advancePosition (advancePositions
          (advancePosition (advancePositions pos2 (toList "SG_")) ' ')
          digits) ' ') name) ' '

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos-after-target quoted

    pos-after-LF : Position
    pos-after-LF =
      advancePosition (advancePosition pos-after-quoted ';') '\n'

    rest1 : List Char
    rest1 = ' ' ∷ toList "SG_" ++ₗ ' ' ∷ digits ++ₗ ' ' ∷ name
              ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix

    rest2 : List Char
    rest2 = toList "SG_" ++ₗ ' ' ∷ digits ++ₗ ' ' ∷ name
              ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix

    rest-after-target : List Char
    rest-after-target = quoted ++ₗ ';' ∷ '\n' ∷ suffix

    cont-after-CM : String → Parser DBCComment
    cont-after-CM _ =
      parseWS >>= λ _ →
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-WS : List Char → Parser DBCComment
    cont-after-WS _ =
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-dispatch : CommentTarget → Parser DBCComment
    cont-after-dispatch tgt =
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    -- Reshape: emit ++ suffix → toList "CM_" ++ rest1.
    -- emit = toList "CM_ SG_ " ++ digits ++ ' ' ∷ name ++ ' ' ∷ quoted
    --        ++ toList ";\n".
    input-shape :
      (toList "CM_ SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ quoted
         ++ₗ toList ";\n") ++ₗ suffix
      ≡ toList "CM_" ++ₗ rest1
    input-shape =
      cong (λ ys → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ ys)
           (trans
             (++ₗ-assoc digits
                (' ' ∷ name ++ₗ ' ' ∷ quoted ++ₗ toList ";\n") suffix)
             (cong (digits ++ₗ_)
               (cong (' ' ∷_)
                 (trans
                   (++ₗ-assoc name (' ' ∷ quoted ++ₗ toList ";\n") suffix)
                   (cong (name ++ₗ_)
                     (cong (' ' ∷_)
                       (++ₗ-assoc quoted (toList ";\n") suffix)))))))

    rest2-non-hspace : SuffixStops isHSpace rest2
    rest2-non-hspace = ∷-stop refl

    step-string-CM :
      parseComment pos (toList "CM_" ++ₗ rest1)
      ≡ cont-after-CM "CM_" pos1 rest1
    step-string-CM =
      bind-just-step (string "CM_") cont-after-CM
                     pos (toList "CM_" ++ₗ rest1)
                     "CM_" pos1 rest1
                     (string-success pos "CM_" rest1)

    step-parseWS :
      cont-after-CM "CM_" pos1 rest1
      ≡ cont-after-WS (' ' ∷ []) pos2 rest2
    step-parseWS =
      bind-just-step parseWS cont-after-WS
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 rest2-non-hspace)

    -- Dispatch: parseSGTgt succeeds.  BU/BO fail on 'S' (alt-fail-fail
    -- collapses them).  Then `(BU <|> BO) <|> SG` succeeds via SG
    -- (alt-right-nothing + parseSGTgt-eq).  Outer alt-left-just wraps
    -- the EV branch.
    parseSGTgt-rest-stop : SuffixStops isHSpace rest-after-target
    parseSGTgt-rest-stop =
      quoteStringLit-chars-head-isHSpace text (';' ∷ '\n' ∷ suffix)

    parseSGTgt-eq :
      parseSGTgt pos2 rest2
      ≡ just (mkResult (CTSignal cid s) pos-after-target rest-after-target)
    parseSGTgt-eq =
      parseSGTgt-roundtrip pos2 cid s rest-after-target name-stop
        parseSGTgt-rest-stop

    parseBUTgt-fails : parseBUTgt pos2 rest2 ≡ nothing
    parseBUTgt-fails =
      parseBUTgt-fail-on-S pos2
        ('G' ∷ '_' ∷ ' ' ∷ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ quoted
          ++ₗ ';' ∷ '\n' ∷ suffix)

    parseBOTgt-fails : parseBOTgt pos2 rest2 ≡ nothing
    parseBOTgt-fails =
      parseBOTgt-fail-on-S pos2
        ('G' ∷ '_' ∷ ' ' ∷ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ quoted
          ++ₗ ';' ∷ '\n' ∷ suffix)

    bu-or-bo-fails : (parseBUTgt <|> parseBOTgt) pos2 rest2 ≡ nothing
    bu-or-bo-fails =
      alt-fail-fail parseBUTgt parseBOTgt pos2 rest2
        parseBUTgt-fails parseBOTgt-fails

    bu-or-bo-or-sg-eq :
      ((parseBUTgt <|> parseBOTgt) <|> parseSGTgt) pos2 rest2
      ≡ just (mkResult (CTSignal cid s) pos-after-target rest-after-target)
    bu-or-bo-or-sg-eq =
      trans
        (alt-right-nothing (parseBUTgt <|> parseBOTgt) parseSGTgt
           pos2 rest2 bu-or-bo-fails)
        parseSGTgt-eq

    parseCommentTarget-CTSignal :
      parseCommentTarget pos2 rest2
      ≡ just (mkResult (CTSignal cid s) pos-after-target rest-after-target)
    parseCommentTarget-CTSignal =
      alt-left-just (parseBUTgt <|> parseBOTgt <|> parseSGTgt) parseEVTgt
        pos2 rest2 _
        bu-or-bo-or-sg-eq

    dispatch-CTSignal :
      (parseCommentTarget <|> pure CTNetwork) pos2 rest2
      ≡ just (mkResult (CTSignal cid s) pos-after-target rest-after-target)
    dispatch-CTSignal =
      alt-left-just parseCommentTarget (pure CTNetwork)
        pos2 rest2 _
        parseCommentTarget-CTSignal

    step-dispatch :
      cont-after-WS (' ' ∷ []) pos2 rest2
      ≡ cont-after-dispatch (CTSignal cid s) pos-after-target rest-after-target
    step-dispatch =
      bind-just-step (parseCommentTarget <|> pure CTNetwork) cont-after-dispatch
                     pos2 rest2
                     (CTSignal cid s) pos-after-target rest-after-target
                     dispatch-CTSignal

    step-tail :
      cont-after-dispatch (CTSignal cid s) pos-after-target rest-after-target
      ≡ just (mkResult (mkComment (CTSignal cid s) text) pos-after-LF suffix)
    step-tail =
      parseStringLit-to-pure-roundtrip pos-after-target (CTSignal cid s)
        text suffix nl-stop

    -- Position fold for SG: 5 chunks (vs 3 for BU/BO/EV).  Strategy: lift
    -- A2 ≡ A2' (the post-SG_ space-collapse) through the position-context
    -- via cong, then 3 forward `advancePositions-++` build the target form.
    parseSGTgt-pos-eq :
      pos-after-target
      ≡ advancePositions pos2 (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name
                                  ++ₗ ' ' ∷ [])
    parseSGTgt-pos-eq = trans pos-to-G (sym target-to-G)
      where
        A2' : Position
        A2' = advancePositions pos2 (toList "SG_ ")

        G : Position → Position
        G x = advancePosition (advancePositions
                (advancePosition (advancePositions x digits) ' ') name) ' '

        pos-to-G : pos-after-target ≡ G A2'
        pos-to-G =
          cong G (sym (advancePositions-++ pos2 (toList "SG_") (' ' ∷ [])))

        target-to-G :
            advancePositions pos2 (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name
                                     ++ₗ ' ' ∷ [])
          ≡ G A2'
        target-to-G =
          trans
            (advancePositions-++ pos2 (toList "SG_ ")
              (digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []))
            (trans
              (advancePositions-++ A2' digits (' ' ∷ name ++ₗ ' ' ∷ []))
              (advancePositions-++
                (advancePosition (advancePositions A2' digits) ' ')
                name (' ' ∷ [])))

    pos-fold : pos-after-LF ≡ advancePositions pos
                                (emitComment-chars (mkComment (CTSignal cid s) text))
    pos-fold =
      trans step1 (trans step2 (trans step3 (trans step4
        (trans step5 step6))))
      where
        outer-tail : List Char
        outer-tail = quoted ++ₗ ';' ∷ '\n' ∷ []

        step1 : pos-after-LF
              ≡ advancePositions (advancePositions pos-after-target quoted)
                                 (';' ∷ '\n' ∷ [])
        step1 = refl

        step2 :
            advancePositions (advancePositions pos-after-target quoted)
                             (';' ∷ '\n' ∷ [])
          ≡ advancePositions pos-after-target outer-tail
        step2 = sym (advancePositions-++ pos-after-target quoted (';' ∷ '\n' ∷ []))

        step3 : advancePositions pos-after-target outer-tail
              ≡ advancePositions
                  (advancePositions pos2
                    (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []))
                  outer-tail
        step3 = cong (λ p → advancePositions p outer-tail) parseSGTgt-pos-eq

        step4 :
            advancePositions
              (advancePositions pos2
                (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []))
              outer-tail
          ≡ advancePositions pos2
              ((toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []) ++ₗ outer-tail)
        step4 = sym (advancePositions-++ pos2
                       (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ [])
                       outer-tail)

        -- Reshape `(toList "SG_ " ++ digits ++ ' ' ∷ name ++ ' ' ∷ []) ++ outer-tail`
        -- into `toList "SG_ " ++ digits ++ ' ' ∷ name ++ ' ' ∷ outer-tail`.
        -- 4 ++-assoc applications: peel off "SG_ ", digits, ' ' ∷, name in turn.
        chunk-reshape :
            (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []) ++ₗ outer-tail
          ≡ toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ outer-tail
        chunk-reshape =
          trans
            (++ₗ-assoc (toList "SG_ ")
               (digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []) outer-tail)
            (cong (toList "SG_ " ++ₗ_)
              (trans
                (++ₗ-assoc digits (' ' ∷ name ++ₗ ' ' ∷ []) outer-tail)
                (cong (digits ++ₗ_)
                  (cong (' ' ∷_)
                    (trans
                      (++ₗ-assoc name (' ' ∷ []) outer-tail)
                      refl)))))

        step5 :
            advancePositions pos2
              ((toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ []) ++ₗ outer-tail)
          ≡ advancePositions pos2
              (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ outer-tail)
        step5 = cong (advancePositions pos2) chunk-reshape

        step6 :
            advancePositions pos2
              (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ outer-tail)
          ≡ advancePositions pos
              (emitComment-chars (mkComment (CTSignal cid s) text))
        step6 = sym (advancePositions-++ pos (toList "CM_ ")
                       (toList "SG_ " ++ₗ digits ++ₗ ' ' ∷ name ++ₗ ' ' ∷ outer-tail))

    position-fold-step :
      just (mkResult (mkComment (CTSignal cid s) text) pos-after-LF suffix)
      ≡ just (mkResult (mkComment (CTSignal cid s) text)
               (advancePositions pos
                  (emitComment-chars (mkComment (CTSignal cid s) text)))
               suffix)
    position-fold-step =
      cong (λ p → just (mkResult (mkComment (CTSignal cid s) text) p suffix))
           pos-fold

-- --------------------------------------------------------------------------
-- CTEnvVar case — parseBUTgt/parseBOTgt/parseSGTgt all fail on `'E' ∷ ...`,
-- parseEVTgt succeeds.  Outer alt: alt-fail-fail collapses BU,BO,SG;
-- alt-right-nothing then parseEVTgt-eq for EV; alt-left-just over CTNetwork.
-- --------------------------------------------------------------------------
parseComment-roundtrip pos (mkComment (CTEnvVar ev) text) suffix
                       name-stop nl-stop =
  trans (cong (parseComment pos) input-shape)
    (trans step-string-CM
      (trans step-parseWS
        (trans step-dispatch
          (trans step-tail
            position-fold-step))))
  where
    quoted : List Char
    quoted = quoteStringLit-chars text

    nm : List Char
    nm = toList (Identifier.name ev)

    pos1 : Position
    pos1 = advancePositions pos (toList "CM_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    -- Position after parseEVTgt: pos2 + "EV_" + ' ' + name + ' '.
    pos-after-target : Position
    pos-after-target =
      advancePosition (advancePositions
        (advancePosition (advancePositions pos2 (toList "EV_")) ' ') nm) ' '

    pos-after-quoted : Position
    pos-after-quoted = advancePositions pos-after-target quoted

    pos-after-LF : Position
    pos-after-LF =
      advancePosition (advancePosition pos-after-quoted ';') '\n'

    rest1 : List Char
    rest1 = ' ' ∷ toList "EV_" ++ₗ ' ' ∷ nm ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    rest2 : List Char
    rest2 = toList "EV_" ++ₗ ' ' ∷ nm ++ₗ ' ' ∷ quoted
              ++ₗ ';' ∷ '\n' ∷ suffix

    rest-after-target : List Char
    rest-after-target = quoted ++ₗ ';' ∷ '\n' ∷ suffix

    cont-after-CM : String → Parser DBCComment
    cont-after-CM _ =
      parseWS >>= λ _ →
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-WS : List Char → Parser DBCComment
    cont-after-WS _ =
      (parseCommentTarget <|> pure CTNetwork) >>= λ tgt →
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    cont-after-dispatch : CommentTarget → Parser DBCComment
    cont-after-dispatch tgt =
      parseStringLit >>= λ t →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (mkComment tgt t)

    -- Reshape: emit ++ suffix → toList "CM_" ++ rest1.
    -- emit = toList "CM_ EV_ " ++ name ++ ' ' ∷ quoted ++ toList ";\n".
    input-shape :
      (toList "CM_ EV_ " ++ₗ nm ++ₗ ' ' ∷ quoted ++ₗ toList ";\n") ++ₗ suffix
      ≡ toList "CM_" ++ₗ rest1
    input-shape =
      cong (λ ys → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ ys)
           (trans (++ₗ-assoc nm (' ' ∷ quoted ++ₗ toList ";\n") suffix)
                  (cong (nm ++ₗ_)
                        (cong (' ' ∷_)
                              (++ₗ-assoc quoted (toList ";\n") suffix))))

    rest2-non-hspace : SuffixStops isHSpace rest2
    rest2-non-hspace = ∷-stop refl

    step-string-CM :
      parseComment pos (toList "CM_" ++ₗ rest1)
      ≡ cont-after-CM "CM_" pos1 rest1
    step-string-CM =
      bind-just-step (string "CM_") cont-after-CM
                     pos (toList "CM_" ++ₗ rest1)
                     "CM_" pos1 rest1
                     (string-success pos "CM_" rest1)

    step-parseWS :
      cont-after-CM "CM_" pos1 rest1
      ≡ cont-after-WS (' ' ∷ []) pos2 rest2
    step-parseWS =
      bind-just-step parseWS cont-after-WS
                     pos1 rest1
                     (' ' ∷ []) pos2 rest2
                     (parseWS-one-space pos1 rest2 rest2-non-hspace)

    -- Dispatch: BU/BO/SG fail on 'E' (alt-fail-fail collapses 3-fold);
    -- parseEVTgt succeeds.  alt-right-nothing transitions to EV, which
    -- closes via parseEVTgt-eq.  alt-left-just wraps CTNetwork.
    parseEVTgt-rest-stop : SuffixStops isHSpace rest-after-target
    parseEVTgt-rest-stop =
      quoteStringLit-chars-head-isHSpace text (';' ∷ '\n' ∷ suffix)

    parseEVTgt-eq :
      parseEVTgt pos2 rest2
      ≡ just (mkResult (CTEnvVar ev) pos-after-target rest-after-target)
    parseEVTgt-eq =
      parseEVTgt-roundtrip pos2 ev rest-after-target name-stop
        parseEVTgt-rest-stop

    parseBUTgt-fails : parseBUTgt pos2 rest2 ≡ nothing
    parseBUTgt-fails =
      parseBUTgt-fail-on-E pos2
        ('V' ∷ '_' ∷ ' ' ∷ nm ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix)

    parseBOTgt-fails : parseBOTgt pos2 rest2 ≡ nothing
    parseBOTgt-fails =
      parseBOTgt-fail-on-E pos2
        ('V' ∷ '_' ∷ ' ' ∷ nm ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix)

    parseSGTgt-fails : parseSGTgt pos2 rest2 ≡ nothing
    parseSGTgt-fails =
      parseSGTgt-fail-on-E pos2
        ('V' ∷ '_' ∷ ' ' ∷ nm ++ₗ ' ' ∷ quoted ++ₗ ';' ∷ '\n' ∷ suffix)

    bu-or-bo-fails : (parseBUTgt <|> parseBOTgt) pos2 rest2 ≡ nothing
    bu-or-bo-fails =
      alt-fail-fail parseBUTgt parseBOTgt pos2 rest2
        parseBUTgt-fails parseBOTgt-fails

    bu-or-bo-or-sg-fails :
      ((parseBUTgt <|> parseBOTgt) <|> parseSGTgt) pos2 rest2 ≡ nothing
    bu-or-bo-or-sg-fails =
      alt-fail-fail (parseBUTgt <|> parseBOTgt) parseSGTgt pos2 rest2
        bu-or-bo-fails parseSGTgt-fails

    parseCommentTarget-CTEnvVar :
      parseCommentTarget pos2 rest2
      ≡ just (mkResult (CTEnvVar ev) pos-after-target rest-after-target)
    parseCommentTarget-CTEnvVar =
      trans
        (alt-right-nothing (parseBUTgt <|> parseBOTgt <|> parseSGTgt) parseEVTgt
           pos2 rest2 bu-or-bo-or-sg-fails)
        parseEVTgt-eq

    dispatch-CTEnvVar :
      (parseCommentTarget <|> pure CTNetwork) pos2 rest2
      ≡ just (mkResult (CTEnvVar ev) pos-after-target rest-after-target)
    dispatch-CTEnvVar =
      alt-left-just parseCommentTarget (pure CTNetwork)
        pos2 rest2 _
        parseCommentTarget-CTEnvVar

    step-dispatch :
      cont-after-WS (' ' ∷ []) pos2 rest2
      ≡ cont-after-dispatch (CTEnvVar ev) pos-after-target rest-after-target
    step-dispatch =
      bind-just-step (parseCommentTarget <|> pure CTNetwork) cont-after-dispatch
                     pos2 rest2
                     (CTEnvVar ev) pos-after-target rest-after-target
                     dispatch-CTEnvVar

    step-tail :
      cont-after-dispatch (CTEnvVar ev) pos-after-target rest-after-target
      ≡ just (mkResult (mkComment (CTEnvVar ev) text) pos-after-LF suffix)
    step-tail =
      parseStringLit-to-pure-roundtrip pos-after-target (CTEnvVar ev)
        text suffix nl-stop

    -- Position fold mirrors CTNode (same chunk shape: keyword + name + ' ').
    parseEVTgt-pos-eq :
      pos-after-target
      ≡ advancePositions pos2 (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ [])
    parseEVTgt-pos-eq =
      trans ev-step1 (trans ev-step2 ev-step3)
      where
        ev-step1 : pos-after-target
                 ≡ advancePositions
                     (advancePositions (advancePositions pos2 (toList "EV_ ")) nm)
                     (' ' ∷ [])
        ev-step1 = refl

        ev-step2 :
            advancePositions
              (advancePositions (advancePositions pos2 (toList "EV_ ")) nm)
              (' ' ∷ [])
          ≡ advancePositions (advancePositions pos2 (toList "EV_ "))
              (nm ++ₗ ' ' ∷ [])
        ev-step2 = sym (advancePositions-++ (advancePositions pos2 (toList "EV_ "))
                                            nm (' ' ∷ []))

        ev-step3 :
            advancePositions (advancePositions pos2 (toList "EV_ "))
              (nm ++ₗ ' ' ∷ [])
          ≡ advancePositions pos2 (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ [])
        ev-step3 = sym (advancePositions-++ pos2 (toList "EV_ ")
                                            (nm ++ₗ ' ' ∷ []))

    pos-fold : pos-after-LF ≡ advancePositions pos
                                (emitComment-chars (mkComment (CTEnvVar ev) text))
    pos-fold =
      trans step1 (trans step2 (trans step3 (trans step4
        (trans step5 step6))))
      where
        outer-tail : List Char
        outer-tail = quoted ++ₗ ';' ∷ '\n' ∷ []

        step1 : pos-after-LF
              ≡ advancePositions (advancePositions pos-after-target quoted)
                                 (';' ∷ '\n' ∷ [])
        step1 = refl

        step2 :
            advancePositions (advancePositions pos-after-target quoted)
                             (';' ∷ '\n' ∷ [])
          ≡ advancePositions pos-after-target outer-tail
        step2 = sym (advancePositions-++ pos-after-target quoted (';' ∷ '\n' ∷ []))

        step3 : advancePositions pos-after-target outer-tail
              ≡ advancePositions
                  (advancePositions pos2 (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []))
                  outer-tail
        step3 = cong (λ p → advancePositions p outer-tail) parseEVTgt-pos-eq

        step4 :
            advancePositions
              (advancePositions pos2 (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []))
              outer-tail
          ≡ advancePositions pos2
              ((toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail)
        step4 = sym (advancePositions-++ pos2
                       (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []) outer-tail)

        chunk-reshape :
            (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail
          ≡ toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail
        chunk-reshape =
          trans (++ₗ-assoc (toList "EV_ ") (nm ++ₗ ' ' ∷ []) outer-tail)
                (cong (toList "EV_ " ++ₗ_)
                      (++ₗ-assoc nm (' ' ∷ []) outer-tail))

        step5 :
            advancePositions pos2
              ((toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ []) ++ₗ outer-tail)
          ≡ advancePositions pos2
              (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail)
        step5 = cong (advancePositions pos2) chunk-reshape

        step6 :
            advancePositions pos2
              (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail)
          ≡ advancePositions pos
              (emitComment-chars (mkComment (CTEnvVar ev) text))
        step6 = sym (advancePositions-++ pos (toList "CM_ ")
                       (toList "EV_ " ++ₗ nm ++ₗ ' ' ∷ outer-tail))

    position-fold-step :
      just (mkResult (mkComment (CTEnvVar ev) text) pos-after-LF suffix)
      ≡ just (mkResult (mkComment (CTEnvVar ev) text)
               (advancePositions pos
                  (emitComment-chars (mkComment (CTEnvVar ev) text)))
               suffix)
    position-fold-step =
      cong (λ p → just (mkResult (mkComment (CTEnvVar ev) text) p suffix))
           pos-fold
