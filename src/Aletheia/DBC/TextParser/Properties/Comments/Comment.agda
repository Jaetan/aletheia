{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — slim `parseComment-roundtrip` derived from the
-- universal Format DSL roundtrip.
--
-- Pre-3d.5.d (3b): hand-written 2,533-line case-by-case proof with 5-way
-- `CommentTarget` dispatch (CTNetwork / CTNode / CTMessage / CTSignal /
-- CTEnvVar) through 4-deep `<|>`-chain composition + per-target bind
-- chains.  CM_ was the heaviest single Layer-3 construct.
--
-- Post-3d.5.d: `parseComment = parse commentFmt >>= many parseNewline >>=
-- buildCommentP` (in `TextParser.Comments`), and the roundtrip reduces to:
--
--   1. A bridge `emit-commentFmt-eq-emitComment-chars` proving DSL emit
--      on `(rawTargetOf target , text , tt)` equals existing
--      `emitComment-chars c`.  Case-splits on `DBCComment.target c`
--      (5 cases) — each closes by `refl` after definitional reduction
--      of the format chain.
--   2. The universal `parseComment-format-roundtrip` (from
--      `Format.Comments`).
--   3. The trailing `many parseNewline` consuming zero from the user's
--      `suffix` (via `manyHelper-parseNewline-exhaust` + the existing
--      `SuffixStops isNewlineStart suffix` precondition).
--   4. `buildCommentP` succeeds: pure cases reduce by `refl`; CAN-ID
--      cases (`CTMessage` / `CTSignal`) discharge via the universal
--      `buildCANId-rawCanIdℕ : ∀ cid → buildCANId (rawCanIdℕ cid) ≡
--      just cid` lemma.
--
-- The `CommentTargetStop` precondition migrates upstream to
-- `Format.Comments`; this module re-exports it for source compatibility
-- with the section facade `Properties/Comments.agda`.
module Aletheia.DBC.TextParser.Properties.Comments.Comment where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; foldr; length) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using
  (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _<ᵇ_; _+_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using
  (<-trans; ≤ᵇ⇒≤; ≤⇒≤ᵇ; <ᵇ⇒<; <⇒≱; m≤n+m; m+n∸n≡m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Topology.Foundations
  using (buildCANId; extFlagBit)
open import Aletheia.DBC.TextParser.Comments using
  (parseComment; buildCommentP)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Constants using
  (standard-can-id-max; extended-can-id-max)
open import Aletheia.DBC.TextFormatter.Comments using (emitComment-chars)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.Types using
  ( CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar
  ; DBCComment; mkComment)

open import Aletheia.Prelude using (ifᵀ_then_else_; ifᵀ-witness)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; ∷-stop)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using (Format; emit; parse)
open import Aletheia.DBC.TextParser.Format.Comments as FmtCM using
  (commentFmt; rawTargetOf; RawCommentTarget;
   RawCTNet; RawCTNode; RawCTMsg; RawCTSig; RawCTEnv;
   parseComment-format-roundtrip)

-- ============================================================================
-- RE-EXPORT — `NameStop` / `CommentTargetStop` migrated to `Format.Comments`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.Comments public
  using (NameStop; CommentTargetStop)

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

  -- standard-can-id-max < extFlagBit — closed-ℕ comparison; `<ᵇ` is a
  -- builtin so the bool-valued comparison reduces in O(1).
  standard-max<extFlagBit : standard-can-id-max < extFlagBit
  standard-max<extFlagBit = <ᵇ⇒< standard-can-id-max extFlagBit tt

  -- `<ᵇ⇒<` accepting irrelevant `T (m <ᵇ n)` — needed because R18 cluster
  -- 17 made `CANId` proof fields `.(…)`-irrelevant, so pattern-matched
  -- `Standard n pf` binds `pf` irrelevantly and stdlib `<ᵇ⇒<` requires
  -- relevant input.  Materializes a relevant `T b` via case split on the
  -- Bool, then defers to stdlib `<ᵇ⇒<`.
  T-materialize : (b : Bool) → .(T b) → T b
  T-materialize true  _  = tt
  T-materialize false ()

  <ᵇ⇒<-irr : ∀ m n → .(T (m <ᵇ n)) → m < n
  <ᵇ⇒<-irr m n pf = <ᵇ⇒< m n (T-materialize (m <ᵇ n) pf)

-- ============================================================================
-- buildCANId roundtrip — `buildCANId (rawCanIdℕ cid) ≡ just cid`
-- ============================================================================

-- Two cases:
--   * Standard n pf: rawCanIdℕ = n; outer ifᵀ on `extFlagBit ≤ᵇ n` is
--     false (n < standard-can-id-max < extFlagBit); inner ifᵀ on
--     `n <ᵇ standard-can-id-max` is true via `pf` — `ifᵀ-witness pf`
--     delivers the result with the original `pf`.
--   * Extended n pf: rawCanIdℕ = n + extFlagBit; outer ifᵀ is true
--     (extFlagBit ≤ n + extFlagBit); subtraction
--     `(n + extFlagBit) ∸ extFlagBit ≡ n` rewrites the inner ifᵀ's
--     domain to `n <ᵇ extended-can-id-max`, and `ifᵀ-witness pf` lands.
--
-- The Extended clause uses pointwise `subst` (not `rewrite`) per the
-- 3d.3b heap-blowup root cause: `rewrite n+ext∸ext≡n` over a goal
-- containing nested `ifᵀ`s produces a `with`-aux that exhausted -M48G
-- in the original CM_ proof.  See AGENTS.md G-A2.
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
    n<extFlagBit = <-trans (<ᵇ⇒<-irr n standard-can-id-max pf) standard-max<extFlagBit
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
-- BRIDGE: DSL emit ≡ existing emitComment-chars
-- ============================================================================

-- DSL emit pairs in left-associated form: every `withWSAfter ident` slot
-- yields `... ++ name ++ ' ' ∷ []`, and the surrounding `pair ... rest`
-- composes that as `(name ++ ' ' ∷ []) ++ rest`.  The formatter
-- (`emitComment-chars`) writes the same content in right-associated form
-- `... ++ name ++ ' ' ∷ rest`.  These differ only by `++ₗ-assoc`; the
-- per-case bridges apply one (or two, for SG_) ++ₗ-assoc steps wrapped in
-- a closed-prefix `cong`.  CTNetwork closes by `refl` (no per-target
-- trailing space — `netFmt = literal []` matches the formatter's
-- bare-`"CM_ "` shape).
private
  -- Single ++ₗ-assoc + cons reduction: `(xs ++ ' ' ∷ []) ++ ys ≡
  -- xs ++ ' ' ∷ ys`.  The RHS of `++ₗ-assoc xs (' ' ∷ []) ys` is
  -- `xs ++ ((' ' ∷ []) ++ ys)`, which Agda reduces to `xs ++ ' ' ∷ ys`
  -- via the `(c ∷ xs) ++ ys = c ∷ (xs ++ ys)` and `[] ++ ys = ys`
  -- equations.
  shift-trail-space : ∀ (xs ys : List Char)
    → (xs ++ₗ ' ' ∷ []) ++ₗ ys ≡ xs ++ₗ ' ' ∷ ys
  shift-trail-space xs ys = ++ₗ-assoc xs (' ' ∷ []) ys

emit-commentFmt-eq-emitComment-chars : ∀ (c : DBCComment)
  → emit commentFmt
       (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
    ≡ emitComment-chars c
-- CTNetwork: emit commentTargetFmt RawCTNet = []; full emit reduces to
-- "CM_ " ++ quoted ++ ";\n" — exactly the formatter's shape.  refl.
emit-commentFmt-eq-emitComment-chars (mkComment CTNetwork _)      = refl
-- CTNode n: shift the `name ++ ' ' ∷ []` trailing space across the
-- following `quoted ++ ";\n"`.
emit-commentFmt-eq-emitComment-chars (mkComment (CTNode n) text) =
  cong (λ x → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ x)
       (shift-trail-space (Identifier.name n)
                          (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ []))
-- CTMessage cid: shift the `showNat (rawCanIdℕ cid) ++ ' ' ∷ []` trailing
-- space across the following `quoted ++ ";\n"`.
emit-commentFmt-eq-emitComment-chars (mkComment (CTMessage cid) text) =
  cong (λ x → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ x)
       (shift-trail-space (showℕ-dec-chars (rawCanIdℕ cid))
                          (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ []))
-- CTSignal cid s: TWO trailing-space shifts — one for the `nat` slot's
-- trailing ' ' (over `' ' ∷ name s ++ ' ' ∷ quoted ++ ";\n"`), one
-- inside for the `name s` slot's trailing ' ' (over `quoted ++ ";\n"`).
emit-commentFmt-eq-emitComment-chars (mkComment (CTSignal cid s) text) =
  cong (λ x → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ x)
       (trans
         (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid))
                    (' ' ∷ (Identifier.name s ++ₗ ' ' ∷ []))
                    (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ []))
         (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
               (cong (' ' ∷_)
                     (shift-trail-space (Identifier.name s)
                                        (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ [])))))
-- CTEnvVar ev: shift the `name ev ++ ' ' ∷ []` trailing space across the
-- following `quoted ++ ";\n"`.
emit-commentFmt-eq-emitComment-chars (mkComment (CTEnvVar ev) text) =
  cong (λ x → 'C' ∷ 'M' ∷ '_' ∷ ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ x)
       (shift-trail-space (Identifier.name ev)
                          (quoteStringLit-chars text ++ₗ ';' ∷ '\n' ∷ []))

-- ============================================================================
-- buildCommentP roundtrip — recover DBCComment from raw target + text
-- ============================================================================

-- 5-way case-split on `DBCComment.target c`.  Pure-target cases (Network
-- / Node / EnvVar) reduce by `refl`.  CAN-ID cases (Message / Signal)
-- use `with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid`
-- followed by `refl` on the matched-just branch (K-elim avoidance: the
-- `| just .cid | refl` pattern unifies the with-result with the
-- intended construction).
buildCommentP-roundtrip : ∀ (c : DBCComment) (pos : Position) (input : List Char)
  → buildCommentP (rawTargetOf (DBCComment.target c)) (DBCComment.text c) pos input
    ≡ just (mkResult c pos input)
buildCommentP-roundtrip (mkComment CTNetwork _)    pos input = refl
buildCommentP-roundtrip (mkComment (CTNode _) _)   pos input = refl
buildCommentP-roundtrip (mkComment (CTEnvVar _) _) pos input = refl
buildCommentP-roundtrip (mkComment (CTMessage cid) text) pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl
buildCommentP-roundtrip (mkComment (CTSignal cid s) text) pos input
  with buildCANId (rawCanIdℕ cid) | buildCANId-rawCanIdℕ cid
... | just .cid | refl = refl

-- ============================================================================
-- SLIM `parseComment-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseComment = parse commentFmt >>= λ result →
-- many parseNewline >>= λ _ → buildCommentP (proj₁ result) (proj₁ (proj₂ result))`.
-- Composition decomposes into:
--
--   1. `parse commentFmt pos (emit commentFmt _ ++ suffix)` via
--      `parseComment-format-roundtrip`.
--   2. `many parseNewline pos' suffix` returns `[]`-no-consume via
--      `manyHelper-parseNewline-exhaust` + `nl-stop` precondition.
--   3. `buildCommentP rt text` returns `just (mkResult c pos' input)`
--      via `buildCommentP-roundtrip` (5-way dispatch + CAN-ID rescue).
--
-- `cong` on the input rewrites `emit commentFmt _ ++ suffix` to
-- `emitComment-chars c ++ suffix` via the bridge.  Output position
-- transports through the same bridge.
parseComment-roundtrip :
    ∀ (pos : Position) (c : DBCComment) (suffix : List Char)
  → CommentTargetStop c
  → SuffixStops isNewlineStart suffix
  → parseComment pos (emitComment-chars c ++ₗ suffix)
    ≡ just (mkResult c
             (advancePositions pos (emitComment-chars c))
             suffix)
parseComment-roundtrip pos c suffix tgtStop nl-stop =
  trans (cong (λ inp → parseComment pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-format
      (trans step-many-newline
        step-build))
  where
    bridge : emit commentFmt
              (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
           ≡ emitComment-chars c
    bridge = emit-commentFmt-eq-emitComment-chars c

    raw-text : RawCommentTarget × (List Char × ⊤)
    raw-text = rawTargetOf (DBCComment.target c) , DBCComment.text c , tt

    pos-line : Position
    pos-line = advancePositions pos (emit commentFmt raw-text)

    cont-line :
        RawCommentTarget × (List Char × ⊤) → Parser DBCComment
    cont-line result =
      many parseNewline >>= λ _ →
      buildCommentP (proj₁ result) (proj₁ (proj₂ result))

    cont-blanks : List Char → Parser DBCComment
    cont-blanks _ =
      buildCommentP (proj₁ raw-text) (proj₁ (proj₂ raw-text))

    -- Step 1: parse commentFmt succeeds via the universal roundtrip.
    step-format :
      parseComment pos (emit commentFmt raw-text ++ₗ suffix)
      ≡ cont-line raw-text pos-line suffix
    step-format =
      bind-just-step (parse commentFmt)
                     cont-line
                     pos (emit commentFmt raw-text ++ₗ suffix)
                     raw-text pos-line suffix
                     (parseComment-format-roundtrip pos c suffix tgtStop)

    -- Step 2: many parseNewline consumes zero from `suffix`.
    step-many-newline :
      cont-line raw-text pos-line suffix
      ≡ cont-blanks [] pos-line suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line suffix
                     [] pos-line suffix
                     (manyHelper-parseNewline-exhaust
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: buildCommentP recovers DBCComment, transport position via
    -- bridge.
    step-build :
      cont-blanks [] pos-line suffix
      ≡ just (mkResult c
               (advancePositions pos (emitComment-chars c))
               suffix)
    step-build =
      trans (buildCommentP-roundtrip c pos-line suffix)
            (cong (λ p → just (mkResult c p suffix))
                  (cong (advancePositions pos) bridge))


-- ============================================================================
-- LIST-LEVEL ROUNDTRIP — `many parseComment` over a CM_ block
-- ============================================================================

-- `0 < length (emitComment-chars c)` — the literal `"CM_ "` prefix is
-- shared across all 5 target shapes; case-split on `c.target` to expose
-- the cons.
emitComment-chars-nonzero : ∀ (c : DBCComment)
  → 0 < length (emitComment-chars c)
emitComment-chars-nonzero (mkComment CTNetwork      _) = s≤s z≤n
emitComment-chars-nonzero (mkComment (CTNode _)     _) = s≤s z≤n
emitComment-chars-nonzero (mkComment (CTMessage _)  _) = s≤s z≤n
emitComment-chars-nonzero (mkComment (CTSignal _ _) _) = s≤s z≤n
emitComment-chars-nonzero (mkComment (CTEnvVar _)   _) = s≤s z≤n

-- Head of `emitComment-chars c` is `'C'` — not a newline-start.
-- Per-target case-split mirrors the formatter's `body` dispatcher.
emitComment-chars-head-not-newline :
    ∀ (c : DBCComment) (suffix : List Char)
  → SuffixStops isNewlineStart (emitComment-chars c ++ₗ suffix)
emitComment-chars-head-not-newline (mkComment CTNetwork      _) _ = ∷-stop refl
emitComment-chars-head-not-newline (mkComment (CTNode _)     _) _ = ∷-stop refl
emitComment-chars-head-not-newline (mkComment (CTMessage _)  _) _ = ∷-stop refl
emitComment-chars-head-not-newline (mkComment (CTSignal _ _) _) _ = ∷-stop refl
emitComment-chars-head-not-newline (mkComment (CTEnvVar _)   _) _ = ∷-stop refl


parseComments-roundtrip :
    ∀ (pos : Position) (cs : List DBCComment) (outer-suffix : List Char)
  → All CommentTargetStop cs
  → SuffixStops isNewlineStart outer-suffix
  → (∀ (pos' : Position) → parseComment pos' outer-suffix ≡ nothing)
  → many parseComment pos
      (foldr (λ c acc → emitComment-chars c ++ₗ acc) [] cs ++ₗ outer-suffix)
    ≡ just (mkResult cs
             (advancePositions pos
               (foldr (λ c acc → emitComment-chars c ++ₗ acc) [] cs))
             outer-suffix)
parseComments-roundtrip pos cs outer-suffix cs-stops os pf =
  many-η-roundtrip
    parseComment
    emitComment-chars
    CommentTargetStop
    (λ pos₁ c suffix tgtStop nl-stop →
       parseComment-roundtrip pos₁ c suffix tgtStop nl-stop)
    emitComment-chars-nonzero
    emitComment-chars-head-not-newline
    pos cs outer-suffix cs-stops os pf
  where
    open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip using
      (many-η-roundtrip)
