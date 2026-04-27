{-# OPTIONS --safe --without-K #-}

-- Per-primitive roundtrip lemmas for the DBC text-format parser
-- (B.3.d Layer 2).
--
-- Commit 2b landed `parseIdentifier-roundtrip`.  Commit 2c adds Tier A
-- (char / keyword dispatch — no `many`, no embedded sub-parser) and
-- Tier B (internal `many` / one embedded sub-parser):
--
--   Tier A:
--     * `parseByteOrderDigit-roundtrip`
--     * `parseSignFlag-roundtrip`
--     * `parseOptionalStandardScope-roundtrip`  (ASNetwork fallback +
--       4 standard scope tags — `BU_` / `BO_` / `SG_` / `EV_`)
--     * `parseRelScopeWS-roundtrip`             (2 rel scope tags —
--       `BU_BO_REL_` / `BU_SG_REL_`)
--     * `parseStringType-roundtrip`             (bare `ATString` —
--       `"STRING"` keyword)
--
--   Tier B:
--     * `parseStringLit-roundtrip`              (escape body)
--     * `parseMuxMarker-roundtrip`              (inverse targets
--       `MuxMarker`, NOT `SignalPresence` — see project memory)
--
-- `ATInt` / `ATFloat` / `ATHex` / `ATEnum` and `SignalPresence` are
-- reclassified to Layer 3: they're per-line-construct payloads with
-- internal WS separation or post-parse context resolution, not
-- primitives.  See `memory/project_b3d_universal_proof.md`.
module Aletheia.DBC.TextParser.Properties.Primitives where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.Properties using (T?; T-irrelevant)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Data.Bool.Base using (if_then_else_; not)
open import Data.Char.Base using (_≈ᵇ_; toℕ; isDigit)
open import Data.Char using () renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Properties using (toℕ-injective)
open import Data.List using (foldr; length)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; ≤-refl; ≡ᵇ⇒≡; m≤n⇒m≤1+n; m≤m+n; ≤-trans)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Relation.Nullary using (¬_)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   pure; fail; _>>=_; _<|>_; _*>_; _<*_; satisfy; many; manyHelper;
   char; string; parseCharsSeq; sameLengthᵇ)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; mkIdentFromChars; isIdentStart; isIdentCont;
   validIdentifierᵇ; allᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; buildIdent; fromMaybeIdent;
   parseStringLit; parseStringChar; parseWS; parseWSOpt; isHSpace;
   parseNatural)
open import Aletheia.DBC.TextParser.Topology using
  (parseByteOrderDigit; parseSignFlag;
   parseMuxMarker; MuxMarker; NotMux; IsMux; SelBy; BothMux)
open import Aletheia.DBC.TextParser.Attributes using
  (parseStandardScope; parseRelScope; parseOptionalStandardScope;
   parseStringType)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitByteOrderDigit-chars; emitSignFlag-chars; emitMuxMarker-chars)
open import Aletheia.DBC.TextFormatter.Attributes using
  (emitScopePrefix-chars; emitAttrType-chars)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; escapeChar-chars; showℕ-dec-chars; showNat-chars)
-- Post-3d.4 + JSON-mirror: Substrate.Unsafe is no longer imported here.
-- `mkIdentFromCharsUnsafe-on-valid` (which needed `fromList∘toList`)
-- becomes `mkIdentFromChars-on-valid` (axiom-free, via `T?` decision).
-- `parseStringLit-roundtrip` now takes `(cs : List Char)` and parses
-- back to the same `cs`, so the trailing `fromList∘toList s` cong step
-- is gone.  This module becomes axiom-free and lifts to `--safe`.
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; sameLengthᵇ-cons;
   advancePositions-++; parseNatural-showNat-chars)
open import Aletheia.Prelude using (ifᵀ-witness; T→true)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.DBC.Types using
  (AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar;
   ASNodeMsg; ASNodeSig; AttrType; ATString)

-- ============================================================================
-- Probe 1 — decompose-valid
-- ============================================================================
--
-- `T (validIdentifierᵇ cs)` destructures into: `cs = h ∷ t`, the head
-- satisfies `isIdentStart`, and the tail is pointwise `isIdentCont`.
-- Empty list rejected by `validIdentifierᵇ [] = false → T false = ⊥`.

-- Helper: T (a ∧ b) → T a × T b  (stdlib has this but requires specific import)
private
  T-∧-split : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
  T-∧-split {true}  {true}  _ = tt , tt
  T-∧-split {true}  {false} ()
  T-∧-split {false} {_}     ()

-- Helper: T (allᵇ p xs) → All (T ∘ p) xs
private
  T-allᵇ→All : ∀ (p : Char → Bool) (xs : List Char)
             → T (allᵇ p xs) → All (T ∘ p) xs
  T-allᵇ→All p []       _  = []
  T-allᵇ→All p (c ∷ cs) ab =
    let (pc , pcs) = T-∧-split {p c} {allᵇ p cs} ab
    in pc ∷ T-allᵇ→All p cs pcs

decompose-valid : ∀ (cs : List Char) → T (validIdentifierᵇ cs)
  → ∃[ h ] ∃[ t ]
    (cs ≡ h ∷ t) × T (isIdentStart h) × All (T ∘ isIdentCont) t
decompose-valid []       ()
decompose-valid (h ∷ t) valid =
  let (ph , pt) = T-∧-split {isIdentStart h} {allᵇ isIdentCont t} valid
  in h , t , refl , ph , T-allᵇ→All isIdentCont t pt

-- ============================================================================
-- Probe 2 — mkIdentFromChars on a valid Identifier's char list
-- ============================================================================
--
-- Post-3d.4 + JSON-mirror: `Identifier.name : List Char`, so the parser
-- builds Identifiers via `mkIdentFromChars : List Char → Maybe Identifier`
-- (`Aletheia.DBC.Identifier`).  No `String ↔ List Char` bridging needed.
-- The proof mirrors `validateIdent-roundtrip` in `MetadataRoundtrip`:
-- match the `with T? (validIdentifierᵇ name)` in the function definition
-- by the same `with` here; the `yes w` branch closes via `T-irrelevant`
-- on the witness field, and the `no ¬w` branch is absurd (`¬w valid`).
mkIdentFromChars-on-valid : ∀ (i : Identifier)
  → mkIdentFromChars (Identifier.name i) ≡ just i
mkIdentFromChars-on-valid (mkIdent name valid)
  with T? (validIdentifierᵇ name)
... | yes w  = cong (λ v → just (mkIdent name v)) (T-irrelevant w valid)
... | no  ¬w = ⊥-elim (¬w valid)

-- ============================================================================
-- Probe 3 — position alignment (decomposition consistency)
-- ============================================================================
--
-- `Identifier.name i` IS `h ∷ t` where (h, t) come from `decompose-valid`
-- applied to `Identifier.valid i`.  Follows by refl from the decomposition's
-- first output equation.

decompose-valid-matches-name : ∀ (i : Identifier)
  → let cs = Identifier.name i
        d  = decompose-valid cs (Identifier.valid i)
        h  = Data.Product.proj₁ d
        t  = Data.Product.proj₁ (Data.Product.proj₂ d)
    in cs ≡ h ∷ t
decompose-valid-matches-name i
  with decompose-valid (Identifier.name i) (Identifier.valid i)
... | _ , _ , eq , _ , _ = eq

-- ============================================================================
-- Probe 4 — satisfy-success-T
-- ============================================================================
--
-- `satisfy P` succeeds and consumes one char given a `T (P h)` witness.
-- Mirrors the pattern used by `some-satisfy-prefix` in
-- `DecRatParse.Properties` — `rewrite T→true ph` unblocks the internal
-- `with P h` in `satisfy`'s body, at which point `refl` closes the goal.

satisfy-success-T : ∀ (P : Char → Bool) (pos : Position) (h : Char) (cs : List Char)
  → T (P h)
  → satisfy P pos (h ∷ cs) ≡ just (mkResult h (advancePosition pos h) cs)
satisfy-success-T P pos h cs ph rewrite T→true ph = refl

-- ============================================================================
-- Probe 5 — buildIdent-eq
-- ============================================================================
--
-- `buildIdent h t ≡ pure i` follows by `cong fromMaybeIdent` from the
-- `mkIdentFromChars (h ∷ t) ≡ just i` equation (given by
-- `mkIdentFromChars-on-valid` composed with `sym cs-eq` from
-- `decompose-valid`).  The Lexer refactor (split into
-- `buildIdent h t = fromMaybeIdent (mkIdentFromChars (h ∷ t))`) is the
-- reason this closes as a one-liner — a top-level `with` in `buildIdent`
-- would have hidden the Maybe from external rewriting.

buildIdent-eq : ∀ (h : Char) (t : List Char) (i : Identifier)
  → mkIdentFromChars (h ∷ t) ≡ just i
  → buildIdent h t ≡ pure i
buildIdent-eq _ _ _ eq = cong fromMaybeIdent eq

-- ============================================================================
-- parseIdentifier-roundtrip — composed theorem
-- ============================================================================
--
-- The main layer-2 Identifier lemma: parsing any valid Identifier's char
-- list concatenated with a stopping suffix returns that Identifier plus
-- the untouched suffix.  Structure mirrors
-- `DecRatParse/Properties.parseDecRat-roundtrip-+suc` — two
-- `bind-just-step`s + one final `buildIdent-eq`-applied step, chained
-- via `trans`.  `subst` on `sym cs-eq` lifts the concrete-shape proof
-- (`h ∷ t` form) back to the abstract `Identifier.name i` form the
-- public theorem advertises.  Post-3d.4 `Identifier.name : List Char`
-- means the public statement is in terms of the same `List Char`
-- substrate the parser machinery operates on — no `toList` wrap needed.

-- Lift `All (T ∘ P) xs` to `All (λ c → P c ≡ true) xs` — the form
-- `manyHelper-satisfy-exhaust-many` demands.  Trivial pointwise `T→true`.
private
  T-All→≡true : ∀ {P : Char → Bool} {xs : List Char}
             → All (T ∘ P) xs
             → All (λ c → P c ≡ true) xs
  T-All→≡true []         = []
  T-All→≡true (px ∷ pxs) = T→true px ∷ T-All→≡true pxs

parseIdentifier-roundtrip : ∀ (pos : Position) (i : Identifier)
                              (suffix : List Char)
                            → SuffixStops isIdentCont suffix
                            → parseIdentifier pos
                                (Identifier.name i ++ₗ suffix)
                              ≡ just (mkResult i
                                       (advancePositions pos
                                          (Identifier.name i))
                                       suffix)
parseIdentifier-roundtrip pos i suffix ss
  with decompose-valid (Identifier.name i) (Identifier.valid i)
... | h , t , cs-eq , start , conts =
      subst (λ cs → parseIdentifier pos (cs ++ₗ suffix)
                      ≡ just (mkResult i (advancePositions pos cs) suffix))
            (sym cs-eq)
            concrete-proof
  where
    pos' : Position
    pos' = advancePosition pos h

    pos'' : Position
    pos'' = advancePositions pos' t

    -- satisfy isIdentStart consumes h, advancing to pos' with tail t++suffix.
    step-satisfy :
      parseIdentifier pos ((h ∷ t) ++ₗ suffix)
      ≡ (many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
          pos' (t ++ₗ suffix)
    step-satisfy =
      bind-just-step (satisfy isIdentStart)
                     (λ h' → many (satisfy isIdentCont) >>=
                             λ t' → buildIdent h' t')
                     pos ((h ∷ t) ++ₗ suffix)
                     h pos' (t ++ₗ suffix)
                     (satisfy-success-T isIdentStart pos h (t ++ₗ suffix) start)

    -- many (satisfy isIdentCont) consumes t, advancing to pos'' with suffix.
    step-many :
      (many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
        pos' (t ++ₗ suffix)
      ≡ buildIdent h t pos'' suffix
    step-many =
      bind-just-step (many (satisfy isIdentCont))
                     (λ t' → buildIdent h t')
                     pos' (t ++ₗ suffix)
                     t pos'' suffix
                     (manyHelper-satisfy-exhaust-many isIdentCont pos' t suffix
                        (T-All→≡true conts) ss)

    -- buildIdent h t reduces via fromMaybeIdent (mkIdentFromChars (h ∷ t))
    -- = fromMaybeIdent (just i) = pure i, once we bridge through cs-eq and
    -- mkIdentFromChars-on-valid.
    mki-eq : mkIdentFromChars (h ∷ t) ≡ just i
    mki-eq = trans (cong mkIdentFromChars (sym cs-eq))
                   (mkIdentFromChars-on-valid i)

    step-build :
      buildIdent h t pos'' suffix
      ≡ just (mkResult i pos'' suffix)
    step-build = cong (λ p → p pos'' suffix) (buildIdent-eq h t i mki-eq)

    concrete-proof :
      parseIdentifier pos ((h ∷ t) ++ₗ suffix)
      ≡ just (mkResult i (advancePositions pos (h ∷ t)) suffix)
    concrete-proof = trans step-satisfy (trans step-many step-build)

-- ============================================================================
-- Tier A — single-char keyword dispatch
-- ============================================================================

-- ByteOrder digit — one-character match.  The emitter produces a single
-- concrete char (`'0'` or `'1'`); the parser's `(char '0' *> …) <|>
-- (char '1' *> …)` reduces definitionally on closed chars so both cases
-- are `refl`.  No suffix precondition: the parser consumes exactly one
-- char and leaves the tail untouched.

parseByteOrderDigit-roundtrip : ∀ (pos : Position) (bo : ByteOrder)
                                  (suffix : List Char)
  → parseByteOrderDigit pos (emitByteOrderDigit-chars bo ++ₗ suffix)
    ≡ just (mkResult bo (advancePositions pos
                           (emitByteOrderDigit-chars bo)) suffix)
parseByteOrderDigit-roundtrip _ LittleEndian _ = refl
parseByteOrderDigit-roundtrip _ BigEndian    _ = refl

-- Sign flag — DBC historical encoding: `'+'` = unsigned (false), `'-'` =
-- signed (true).  Same single-char dispatch pattern as ByteOrder;
-- definitional reduction on closed chars closes both cases.

parseSignFlag-roundtrip : ∀ (pos : Position) (b : Bool) (suffix : List Char)
  → parseSignFlag pos (emitSignFlag-chars b ++ₗ suffix)
    ≡ just (mkResult b (advancePositions pos (emitSignFlag-chars b))
                     suffix)
parseSignFlag-roundtrip _ true  _ = refl
parseSignFlag-roundtrip _ false _ = refl

-- ============================================================================
-- Char equality — concrete char matches trivially, abstract needs reflexivity
-- ============================================================================

-- `_≈ᵇ_` is `toℕ c ≡ᵇ toℕ d`; reflexivity reduces definitionally on closed
-- chars but needs a lemma on an abstract `c`.  Thread through stdlib's
-- `≡⇒≡ᵇ` + `T→true`.

≈ᵇ-refl : ∀ (c : Char) → (c ≈ᵇ c) ≡ true
≈ᵇ-refl c = T→true (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)

-- `char c` on input starting with exactly `c` consumes one char and
-- advances position.  `rewrite ≈ᵇ-refl c` unblocks the internal
-- `with c ≈ᵇ c` inside `satisfy`'s body, leaving `refl`.

char-matches : ∀ (c : Char) (pos : Position) (cs : List Char)
  → char c pos (c ∷ cs)
    ≡ just (mkResult c (advancePosition pos c) cs)
char-matches c pos cs rewrite ≈ᵇ-refl c = refl

-- ============================================================================
-- Tier A — `string` keyword helpers
-- ============================================================================

-- `string s` on input that begins with `toList s` succeeds and returns
-- `just (mkResult s (advancePositions pos (toList s)) suffix)`.
--
-- Proof pattern: induct on the char list `cs = toList s`, reducing the
-- internal `parseChars` recursion one char at a time.  Each step uses
-- definitional reduction of `char c` on `c ∷ rest`.  Factored out so
-- every scope / keyword primitive reuses it.

-- `parseCharsSeq cs` on input `cs ++ₗ suffix` succeeds, returning the
-- same list `cs` with the position advanced past every element.  Induct
-- on `cs`; each step uses `char-matches` to reduce the head char match
-- then recurses on the tail.
parseCharsSeq-success : ∀ (pos : Position) (cs : List Char)
                          (suffix : List Char)
  → parseCharsSeq cs pos (cs ++ₗ suffix)
    ≡ just (mkResult cs (advancePositions pos cs) suffix)
parseCharsSeq-success pos []       suffix = refl
parseCharsSeq-success pos (c ∷ cs) suffix =
  trans (bind-just-step (char c)
           (λ x → parseCharsSeq cs >>= λ xs → pure (x ∷ xs))
           pos (c ∷ cs ++ₗ suffix)
           c (advancePosition pos c) (cs ++ₗ suffix)
           (char-matches c pos (cs ++ₗ suffix)))
    (trans (bind-just-step (parseCharsSeq cs)
              (λ xs → pure (c ∷ xs))
              (advancePosition pos c) (cs ++ₗ suffix)
              cs (advancePositions (advancePosition pos c) cs) suffix
              (parseCharsSeq-success (advancePosition pos c) cs suffix))
       refl)

-- `string`-success lemma: `string s` on `toList s ++ₗ suffix` returns
-- `just (mkResult s (advancePositions pos (toList s)) suffix)`.
string-success : ∀ (pos : Position) (s : String) (suffix : List Char)
  → string s pos (toList s ++ₗ suffix)
    ≡ just (mkResult s (advancePositions pos (toList s)) suffix)
string-success pos s suffix =
  bind-just-step (parseCharsSeq (toList s))
                 (λ _ → pure s)
                 pos (toList s ++ₗ suffix)
                 (toList s) (advancePositions pos (toList s)) suffix
                 (parseCharsSeq-success pos (toList s) suffix)

-- `(string s *> pure v)` — the keyword-dispatch idiom used by every
-- scope / attr-type-tag parser.  Composes `string-success` with a
-- single `bind-just-step`.
string-*>-success : ∀ {V : Set} (pos : Position) (s : String) (v : V)
                      (suffix : List Char)
  → (string s *> pure v) pos (toList s ++ₗ suffix)
    ≡ just (mkResult v (advancePositions pos (toList s)) suffix)
string-*>-success pos s v suffix =
  bind-just-step (string s)
                 (λ _ → pure v)
                 pos (toList s ++ₗ suffix)
                 s (advancePositions pos (toList s)) suffix
                 (string-success pos s suffix)

-- ============================================================================
-- <|> reduction lemmas
-- ============================================================================

-- `p <|> q` reduces to `q` when `p` returns `nothing`.
alt-right-nothing : ∀ {A : Set} (p q : Parser A) (pos : Position)
                      (input : List Char)
  → p pos input ≡ nothing
  → (p <|> q) pos input ≡ q pos input
alt-right-nothing p q pos input eq with p pos input | eq
... | nothing | refl = refl

-- `p <|> q` reduces to `just r` when `p` returns `just r` (left wins).
alt-left-just : ∀ {A : Set} (p q : Parser A) (pos : Position)
                  (input : List Char) r
  → p pos input ≡ just r
  → (p <|> q) pos input ≡ just r
alt-left-just p q pos input r eq with p pos input | eq
... | just .r | refl = refl

-- Bind propagates `nothing` outward.
bind-nothing : ∀ {A B : Set} (p : Parser A) (f : A → Parser B)
                 (pos : Position) (input : List Char)
  → p pos input ≡ nothing
  → (p >>= f) pos input ≡ nothing
bind-nothing p f pos input eq with p pos input | eq
... | nothing | refl = refl

-- ============================================================================
-- parseWS on "one horizontal space then non-space suffix"
-- ============================================================================

-- `parseWS = some (satisfy isHSpace) = (λ x xs → x ∷ xs) <$> satisfy … <*> many …`.
-- On input `' ' ∷ suffix` with `SuffixStops isHSpace suffix`, `satisfy`
-- consumes the space, `many` returns empty (base case: the suffix's head
-- fails `isHSpace`), and the `<$>`/`<*>` chain wraps the result as
-- `[' ']`.
parseWS-one-space : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseWS pos (' ' ∷ suffix)
    ≡ just (mkResult (' ' ∷ [])
                     (advancePosition pos ' ') suffix)
parseWS-one-space pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition pos ' ') [] suffix [] ss
  = refl

-- ============================================================================
-- Tier A — scope tag roundtrips
-- ============================================================================
--
-- The parser-emitter pair:
--   emitter  `emitScopePrefix-chars` — closed string literals with a
--            trailing space for non-Network scopes.
--   parser   `parseOptionalStandardScope` = `parseStandardScope <*
--            parseWS <|> pure ASNetwork` for standard scopes;
--            `parseRelScope <* parseWS` for BA_DEF_REL_ paths.
--
-- Both the `<|>` chain inside `parseStandardScope` / `parseRelScope`
-- and the outer `<* parseWS` reduce definitionally on closed keyword
-- prefixes.  The only non-refl step is `many (satisfy isHSpace)`'s
-- termination on the suffix, discharged by `manyHelper-satisfy-
-- exhaust-many` under a `SuffixStops isHSpace suffix` precondition.

-- Non-network standard scopes — four tags `BU_`, `BO_`, `SG_`, `EV_`.
-- Each emits `<keyword> <space>`; the parser consumes the keyword via
-- the matching `<|>` branch, then `<* parseWS` consumes the trailing
-- space (and stops at the suffix boundary).

parseOptionalStandardScope-ASNode-roundtrip : ∀ (pos : Position)
                                                  (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseOptionalStandardScope pos (emitScopePrefix-chars ASNode ++ₗ suffix)
    ≡ just (mkResult ASNode
             (advancePositions pos (emitScopePrefix-chars ASNode))
             suffix)
parseOptionalStandardScope-ASNode-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
               (advancePosition pos 'B') 'U') '_') ' ')
            [] suffix [] ss = refl

parseOptionalStandardScope-ASMessage-roundtrip : ∀ (pos : Position)
                                                    (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseOptionalStandardScope pos (emitScopePrefix-chars ASMessage ++ₗ suffix)
    ≡ just (mkResult ASMessage
             (advancePositions pos (emitScopePrefix-chars ASMessage))
             suffix)
parseOptionalStandardScope-ASMessage-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
               (advancePosition pos 'B') 'O') '_') ' ')
            [] suffix [] ss = refl

parseOptionalStandardScope-ASSignal-roundtrip : ∀ (pos : Position)
                                                   (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseOptionalStandardScope pos (emitScopePrefix-chars ASSignal ++ₗ suffix)
    ≡ just (mkResult ASSignal
             (advancePositions pos (emitScopePrefix-chars ASSignal))
             suffix)
parseOptionalStandardScope-ASSignal-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
               (advancePosition pos 'S') 'G') '_') ' ')
            [] suffix [] ss = refl

parseOptionalStandardScope-ASEnvVar-roundtrip : ∀ (pos : Position)
                                                   (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseOptionalStandardScope pos (emitScopePrefix-chars ASEnvVar ++ₗ suffix)
    ≡ just (mkResult ASEnvVar
             (advancePositions pos (emitScopePrefix-chars ASEnvVar))
             suffix)
parseOptionalStandardScope-ASEnvVar-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
               (advancePosition pos 'E') 'V') '_') ' ')
            [] suffix [] ss = refl

-- Network scope — empty emission; the parser falls through to
-- `pure ASNetwork` when the left branch fails.  Precondition:
-- `parseStandardScope pos suffix ≡ nothing` (no scope keyword at
-- the head of `suffix`).  The `<* parseWS` bind propagates `nothing`
-- via `bind-nothing`, and `<|>` falls through via `alt-right-nothing`.

parseOptionalStandardScope-ASNetwork-roundtrip : ∀ (pos : Position)
                                                    (suffix : List Char)
  → parseStandardScope pos suffix ≡ nothing
  → parseOptionalStandardScope pos (emitScopePrefix-chars ASNetwork ++ₗ suffix)
    ≡ just (mkResult ASNetwork
             (advancePositions pos (emitScopePrefix-chars ASNetwork))
             suffix)
parseOptionalStandardScope-ASNetwork-roundtrip pos suffix eq =
  trans (alt-right-nothing (parseStandardScope <* parseWS)
                           (pure ASNetwork) pos suffix
          (bind-nothing parseStandardScope _ pos suffix eq))
    refl

-- ============================================================================
-- Tier A — rel scope tag roundtrips (`parseRelScope <* parseWS` path)
-- ============================================================================

-- `parseRelScope` pairs with BA_DEF_REL_ contexts.  Emission:
-- `BU_BO_REL_ ` or `BU_SG_REL_ ` (11 chars + trailing space).  The
-- parser `parseRelScope <* parseWS` is the BA_DEF_REL_ caller's
-- concrete wrapping; we prove the pair here at Layer 2.

-- `(parseRelScope <* parseWS)` composite parser, named for clarity.
parseRelScopeWS : Parser AttrScope
parseRelScopeWS = parseRelScope <* parseWS

parseRelScopeWS-ASNodeMsg-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseRelScopeWS pos (emitScopePrefix-chars ASNodeMsg ++ₗ suffix)
    ≡ just (mkResult ASNodeMsg
             (advancePositions pos (emitScopePrefix-chars ASNodeMsg))
             suffix)
parseRelScopeWS-ASNodeMsg-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition pos 'B') 'U') '_')
              'B') 'O') '_') 'R') 'E') 'L') '_') ' ')
            [] suffix [] ss = refl

parseRelScopeWS-ASNodeSig-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseRelScopeWS pos (emitScopePrefix-chars ASNodeSig ++ₗ suffix)
    ≡ just (mkResult ASNodeSig
             (advancePositions pos (emitScopePrefix-chars ASNodeSig))
             suffix)
parseRelScopeWS-ASNodeSig-roundtrip pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition (advancePosition
            (advancePosition (advancePosition pos 'B') 'U') '_')
              'S') 'G') '_') 'R') 'E') 'L') '_') ' ')
            [] suffix [] ss = refl

-- ============================================================================
-- Tier A — `ATString` attr-type tag roundtrip
-- ============================================================================
--
-- `emitAttrType-chars ATString = toList "STRING"`.  The parser
-- `parseStringType = string "STRING" *> pure ATString` is a single
-- keyword match.  Using `string-*>-success`.

parseStringType-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → parseStringType pos (emitAttrType-chars ATString ++ₗ suffix)
    ≡ just (mkResult ATString
             (advancePositions pos (emitAttrType-chars ATString))
             suffix)
parseStringType-roundtrip pos suffix =
  string-*>-success pos "STRING" ATString suffix

-- ============================================================================
-- Tier B — string literal roundtrip
-- ============================================================================
--
-- `quoteStringLit-chars cs = '"' ∷ (body) ++ₗ '"' ∷ []` where the body
-- is `foldr` expanding each `"` to `""`.  The parser consumes the
-- opening quote, `many parseStringChar` expands back to the original
-- `cs`, then consumes the closing quote.  Post-3d.4 + JSON-mirror,
-- `parseStringLit : Parser (List Char)` returns `cs` directly (no
-- `fromList`); the trailing `fromList∘toList` axiom step is gone.
--
-- Bool-form precondition: `SuffixStops (λ c → c ≈ᵇ '"') suffix`.  We
-- pick `_≈ᵇ_` because every concrete char-dispatch inside the body
-- reduces through `char '"'` (which uses `_≈ᵇ_` via `satisfy`).  The
-- ambient `escapeChar-chars` + `satisfy (not ⌊ _ ≟ᶜ '"' ⌋)` branches
-- use `_≟ᶜ_`; we bridge once with `≈ᵇ-false→≟ᶜ-false`.

-- Structural decomposition of the escape-body produced by the
-- `foldr` inside `quoteStringLit-chars`.
escape-body-chars : List Char → List Char
escape-body-chars []       = []
escape-body-chars (c ∷ cs) = escapeChar-chars c ++ₗ escape-body-chars cs

-- `quoteStringLit-chars` rewritten as explicit open quote + escape
-- body + close quote.  Structural induction on `cs`; the `cons` step
-- uses `++ₗ-assoc` to relocate the close-quote seed from inside the
-- `foldr` into the list-append chain.
quoteStringLit-chars-shape : ∀ (cs : List Char)
  → quoteStringLit-chars cs
    ≡ '"' ∷ escape-body-chars cs ++ₗ '"' ∷ []
quoteStringLit-chars-shape cs = cong ('"' ∷_) (shape cs)
  where
    shape : ∀ (xs : List Char)
      → foldr (λ c acc → escapeChar-chars c ++ₗ acc) ('"' ∷ []) xs
        ≡ escape-body-chars xs ++ₗ '"' ∷ []
    shape []       = refl
    shape (x ∷ xs) =
      trans (cong (λ acc → escapeChar-chars x ++ₗ acc) (shape xs))
            (sym (++ₗ-assoc (escapeChar-chars x)
                    (escape-body-chars xs) ('"' ∷ [])))

-- ============================================================================
-- Char (in)equality bridges for the string-literal proofs
-- ============================================================================

-- `c ≢ d` ⇒ `⌊ c ≟ᶜ d ⌋ ≡ false`.  Routine case-split on decidability.
⌊⌋-false-of-≢ : ∀ {c d : Char} → ¬ (c ≡ d) → ⌊ c ≟ᶜ d ⌋ ≡ false
⌊⌋-false-of-≢ {c} {d} c≢d with c ≟ᶜ d
... | yes c≡d = ⊥-elim (c≢d c≡d)
... | no  _   = refl

-- `c ≢ d` ⇒ `(c ≈ᵇ d) ≡ false`.  Bridge through the primitive
-- `toℕ-injective`: if `c ≈ᵇ d = true`, then `toℕ c ≡ᵇ toℕ d = true`,
-- hence `toℕ c ≡ toℕ d` (via stdlib `≡ᵇ⇒≡`), hence `c ≡ d` — which
-- contradicts the precondition.
≈ᵇ-false-of-≢ : ∀ {c d : Char} → ¬ (c ≡ d) → (c ≈ᵇ d) ≡ false
≈ᵇ-false-of-≢ {c} {d} c≢d with c ≈ᵇ d in eq
... | false = refl
... | true  =
      ⊥-elim (c≢d (toℕ-injective c d
                     (≡ᵇ⇒≡ (toℕ c) (toℕ d) (subst T (sym eq) tt))))
  where open import Data.Bool using (T)


-- ============================================================================
-- parseStringChar probes
-- ============================================================================

-- Escape pair: closed-char dispatch reduces to refl.  `string "\"\""`
-- matches the two concrete `"` characters via the parseCharsSeq
-- definitional expansion; the outer `<|>` returns via `alt-left-just`
-- (definitionally).
parseStringChar-escape : ∀ (pos : Position) (rest : List Char)
  → parseStringChar pos ('"' ∷ '"' ∷ rest)
    ≡ just (mkResult '"'
             (advancePosition (advancePosition pos '"') '"') rest)
parseStringChar-escape _ _ = refl

-- Non-quote literal: `string "\"\""` branch fails (char '"' on `c ∷ rest`
-- with `c ≢ '"'` fails), so `<|>` falls to `satisfy (not ⌊ _ ≟ᶜ '"' ⌋)`.
-- With `⌊ c ≟ᶜ '"' ⌋ ≡ false`, `not false = true`, and `satisfy`
-- succeeds with the head char.
parseStringChar-literal : ∀ (pos : Position) (c : Char) (rest : List Char)
  → ¬ (c ≡ '"')
  → parseStringChar pos (c ∷ rest)
    ≡ just (mkResult c (advancePosition pos c) rest)
parseStringChar-literal pos c rest c≢quote
  rewrite ≈ᵇ-false-of-≢ {c} {'"'} c≢quote
        | ⌊⌋-false-of-≢ {c} {'"'} c≢quote = refl

-- Fail at closing quote: input `'"' ∷ suffix` with suffix not starting
-- with `"`.  Both `<|>` branches fail:
--   * `string "\"\""` tries `char '"'` (succeeds at position 0),
--     then `char '"'` on `suffix`.  `suffix` first-char isn't `"`
--     (via `SuffixStops _≈ᵇ_ `) → fails.
--   * `satisfy (not ⌊ '"' ≟ᶜ '"' ⌋)` = `satisfy (not true)` =
--     `satisfy false-predicate` → fails on any non-empty input.
parseStringChar-fail-at-close : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → parseStringChar pos ('"' ∷ suffix) ≡ nothing
parseStringChar-fail-at-close pos [] _ = refl
parseStringChar-fail-at-close pos (c ∷ suffix) (∷-stop ≈false)
  rewrite ≈false = refl

-- `escape-body-chars` dispatch helpers: the `c = '"'` branch emits
-- `'"' ∷ '"' ∷ []` (escape pair); the non-quote branch emits `c ∷ []`.
escape-body-chars-quote : ∀ (cs : List Char)
  → escape-body-chars ('"' ∷ cs) ≡ '"' ∷ '"' ∷ escape-body-chars cs
escape-body-chars-quote _ = refl

escape-body-chars-nonquote : ∀ (c : Char) (cs : List Char)
  → ¬ (c ≡ '"')
  → escape-body-chars (c ∷ cs) ≡ c ∷ escape-body-chars cs
escape-body-chars-nonquote c cs c≢quote
  rewrite ⌊⌋-false-of-≢ {c} {'"'} c≢quote = refl

-- Cons-by-2 progress witness for `manyHelper`'s `sameLengthᵇ` check.
-- Structurally recursive on the tail; mirrors `sameLengthᵇ-cons` in
-- `DecRatParse.Properties` (which covers the cons-by-1 case).
private
  sameLengthᵇ-cons-cons : ∀ {A : Set} (x y : A) (l : List A)
    → sameLengthᵇ (x ∷ y ∷ l) l ≡ false
  sameLengthᵇ-cons-cons x y []       = refl
  sameLengthᵇ-cons-cons x y (z ∷ zs) = sameLengthᵇ-cons-cons y z zs

-- ============================================================================
-- `manyHelper parseStringChar` workhorse
-- ============================================================================
--
-- Mirrors `manyHelper-satisfy-exhaust` (DecRatParse/Properties) but
-- for the two-branch `parseStringChar` parser.  Induction on `cs + n`;
-- each step case-splits on `c ≟ᶜ '"'` and discharges the `sameLengthᵇ`
-- progress check via `sameLengthᵇ-cons` (literal) or `-cons-cons`
-- (escape).

-- Mutual-recursion structure: the `'"' ∷ cs'` clause directly recurses
-- (shrinking `cs'`); the `(c ∷ cs')` catch-all's `yes refl` branch can't
-- structurally shrink from `(c ∷ cs')` to `('"' ∷ cs')` (same list),
-- so it delegates to a named helper `-escape-step` that recurses on the
-- strictly smaller tail.

private
  manyHelper-parseStringChar-exhaust-escape-step :
    ∀ (pos : Position) (cs' : List Char) (suffix : List Char) (n' : ℕ)
    → SuffixStops (λ c → c ≈ᵇ '"') suffix
    → length cs' ≤ n'
    → manyHelper parseStringChar pos
        ('"' ∷ '"' ∷ escape-body-chars cs' ++ₗ '"' ∷ suffix) (suc n')
      ≡ just (mkResult ('"' ∷ cs')
               (advancePositions pos
                  ('"' ∷ '"' ∷ escape-body-chars cs'))
               ('"' ∷ suffix))

manyHelper-parseStringChar-exhaust :
  ∀ (pos : Position) (cs : List Char) (suffix : List Char) (n : ℕ)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → length cs ≤ n
  → manyHelper parseStringChar pos
      (escape-body-chars cs ++ₗ '"' ∷ suffix) n
    ≡ just (mkResult cs
             (advancePositions pos (escape-body-chars cs))
             ('"' ∷ suffix))
manyHelper-parseStringChar-exhaust pos [] suffix zero     _  _         = refl
manyHelper-parseStringChar-exhaust pos [] suffix (suc n') ss _
  rewrite parseStringChar-fail-at-close pos suffix ss = refl
manyHelper-parseStringChar-exhaust pos ('"' ∷ cs') suffix (suc n') ss (s≤s len≤) =
  manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
manyHelper-parseStringChar-exhaust pos (c ∷ cs') suffix (suc n') ss (s≤s len≤)
  with c ≟ᶜ '"'
... | yes refl =
      manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
... | no c≢quote
  rewrite parseStringChar-literal pos c
            (escape-body-chars cs' ++ₗ '"' ∷ suffix) c≢quote
        | sameLengthᵇ-cons c (escape-body-chars cs' ++ₗ '"' ∷ suffix)
        | manyHelper-parseStringChar-exhaust
            (advancePosition pos c) cs' suffix n' ss len≤
  = refl

manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
  rewrite sameLengthᵇ-cons-cons '"' '"' (escape-body-chars cs' ++ₗ '"' ∷ suffix)
        | manyHelper-parseStringChar-exhaust
            (advancePosition (advancePosition pos '"') '"') cs' suffix n' ss len≤
  = refl

-- ============================================================================
-- parseStringLit roundtrip
-- ============================================================================
--
-- Compose: opening `"` via `char-matches`, body via
-- `manyHelper-parseStringChar-exhaust` specialised at `length input`
-- fuel, closing `"` via `char-matches`, final `pure cs` (post-3d.4 +
-- JSON-mirror, `parseStringLit : Parser (List Char)` returns the body
-- chars directly — no `fromList`, no `fromList∘toList` axiom).

-- Length bound: each char in `cs` contributes ≥ 1 char to
-- `escape-body-chars cs`.  Induction on `cs`; the mutual-recursion
-- trick sidesteps the overlapping `'"' ∷ cs'` / `(c ∷ cs')` clauses.
private
  length-cs-≤-escape-body : ∀ (cs : List Char)
    → length cs ≤ length (escape-body-chars cs)

  length-cs-≤-escape-body-escape-step : ∀ (cs : List Char)
    → suc (length cs) ≤ suc (suc (length (escape-body-chars cs)))
  length-cs-≤-escape-body-escape-step cs =
    m≤n⇒m≤1+n (s≤s (length-cs-≤-escape-body cs))

  length-cs-≤-escape-body [] = z≤n
  length-cs-≤-escape-body ('"' ∷ cs) =
    length-cs-≤-escape-body-escape-step cs
  length-cs-≤-escape-body (c ∷ cs) with c ≟ᶜ '"'
  ... | yes refl = length-cs-≤-escape-body-escape-step cs
  ... | no c≢quote = s≤s (length-cs-≤-escape-body cs)

-- ============================================================================
-- parseStringLit roundtrip — composition
-- ============================================================================

parseStringLit-roundtrip : ∀ (pos : Position) (cs : List Char) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → parseStringLit pos (quoteStringLit-chars cs ++ₗ suffix)
    ≡ just (mkResult cs
             (advancePositions pos (quoteStringLit-chars cs)) suffix)
parseStringLit-roundtrip pos cs suffix ss =
  trans (cong (λ input → parseStringLit pos (input ++ₗ suffix))
              (quoteStringLit-chars-shape cs))
    (trans input-shape-adjust
      (trans step-open-quote
        (trans step-many
          (trans step-close-quote step-pure))))
  where
    body-chars : List Char
    body-chars = escape-body-chars cs

    rest-after-open : List Char
    rest-after-open = body-chars ++ₗ '"' ∷ suffix

    pos1 : Position
    pos1 = advancePosition pos '"'

    pos2 : Position
    pos2 = advancePositions pos1 body-chars

    pos3 : Position
    pos3 = advancePosition pos2 '"'

    -- After the shape-rewrite, `(quoteStringLit-chars cs) ++ₗ suffix`
    -- needs one `++ₗ-assoc` to fold the nested append into the form
    -- `'"' ∷ body-chars ++ₗ '"' ∷ suffix`.
    input-shape-adjust :
      parseStringLit pos
        (('"' ∷ body-chars ++ₗ '"' ∷ []) ++ₗ suffix)
      ≡ parseStringLit pos ('"' ∷ body-chars ++ₗ '"' ∷ suffix)
    input-shape-adjust =
      cong (λ xs → parseStringLit pos ('"' ∷ xs))
           (++ₗ-assoc body-chars ('"' ∷ []) suffix)

    step-open-quote :
      parseStringLit pos ('"' ∷ body-chars ++ₗ '"' ∷ suffix)
      ≡ (many parseStringChar >>= λ chars →
           char '"' >>= λ _ → pure chars)
          pos1 rest-after-open
    step-open-quote =
      bind-just-step (char '"')
        (λ _ → many parseStringChar >>= λ chars →
               char '"' >>= λ _ → pure chars)
        pos ('"' ∷ rest-after-open)
        '"' pos1 rest-after-open
        (char-matches '"' pos rest-after-open)

    many-success :
      many parseStringChar pos1 rest-after-open
      ≡ just (mkResult cs pos2 ('"' ∷ suffix))
    many-success =
      manyHelper-parseStringChar-exhaust pos1 cs suffix
        (length rest-after-open) ss len-bound
      where
        open import Data.List.Properties
          using () renaming (length-++ to length-++ₗ-prop)

        len-bound : length cs ≤ length rest-after-open
        len-bound =
          ≤-trans (length-cs-≤-escape-body cs)
            (subst (λ n → length body-chars ≤ n)
                   (sym (length-++ₗ-prop body-chars {'"' ∷ suffix}))
                   (m≤m+n (length body-chars) (length ('"' ∷ suffix))))

    step-many :
      (many parseStringChar >>= λ chars →
         char '"' >>= λ _ → pure chars)
        pos1 rest-after-open
      ≡ (char '"' >>= λ _ → pure cs)
          pos2 ('"' ∷ suffix)
    step-many =
      bind-just-step (many parseStringChar)
        (λ chars → char '"' >>= λ _ → pure chars)
        pos1 rest-after-open
        cs pos2 ('"' ∷ suffix)
        many-success

    step-close-quote :
      (char '"' >>= λ _ → pure cs)
        pos2 ('"' ∷ suffix)
      ≡ pure cs pos3 suffix
    step-close-quote =
      bind-just-step (char '"')
        (λ _ → pure cs)
        pos2 ('"' ∷ suffix)
        '"' pos3 suffix
        (char-matches '"' pos2 suffix)

    step-pure :
      pure cs pos3 suffix
      ≡ just (mkResult cs
               (advancePositions pos (quoteStringLit-chars cs))
               suffix)
    step-pure = cong (λ p → just (mkResult cs p suffix)) pos3-eq
      where
        -- `pos3 ≡ advancePositions pos (quoteStringLit-chars cs)` by
        -- walking the shape.  `advancePositions` over a cons: advance
        -- one char, then recurse; over `++ₗ`, `advancePositions pos
        -- (xs ++ ys) ≡ advancePositions (advancePositions pos xs) ys`.
        pos3-eq : pos3
          ≡ advancePositions pos (quoteStringLit-chars cs)
        pos3-eq =
          trans (sym (advancePositions-++
                        (advancePositions pos1 body-chars)
                        ('"' ∷ []) []))
            (trans (sym (advancePositions-++ pos1 body-chars ('"' ∷ [])))
              (cong (advancePositions pos)
                    (sym (quoteStringLit-chars-shape cs))))

-- ============================================================================
-- Tier B — mux marker roundtrip
-- ============================================================================
--
-- Three emission shapes from `emitMuxMarker-chars`:
--   * `[]`              — NotMux (two sources: nothing-master + Always,
--                         and just-master but thisName ≠ master)
--   * `toList " M"`     — IsMux
--   * `toList " m" ++ₗ showℕ-dec-chars v`
--                       — SelBy v
--
-- Separate roundtrip theorems per emission shape.  Layer 3 will compose
-- them against the emitter's case-split on `(master, thisName, presence)`.

-- IsMux: " M" emission.  `parseWS` consumes the single space
-- (precondition: suffix doesn't start with horizontal space so parseWS
-- doesn't over-consume), then `char 'M'` matches definitionally.

-- The `SuffixStops isHSpace suffix` precondition is structurally
-- unnecessary — the proof's internal `parseWS-one-space` discharges
-- against the FIRST character of the inner input (`'M' ∷ suffix`),
-- whose stop predicate `isHSpace 'M' ≡ false` is closed.  Required by
-- the SG_ mux roundtrip (3d.3) where the post-mux suffix is `" : ..."`
-- (starts with hspace), making the original precondition unprovable.
parseMuxMarker-IsMux-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → parseMuxMarker pos (toList " M" ++ₗ suffix)
    ≡ just (mkResult IsMux (advancePositions pos (toList " M")) suffix)
parseMuxMarker-IsMux-roundtrip pos suffix =
  alt-left-just left-branch (pure NotMux) pos
    (' ' ∷ 'M' ∷ suffix) _ step-left
  where
    pos1 : Position
    pos1 = advancePosition pos ' '

    inner : Parser MuxMarker
    inner = (char 'M' *> pure IsMux) <|>
            (char 'm' *> parseNatural >>= λ n →
              (char 'M' *> pure (BothMux n)) <|>
              pure (SelBy n))

    left-branch : Parser MuxMarker
    left-branch = parseWS *> inner

    step-parseWS :
      left-branch pos (' ' ∷ 'M' ∷ suffix)
      ≡ inner pos1 ('M' ∷ suffix)
    step-parseWS =
      bind-just-step parseWS (λ _ → inner)
        pos (' ' ∷ 'M' ∷ suffix)
        (' ' ∷ []) pos1 ('M' ∷ suffix)
        (parseWS-one-space pos ('M' ∷ suffix) (∷-stop refl))

    -- inner reduces on closed 'M' definitionally: char 'M' succeeds,
    -- `pure IsMux` at the advanced position.
    step-inner :
      inner pos1 ('M' ∷ suffix)
      ≡ just (mkResult IsMux (advancePosition pos1 'M') suffix)
    step-inner = refl

    step-left : left-branch pos (' ' ∷ 'M' ∷ suffix)
      ≡ just (mkResult IsMux
               (advancePositions pos (toList " M")) suffix)
    step-left = trans step-parseWS step-inner

-- NotMux: empty emission.  Precondition exposes the whole left branch
-- of parseMuxMarker's `<|>`; Layer 3 discharges it by computing through
-- parseWS + char M / char m failures on the grammar's specific
-- successor characters (e.g. `" :"` for SG_, `" ;"` for EV_).

parseMuxMarker-left-branch : Parser MuxMarker
parseMuxMarker-left-branch =
  parseWS *>
    ((char 'M' *> pure IsMux) <|>
     (char 'm' *> parseNatural >>= λ n →
       (char 'M' *> pure (BothMux n)) <|>
       pure (SelBy n)))

parseMuxMarker-NotMux-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → parseMuxMarker-left-branch pos suffix ≡ nothing
  → parseMuxMarker pos suffix ≡ just (mkResult NotMux pos suffix)
parseMuxMarker-NotMux-roundtrip pos suffix eq =
  alt-right-nothing parseMuxMarker-left-branch (pure NotMux) pos suffix eq

-- SelBy: " m<digits>" emission.  Preconditions:
--   * `SuffixStops isHSpace suffix` — parseWS consumes the single leading
--     space, stops at `'m'`.  (Precondition applies to the `suffix`
--     *after* the digit string, but the proof threads `SuffixStops`
--     through the intermediate stages via its structural form.)
--   * `SuffixStops isDigit suffix` — parseNatural stops at the end of
--     the emitted digits, not consuming into `suffix`.
--   * `SuffixStops (λ c → c ≈ᵇ 'M') suffix` — the BothMux branch doesn't
--     fire (suffix doesn't begin with `'M'`).

parseMuxMarker-SelBy-roundtrip : ∀ (pos : Position) (v : ℕ) (suffix : List Char)
  → SuffixStops isDigit suffix
  → SuffixStops (λ c → c ≈ᵇ 'M') suffix
  → parseMuxMarker pos
      (toList " m" ++ₗ showℕ-dec-chars v ++ₗ suffix)
    ≡ just (mkResult (SelBy v)
             (advancePositions pos
                (toList " m" ++ₗ showℕ-dec-chars v))
             suffix)
parseMuxMarker-SelBy-roundtrip pos v suffix digit-stop m-stop =
  alt-left-just left-branch (pure NotMux) pos
    (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
    _ step-left
  where
    pos1 : Position
    pos1 = advancePosition pos ' '

    pos2 : Position
    pos2 = advancePosition pos1 'm'

    pos3 : Position
    pos3 = advancePositions pos2 (showℕ-dec-chars v)

    inner : Parser MuxMarker
    inner = (char 'M' *> pure IsMux) <|>
            (char 'm' *> parseNatural >>= λ n →
              (char 'M' *> pure (BothMux n)) <|>
              pure (SelBy n))

    left-branch : Parser MuxMarker
    left-branch = parseWS *> inner

    pos-eq : pos3 ≡ advancePositions pos
                     (toList " m" ++ₗ showℕ-dec-chars v)
    pos-eq =
      sym (advancePositions-++ pos (toList " m") (showℕ-dec-chars v))

    -- char 'M' on suffix returns `nothing`.  Establish this once at the
    -- top by direct pattern-match on `m-stop`.
    char-M-fail : char 'M' pos3 suffix ≡ nothing
    char-M-fail = char-M-fail-helper suffix m-stop
      where
        char-M-fail-helper : ∀ (xs : List Char)
          → SuffixStops (λ c → c ≈ᵇ 'M') xs
          → char 'M' pos3 xs ≡ nothing
        char-M-fail-helper [] []-stop = refl
        char-M-fail-helper (c ∷ _) (∷-stop m-false) rewrite m-false = refl

    step-parseWS :
      left-branch pos
        (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
      ≡ inner pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
    step-parseWS =
      bind-just-step parseWS (λ _ → inner)
        pos (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
        (' ' ∷ []) pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
        (parseWS-one-space pos ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
           (∷-stop refl))

    step-char-m :
      inner pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
      ≡ (parseNatural >>= λ n →
          (char 'M' *> pure (BothMux n)) <|>
          pure (SelBy n))
          pos2 (showℕ-dec-chars v ++ₗ suffix)
    step-char-m = refl

    step-parseNat :
      (parseNatural >>= λ n →
        (char 'M' *> pure (BothMux n)) <|>
        pure (SelBy n))
        pos2 (showℕ-dec-chars v ++ₗ suffix)
      ≡ ((char 'M' *> pure (BothMux v)) <|> pure (SelBy v))
          pos3 suffix
    step-parseNat =
      bind-just-step parseNatural
        (λ n → (char 'M' *> pure (BothMux n)) <|> pure (SelBy n))
        pos2 (showℕ-dec-chars v ++ₗ suffix)
        v pos3 suffix
        (parseNatural-showNat-chars pos2 v suffix digit-stop)

    step-selby :
      ((char 'M' *> pure (BothMux v)) <|> pure (SelBy v))
        pos3 suffix
      ≡ just (mkResult (SelBy v)
               (advancePositions pos
                  (toList " m" ++ₗ showℕ-dec-chars v))
               suffix)
    step-selby =
      trans (alt-right-nothing (char 'M' *> pure (BothMux v))
                               (pure (SelBy v)) pos3 suffix
              (bind-nothing (char 'M') _ pos3 suffix char-M-fail))
            (cong (λ p → just (mkResult (SelBy v) p suffix)) pos-eq)

    step-left : left-branch pos
                  (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
                ≡ just (mkResult (SelBy v)
                         (advancePositions pos
                            (toList " m" ++ₗ showℕ-dec-chars v))
                         suffix)
    step-left = trans step-parseWS
                  (trans step-char-m
                    (trans step-parseNat step-selby))
