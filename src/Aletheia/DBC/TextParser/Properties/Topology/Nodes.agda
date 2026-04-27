{-# OPTIONS --safe --without-K #-}

-- `parseBU-roundtrip` — per-line-construct roundtrip for the
-- `BU_: <node>*` DBC node-list line (B.3.d Layer 3 Commit 3b).
--
-- Bind chain (matches `Aletheia.DBC.TextParser.Topology.parseBU`):
--
--   string "BU_" *> parseWSOpt *> char ':' *>
--   many (parseWS *> parseIdentifier) >>= λ names →
--   parseWSOpt *> parseNewline *>
--   many parseNewline *>
--   pure (map mkNode names)
--
-- The body `many (parseWS *> parseIdentifier)` is the new ingredient
-- compared with the Preamble constructs (3a): each iteration consumes
-- a leading single-space separator + one identifier, and the
-- iteration terminates when the next char is `'\n'` (parseWS fails
-- since `\n` isn't horizontal whitespace).
--
-- The map-mkNode-after-projection witness is closed via η on the
-- single-field `Node` record (`mkNode (Node.name n) ≡ n`), proven by
-- induction on the list under `--without-K`.
module Aletheia.DBC.TextParser.Properties.Topology.Nodes where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n; m≤m+n; m≤n+m; +-suc)
open import Data.List.Properties using (length-++) renaming (++-assoc to ++ₗ-assoc)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   sameLengthᵇ; pure; _>>=_; _*>_; string; char; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.Topology using (parseBU)
open import Aletheia.DBC.TextFormatter.Topology using (emitBU-chars)
open import Aletheia.DBC.Types using (Node; mkNode)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; sameLengthᵇ-cons; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; char-matches; parseWS-one-space;
   parseIdentifier-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF; many-parseNewline-one-LF-stop;
   manyHelper-prog-cons)

-- ============================================================================
-- Body decomposition: nodeNameSep-chars
-- ============================================================================

-- The names section of the BU_ body — one ` <name>` group per node,
-- *without* the trailing `\n\n`.  Pulling the trailer out keeps the
-- inductive proof on `ns` clean: the `many` body consumes exactly
-- `nodeNameSep-chars`, then the rest of the parser handles `\n\n`.
nodeNameSep-chars : List Node → List Char
nodeNameSep-chars []       = []
nodeNameSep-chars (n ∷ ns) =
  ' ' ∷ Identifier.name (Node.name n) ++ₗ nodeNameSep-chars ns

-- Shape lemmas: `emitBU-chars ns` reassociates as the parser consumes
-- it — `"BU_:"` head + `nodeNameSep-chars ns` body + `"\n\n"` tail
-- + outer suffix.
private
  emitBU-chars-foldr-shape : ∀ (ns : List Node)
    → foldr (λ n acc → ' ' ∷ Identifier.name (Node.name n) ++ₗ acc)
            (toList "\n\n") ns
      ≡ nodeNameSep-chars ns ++ₗ toList "\n\n"
  emitBU-chars-foldr-shape [] = refl
  emitBU-chars-foldr-shape (n ∷ ns)
    rewrite emitBU-chars-foldr-shape ns =
      cong (' ' ∷_)
           (sym (++ₗ-assoc (Identifier.name (Node.name n))
                           (nodeNameSep-chars ns)
                           (toList "\n\n")))

  emitBU-chars-shape : ∀ (ns : List Node) (suffix : List Char)
    → emitBU-chars ns ++ₗ suffix
      ≡ toList "BU_"
          ++ₗ ':' ∷ (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix)
  emitBU-chars-shape ns suffix =
    trans (cong (λ body → toList "BU_:" ++ₗ body ++ₗ suffix)
                (emitBU-chars-foldr-shape ns))
      (trans (++ₗ-assoc (toList "BU_:")
                        (nodeNameSep-chars ns ++ₗ toList "\n\n")
                        suffix)
        (cong (toList "BU_:" ++ₗ_)
              (++ₗ-assoc (nodeNameSep-chars ns)
                         (toList "\n\n") suffix)))

-- ============================================================================
-- η for Node — map mkNode (map Node.name ns) ≡ ns
-- ============================================================================

private
  map-mkNode-Node-name : ∀ (ns : List Node)
    → map mkNode (map Node.name ns) ≡ ns
  map-mkNode-Node-name [] = refl
  map-mkNode-Node-name (n ∷ ns) = cong (n ∷_) (map-mkNode-Node-name ns)

-- ============================================================================
-- Per-node validity: explicit non-empty head + non-hspace witness
-- ============================================================================

-- Per-node precondition: each name decomposes as `c ∷ cs` with
-- `isHSpace c ≡ false` (so parseWS stops cleanly after consuming the
-- leading separator space and the `many (satisfy isHSpace)` inner
-- recursion fails on the first identifier char).  Structurally
-- guaranteed for every valid identifier — `validIdentifierᵇ (toList
-- name) ≡ true` implies `length (toList name) ≥ 1` and the first char
-- is `isIdentStart` (alphanumeric / underscore, never whitespace).
-- Here the witness is supplied as a precondition by the caller; the
-- `isIdentStart c → isHSpace c ≡ false` bridge lemma is owed at
-- Layer 4 (universal proof).
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

NodeNameStop : Node → Set
NodeNameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (Node.name n) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- Single-iteration: parseWS *> parseIdentifier on ' ' ∷ toList name ++ ...
-- ============================================================================

private
  parseWSIdent-step :
      ∀ (pos : Position) (n : Node) (rest : List Char)
    → SuffixStops isHSpace (Identifier.name (Node.name n) ++ₗ rest)
    → SuffixStops isIdentCont rest
    → (parseWS *> parseIdentifier) pos
        (' ' ∷ Identifier.name (Node.name n) ++ₗ rest)
      ≡ just (mkResult (Node.name n)
               (advancePositions
                  (advancePosition pos ' ')
                  (Identifier.name (Node.name n)))
               rest)
  parseWSIdent-step pos n rest ws-ss ident-ss =
    trans
      (bind-just-step parseWS (λ _ → parseIdentifier)
         pos (' ' ∷ Identifier.name (Node.name n) ++ₗ rest)
         (' ' ∷ []) (advancePosition pos ' ')
         (Identifier.name (Node.name n) ++ₗ rest)
         (parseWS-one-space pos
            (Identifier.name (Node.name n) ++ₗ rest)
            ws-ss))
      (parseIdentifier-roundtrip
         (advancePosition pos ' ')
         (Node.name n)
         rest
         ident-ss)

-- ============================================================================
-- many termination: parseWS *> parseIdentifier fails on '\n' input
-- ============================================================================

private
  manyHelper-parseWSIdent-stop-LF :
      ∀ (pos : Position) (rest : List Char) (m : ℕ)
    → manyHelper (parseWS *> parseIdentifier) pos ('\n' ∷ rest) m
      ≡ just (mkResult [] pos ('\n' ∷ rest))
  manyHelper-parseWSIdent-stop-LF _ _ zero    = refl
  manyHelper-parseWSIdent-stop-LF _ _ (suc _) = refl

-- ============================================================================
-- Inductive: many parses out all node names, then stops at '\n'
-- ============================================================================

-- Per-iteration progress witness — the input `' ' ∷ toList name ++ rest`
-- is strictly longer than `rest` (it has at least one extra char).
private
  -- Generic: `length ys < length xs → sameLengthᵇ xs ys ≡ false`.
  -- Stronger than `sameLengthᵇ-cons` (covers arbitrary-length prefix).
  -- Mirrors `Namespace.sameLengthᵇ-lt`; duplicated here as that one is
  -- private to its module.  Lift to a shared location when more
  -- Layer-3 constructs need it.
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys < length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (_ ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  sameLengthᵇ-name-iter-fail : ∀ (n : Node) (rest : List Char)
    → sameLengthᵇ (' ' ∷ Identifier.name (Node.name n) ++ₗ rest) rest ≡ false
  sameLengthᵇ-name-iter-fail n rest =
    sameLengthᵇ-lt (' ' ∷ Identifier.name (Node.name n) ++ₗ rest) rest len-witness
    where
      len-witness : length rest < length (' ' ∷ Identifier.name (Node.name n) ++ₗ rest)
      len-witness
        rewrite length-++ (Identifier.name (Node.name n)) {rest} =
          s≤s (m≤n+m (length rest) (length (Identifier.name (Node.name n))))

-- After consuming `nodeNameSep-chars ns`, the cursor advances by
-- `nodeNameSep-chars ns` chars from the starting position.
afterNodes : Position → List Node → Position
afterNodes pos []       = pos
afterNodes pos (n ∷ ns) =
  afterNodes (advancePositions
                (advancePosition pos ' ')
                (Identifier.name (Node.name n))) ns

-- The advancePositions / afterNodes alignment lemma — the position
-- after walking `nodeNameSep-chars ns` from `pos` equals
-- `afterNodes pos ns`.  Definitionally: `advancePositions pos (' ' ∷
-- xs) = advancePositions (advancePosition pos ' ') xs`, so the cons
-- case folds into the IH + one `advancePositions-++` step.
private
  afterNodes-advancePositions : ∀ (pos : Position) (ns : List Node)
    → afterNodes pos ns ≡ advancePositions pos (nodeNameSep-chars ns)
  afterNodes-advancePositions pos []       = refl
  afterNodes-advancePositions pos (n ∷ ns) =
    trans
      (afterNodes-advancePositions
         (advancePositions (advancePosition pos ' ')
                           (Identifier.name (Node.name n)))
         ns)
      (sym (advancePositions-++
              (advancePosition pos ' ')
              (Identifier.name (Node.name n))
              (nodeNameSep-chars ns)))

-- Body iteration — manyHelper consumes `nodeNameSep-chars ns ++ '\n' ∷
-- '\n' ∷ suffix` and leaves `'\n' ∷ '\n' ∷ suffix`, returning
-- `map Node.name ns`.  Fuel `m ≥ length ns`.
manyHelper-parseWSIdent-body :
    ∀ (pos : Position) (ns : List Node) (suffix : List Char) (m : ℕ)
  → All NodeNameStop ns
  → length ns ≤ m
  → manyHelper (parseWS *> parseIdentifier) pos
      (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix) m
    ≡ just (mkResult (map Node.name ns)
             (afterNodes pos ns)
             ('\n' ∷ '\n' ∷ suffix))
manyHelper-parseWSIdent-body pos []       suffix m _ _ =
  manyHelper-parseWSIdent-stop-LF pos ('\n' ∷ suffix) m
manyHelper-parseWSIdent-body pos (n ∷ ns) suffix (suc m')
    (n-stop ∷ rest-stops) (s≤s len-le) =
  let
    -- One iteration: consume ` <name>`, leave the rest of the body.
    iter-rest = nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix
    pos-after-name = advancePositions
                       (advancePosition pos ' ')
                       (Identifier.name (Node.name n))
    -- SuffixStops isIdentCont on the post-name input — head is either
    -- `' '` (start of next iteration's separator) or `'\n'` (body
    -- terminator).  Both have isIdentCont ≡ false.
    iter-rest-ss : SuffixStops isIdentCont iter-rest
    iter-rest-ss = nodeNameSep-isIdentCont-stop ns suffix
    -- SuffixStops isHSpace `(toList name ++ iter-rest)` — head is
    -- the first char of the name (non-hspace by precondition).
    full-rest-ss : SuffixStops isHSpace
                     (Identifier.name (Node.name n) ++ₗ iter-rest)
    full-rest-ss = name-stop-extends n iter-rest n-stop
    iter-eq :
      (parseWS *> parseIdentifier) pos
        (' ' ∷ Identifier.name (Node.name n) ++ₗ iter-rest)
      ≡ just (mkResult (Node.name n) pos-after-name iter-rest)
    iter-eq = parseWSIdent-step pos n iter-rest full-rest-ss iter-rest-ss
    -- Recursive call on the tail.
    rec-eq = manyHelper-parseWSIdent-body
               pos-after-name ns suffix m' rest-stops len-le
    -- Reshape ` <name> ++ tail-body ++ '\n\n suffix' ≡ ' ∷ name ++
    -- (tail-body ++ '\n\n suffix)`.  Closed by ++-assoc.
    shape-eq :
      nodeNameSep-chars (n ∷ ns) ++ₗ '\n' ∷ '\n' ∷ suffix
      ≡ ' ' ∷ Identifier.name (Node.name n) ++ₗ iter-rest
    shape-eq =
      cong (_∷_ ' ')
        (++ₗ-assoc (Identifier.name (Node.name n))
                   (nodeNameSep-chars ns)
                   ('\n' ∷ '\n' ∷ suffix))
  in
    trans
      (cong (λ input →
                manyHelper (parseWS *> parseIdentifier) pos input (suc m'))
            shape-eq)
      (manyHelper-prog-cons (parseWS *> parseIdentifier) pos
        (' ' ∷ Identifier.name (Node.name n) ++ₗ iter-rest) m'
        (Node.name n) pos-after-name iter-rest
        (map Node.name ns)
        (afterNodes pos-after-name ns)
        ('\n' ∷ '\n' ∷ suffix)
        iter-eq
        (sameLengthᵇ-name-iter-fail n iter-rest)
        rec-eq)
  where
    -- The post-`many`-body input is `nodeNameSep-chars ns ++ '\n\n'
    -- ∷ suffix`.  Its head is `' '` if `ns ≢ []`, `'\n'` otherwise.
    -- Both have `isIdentCont c ≡ false`.
    nodeNameSep-isIdentCont-stop : ∀ (ns : List Node) (suffix : List Char)
      → SuffixStops isIdentCont
          (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix)
    nodeNameSep-isIdentCont-stop []        suffix = ∷-stop refl
    nodeNameSep-isIdentCont-stop (n' ∷ _)  _      = ∷-stop refl

    -- Decompose `NodeNameStop n` to a `SuffixStops isHSpace (toList
    -- name ++ rest)` — head of `toList name` decomposes to `c ∷ cs`
    -- via `name-eq`, and `isHSpace c ≡ false` discharges the stop.
    name-stop-extends : ∀ (n : Node) (rest : List Char)
      → NodeNameStop n
      → SuffixStops isHSpace (Identifier.name (Node.name n) ++ₗ rest)
    name-stop-extends n rest (c , cs , name-eq , c-non-hspace) =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym name-eq)
            (∷-stop c-non-hspace)

-- ============================================================================
-- Main theorem: parseBU-roundtrip
-- ============================================================================

parseBU-roundtrip :
    ∀ (pos : Position) (ns : List Node) (suffix : List Char)
  → All NodeNameStop ns
  → SuffixStops isNewlineStart suffix
  → parseBU pos (emitBU-chars ns ++ₗ suffix)
    ≡ just (mkResult ns
             (advancePositions pos (emitBU-chars ns))
             suffix)
parseBU-roundtrip pos ns suffix node-stops nl-stop =
  trans (cong (parseBU pos) (emitBU-chars-shape ns suffix))
    (trans step-BU_
      (trans step-parseWSOpt
        (trans step-char-colon
          (trans step-many-body
            (trans step-parseWSOpt-2
              (trans step-parseNewline
                (trans step-many-parseNewline
                  step-pure)))))))
  where
    -- Intermediate positions.
    pos-bu : Position
    pos-bu = advancePositions pos (toList "BU_")

    pos-colon : Position
    pos-colon = advancePosition pos-bu ':'

    pos-after-body : Position
    pos-after-body = afterNodes pos-colon ns

    pos-lf1 : Position
    pos-lf1 = advancePosition pos-after-body '\n'

    pos-lf2 : Position
    pos-lf2 = advancePosition pos-lf1 '\n'

    -- Intermediate inputs.
    rest-after-BU_ : List Char
    rest-after-BU_ =
      ':' ∷ (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix)

    rest-after-WSOpt-1 : List Char
    rest-after-WSOpt-1 = rest-after-BU_

    rest-after-colon : List Char
    rest-after-colon = nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ suffix

    rest-after-body : List Char
    rest-after-body = '\n' ∷ '\n' ∷ suffix

    rest-after-WSOpt-2 : List Char
    rest-after-WSOpt-2 = rest-after-body

    rest-after-LF1 : List Char
    rest-after-LF1 = '\n' ∷ suffix

    -- Parser continuations after each bind.
    cont-after-BU_ : String → Parser (List Node)
    cont-after-BU_ _ =
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      many (parseWS *> parseIdentifier) >>= λ names →
      parseWSOpt *> parseNewline *>
      many parseNewline *>
      pure (map mkNode names)

    cont-after-WSOpt-1 : List Char → Parser (List Node)
    cont-after-WSOpt-1 _ =
      char ':' >>= λ _ →
      many (parseWS *> parseIdentifier) >>= λ names →
      parseWSOpt *> parseNewline *>
      many parseNewline *>
      pure (map mkNode names)

    cont-after-colon : Char → Parser (List Node)
    cont-after-colon _ =
      many (parseWS *> parseIdentifier) >>= λ names →
      parseWSOpt *> parseNewline *>
      many parseNewline *>
      pure (map mkNode names)

    cont-after-body : List Identifier → Parser (List Node)
    cont-after-body names =
      parseWSOpt *> parseNewline *>
      many parseNewline *>
      pure (map mkNode names)

    cont-after-WSOpt-2 : List Char → Parser (List Node)
    cont-after-WSOpt-2 _ =
      parseNewline *>
      many parseNewline *>
      pure (map mkNode (map Node.name ns))

    cont-after-LF1 : Char → Parser (List Node)
    cont-after-LF1 _ =
      many parseNewline *>
      pure (map mkNode (map Node.name ns))

    cont-after-manyLF : List Char → Parser (List Node)
    cont-after-manyLF _ = pure (map mkNode (map Node.name ns))

    -- Step 1: consume "BU_".
    step-BU_ :
      parseBU pos (toList "BU_" ++ₗ rest-after-BU_)
      ≡ cont-after-BU_ "BU_" pos-bu rest-after-BU_
    step-BU_ =
      bind-just-step (string "BU_")
                     cont-after-BU_
                     pos (toList "BU_" ++ₗ rest-after-BU_)
                     "BU_" pos-bu rest-after-BU_
                     (string-success pos "BU_" rest-after-BU_)

    -- Step 2: parseWSOpt consumes 0 hspace (next is ':').
    wsopt1-ss : SuffixStops isHSpace rest-after-WSOpt-1
    wsopt1-ss = ∷-stop refl

    step-parseWSOpt :
      cont-after-BU_ "BU_" pos-bu rest-after-BU_
      ≡ cont-after-WSOpt-1 [] pos-bu rest-after-WSOpt-1
    step-parseWSOpt =
      bind-just-step parseWSOpt
                     cont-after-WSOpt-1
                     pos-bu rest-after-BU_
                     [] pos-bu rest-after-WSOpt-1
                     (manyHelper-satisfy-exhaust-many isHSpace pos-bu
                        [] rest-after-BU_ All.[] wsopt1-ss)

    -- Step 3: char ':'.
    step-char-colon :
      cont-after-WSOpt-1 [] pos-bu rest-after-WSOpt-1
      ≡ cont-after-colon ':' pos-colon rest-after-colon
    step-char-colon =
      bind-just-step (char ':')
                     cont-after-colon
                     pos-bu rest-after-WSOpt-1
                     ':' pos-colon rest-after-colon
                     (char-matches ':' pos-bu rest-after-colon)

    -- Step 4: many (parseWS *> parseIdentifier) iterates through ns.
    step-many-body :
      cont-after-colon ':' pos-colon rest-after-colon
      ≡ cont-after-body (map Node.name ns) pos-after-body rest-after-body
    step-many-body =
      bind-just-step (many (parseWS *> parseIdentifier))
                     cont-after-body
                     pos-colon rest-after-colon
                     (map Node.name ns) pos-after-body rest-after-body
                     (manyHelper-parseWSIdent-body
                        pos-colon ns suffix
                        (length rest-after-colon)
                        node-stops
                        body-fuel-bound)
      where
        -- Fuel `length rest-after-colon = length (nodeNameSep-chars ns)
        -- + 2 + length suffix`.  Need `length ns ≤ that`.  Each Node
        -- contributes at least 1 char (the leading space), so
        -- `length ns ≤ length (nodeNameSep-chars ns)` always; combined
        -- with `≤-trans m≤m+n` covers the rest.
        body-fuel-bound : length ns ≤ length rest-after-colon
        body-fuel-bound
          rewrite length-++ (nodeNameSep-chars ns)
                            {'\n' ∷ '\n' ∷ suffix} =
            ≤-trans
              (length-ns-le-nodeNameSep ns)
              (m≤m+n (length (nodeNameSep-chars ns))
                     (length ('\n' ∷ '\n' ∷ suffix)))
          where
            length-ns-le-nodeNameSep : ∀ (ns : List Node)
              → length ns ≤ length (nodeNameSep-chars ns)
            length-ns-le-nodeNameSep []       = z≤n
            length-ns-le-nodeNameSep (n ∷ ns') =
              s≤s
                (≤-trans
                   (length-ns-le-nodeNameSep ns')
                   (le-monotone-++
                      (Identifier.name (Node.name n))
                      (nodeNameSep-chars ns')))
              where
                le-monotone-++ : ∀ (xs ys : List Char)
                  → length ys ≤ length (xs ++ₗ ys)
                le-monotone-++ []        ys = ≤-refl
                le-monotone-++ (x ∷ xs') ys =
                  ≤-trans (le-monotone-++ xs' ys) (n≤1+n _)

    -- Step 5: parseWSOpt-2 consumes 0 hspace (next is '\n').
    wsopt2-ss : SuffixStops isHSpace rest-after-body
    wsopt2-ss = ∷-stop refl

    step-parseWSOpt-2 :
      cont-after-body (map Node.name ns) pos-after-body rest-after-body
      ≡ cont-after-WSOpt-2 [] pos-after-body rest-after-WSOpt-2
    step-parseWSOpt-2 =
      bind-just-step parseWSOpt
                     cont-after-WSOpt-2
                     pos-after-body rest-after-body
                     [] pos-after-body rest-after-WSOpt-2
                     (manyHelper-satisfy-exhaust-many isHSpace pos-after-body
                        [] rest-after-body All.[] wsopt2-ss)

    -- Step 6: parseNewline matches first '\n'.
    step-parseNewline :
      cont-after-WSOpt-2 [] pos-after-body rest-after-WSOpt-2
      ≡ cont-after-LF1 '\n' pos-lf1 rest-after-LF1
    step-parseNewline =
      bind-just-step parseNewline
                     cont-after-LF1
                     pos-after-body rest-after-WSOpt-2
                     '\n' pos-lf1 rest-after-LF1
                     (parseNewline-match-LF pos-after-body
                        ('\n' ∷ suffix))

    -- Step 7: many parseNewline matches second '\n', then stops.
    step-many-parseNewline :
      cont-after-LF1 '\n' pos-lf1 rest-after-LF1
      ≡ cont-after-manyLF ('\n' ∷ []) pos-lf2 suffix
    step-many-parseNewline =
      bind-just-step (many parseNewline)
                     cont-after-manyLF
                     pos-lf1 rest-after-LF1
                     ('\n' ∷ []) pos-lf2 suffix
                     (many-parseNewline-one-LF-stop
                        pos-lf1 suffix (length suffix) nl-stop)

    -- Step 8: pure (map mkNode (map Node.name ns)) ≡ pure ns by η.
    pos-final-eq : pos-lf2 ≡ advancePositions pos (emitBU-chars ns)
    pos-final-eq =
      trans
        (cong (λ p → advancePosition (advancePosition p '\n') '\n')
              (afterNodes-advancePositions pos-colon ns))
        body-pos-fold
      where
        -- `pos-colon = advancePosition pos-bu ':' = advancePositions pos-bu (':' ∷ [])`.
        -- Combine: `advancePositions pos-colon (nodeNameSep-chars ns)`
        -- = `advancePositions pos-bu (':' ∷ nodeNameSep-chars ns)`
        -- via `advancePositions-++`.  Then absorb the trailing `\n\n`
        -- the same way.  Finally, the head `pos-bu = advancePositions pos
        -- (toList "BU_")` lifts to `advancePositions pos (toList "BU_:" ++
        -- nodeNameSep-chars ns ++ '\n\n')` which is `emitBU-chars ns`.
        body-pos-fold :
          advancePosition (advancePosition
              (advancePositions pos-colon (nodeNameSep-chars ns)) '\n') '\n'
          ≡ advancePositions pos (emitBU-chars ns)
        body-pos-fold =
          trans
            (sym (advancePositions-++
                    (advancePositions pos-colon (nodeNameSep-chars ns))
                    ('\n' ∷ []) ('\n' ∷ [])))
            (trans
              (sym (advancePositions-++
                      pos-colon (nodeNameSep-chars ns)
                      ('\n' ∷ '\n' ∷ [])))
              (trans
                (cong (λ p → advancePositions p
                                (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ []))
                      (sym (advancePositions-++
                              pos-bu (':' ∷ []) [])))
                (trans
                  (sym (advancePositions-++
                          pos-bu (':' ∷ [])
                          (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ [])))
                  (trans
                    (sym (advancePositions-++
                            pos (toList "BU_")
                            (':' ∷ nodeNameSep-chars ns
                                ++ₗ '\n' ∷ '\n' ∷ [])))
                    (cong (advancePositions pos)
                          (emitBU-chars-shape-tail ns))))))
          where
            -- The full input shape (sans outer suffix).  `toList "BU_"
            -- ++ ':' ∷ xs ≡ toList "BU_:" ++ xs` definitionally; the
            -- foldr-shape lemma bridges the trailing `nodeNameSep-chars
            -- ns ++ "\n\n"` to the literal `foldr ... "\n\n" ns` form
            -- inside `emitBU-chars`.
            emitBU-chars-shape-tail : ∀ (ns : List Node)
              → toList "BU_" ++ₗ
                  ':' ∷ (nodeNameSep-chars ns ++ₗ '\n' ∷ '\n' ∷ [])
                ≡ emitBU-chars ns
            emitBU-chars-shape-tail ns =
              cong (toList "BU_:" ++ₗ_) (sym (emitBU-chars-foldr-shape ns))

    step-pure :
      cont-after-manyLF ('\n' ∷ []) pos-lf2 suffix
      ≡ just (mkResult ns
               (advancePositions pos (emitBU-chars ns))
               suffix)
    step-pure =
      trans
        (cong (λ result → just (mkResult result pos-lf2 suffix))
              (map-mkNode-Node-name ns))
        (cong (λ p → just (mkResult ns p suffix)) pos-final-eq)
