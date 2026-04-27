{-# OPTIONS --safe --without-K #-}

-- `parseValueTable-roundtrip` — per-line-construct roundtrip for the
-- DBC `VAL_TABLE_ <name> (<n> "<desc>")* ;` line (B.3.d Layer 3
-- Commit 3b).
--
-- Bind chain (matches `Aletheia.DBC.TextParser.ValueTables.parseValueTable`):
--
--   string "VAL_TABLE_" *> parseWS *>
--   parseIdentifier >>= λ name →
--   many parseValueEntry >>= λ entries →
--   parseWSOpt *> char ';' *> parseNewline *>
--   many parseNewline *>
--   pure (record { name = name ; entries = entries })
--
-- The many-stop on `parseValueEntry` is *partial-failure-then-rollback*:
-- `parseWS` consumes the leading ` ` of the synthesized terminator,
-- then `parseNatural` rejects `;` and the whole bind chain returns
-- `nothing`.  `manyHelper`'s `nothing` arm restores the original
-- input/position, so the per-entry many-loop stops cleanly without
-- consuming any of the trailing ` ;\n` sequence.
module Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_; map; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n; m≤m+n; m≤n+m)
open import Data.List.Properties using (length-++; ++-identityʳ) renaming (++-assoc to ++ₗ-assoc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃₂)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   sameLengthᵇ; pure; _>>=_; _*>_; string; char; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseNatural;
   parseWS; parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.ValueTables using
  (parseValueTable; parseValueEntry)
open import Aletheia.DBC.TextFormatter.ValueTables using
  (emitValueTable-chars; emitValueEntry-chars)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; showNat-chars; quoteStringLit-chars; digitChar)
open import Aletheia.DBC.Types using (ValueTable)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; advancePositions-++;
   parseNatural-showNat-chars; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; char-matches; parseWS-one-space;
   parseIdentifier-roundtrip; parseStringLit-roundtrip;
   quoteStringLit-chars-shape)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF;
   manyHelper-parseNewline-exhaust; manyHelper-prog-cons)

-- ============================================================================
-- Per-table-name precondition (mirrors BU_'s `NodeNameStop`)
-- ============================================================================

-- Each table's `name` decomposes as `c ∷ cs` with `isHSpace c ≡ false`,
-- so `parseWS` between `VAL_TABLE_` and the name stops cleanly after
-- consuming the single separator space.  Layer 4 will discharge this
-- universally from `validIdentifierᵇ` via the `isIdentStart→¬isHSpace`
-- bridge (see `project_b3d_layer4_owed_lemmas.md`).
ValueTableNameStop : ValueTable → Set
ValueTableNameStop vt =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (ValueTable.name vt) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- Char-class disjointness — `digitChar` is never hspace
-- ============================================================================

-- `digitChar d ≡ '0' .. '9'` for `d < 10`; the fallthrough `digitChar
-- _ = '0'` covers `d ≥ 10`.  All ten possible outputs are non-hspace
-- closed-Char terms; `isHSpace` reduces on each via `_≟ᶜ_`'s primitive
-- equality.  Eleven cases mirror `digitChar-≢-dash` in
-- `DecRatParse.Properties`.
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

-- The head of `showNat-chars n ++ rest` is `digitChar k` for some
-- `k < 10`, so its `isHSpace` reduces to `false`.
private
  showNat-chars-head-stop-isHSpace : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops isHSpace (showℕ-dec-chars n ++ₗ rest)
  showNat-chars-head-stop-isHSpace n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

-- The head of `quoteStringLit-chars s ++ rest` is `'"'`, so its
-- `isHSpace` reduces to `false` (and `_≈ᵇ '"'` reduces to `true`).
private
  quoteStringLit-chars-head-isHSpace : ∀ (s : List Char) (rest : List Char)
    → SuffixStops isHSpace (quoteStringLit-chars s ++ₗ rest)
  quoteStringLit-chars-head-isHSpace s rest =
    subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
          (sym (quoteStringLit-chars-shape s))
          (∷-stop refl)

-- ============================================================================
-- Body decomposition: entries-chars
-- ============================================================================

-- The entries section of the body — one ` <n> "<desc>"` group per
-- entry, *without* the trailing ` ;\n` terminator.
entries-chars : List (ℕ × List Char) → List Char
entries-chars []              = []
entries-chars ((v , d) ∷ es)  =
  ' ' ∷ showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars d ++ₗ entries-chars es

-- Shape lemmas: `emitValueTable-chars vt` reassociates as the parser
-- consumes it — `"VAL_TABLE_"` head + `' '` separator + `nm-chars` +
-- `entries-chars es` body + ` ;\n` tail + outer suffix.
private
  emitValueTable-foldr-shape : ∀ (es : List (ℕ × List Char))
    → foldr (λ e acc → emitValueEntry-chars e ++ₗ acc) (toList " ;\n") es
      ≡ entries-chars es ++ₗ toList " ;\n"
  emitValueTable-foldr-shape [] = refl
  emitValueTable-foldr-shape ((v , d) ∷ es)
    rewrite emitValueTable-foldr-shape es =
      cong (' ' ∷_)
        (trans
          (++ₗ-assoc (showℕ-dec-chars v)
                     (' ' ∷ quoteStringLit-chars d)
                     (entries-chars es ++ₗ toList " ;\n"))
          (trans
            (cong (λ x → showℕ-dec-chars v ++ₗ x)
              (cong (' ' ∷_)
                (sym (++ₗ-assoc (quoteStringLit-chars d)
                                (entries-chars es)
                                (toList " ;\n")))))
            (sym (++ₗ-assoc (showℕ-dec-chars v)
                            (' ' ∷ (quoteStringLit-chars d ++ₗ entries-chars es))
                            (toList " ;\n")))))

  emitValueTable-chars-shape : ∀ (vt : ValueTable) (suffix : List Char)
    → emitValueTable-chars vt ++ₗ suffix
      ≡ toList "VAL_TABLE_"
          ++ₗ ' ' ∷ (Identifier.name (ValueTable.name vt) ++ₗ
                       (entries-chars (ValueTable.entries vt) ++ₗ
                          ' ' ∷ ';' ∷ '\n' ∷ suffix))
  emitValueTable-chars-shape vt suffix =
    let es = ValueTable.entries vt
        nm-chars = Identifier.name (ValueTable.name vt)
    in
    -- emitValueTable-chars vt = toList "VAL_TABLE_ " ++ₗ (nm-chars ++ₗ foldr ...)
    -- ⇒ (... ++ₗ suffix) is left-associated at the outer level.
    trans
      (cong (λ body → (toList "VAL_TABLE_ " ++ₗ (nm-chars ++ₗ body)) ++ₗ suffix)
            (emitValueTable-foldr-shape es))
      -- Now: ((TBL ++ NM ++ entries-chars es ++ " ;\n")) ++ suffix
      (trans
        (++ₗ-assoc (toList "VAL_TABLE_ ")
                   (nm-chars ++ₗ entries-chars es ++ₗ toList " ;\n")
                   suffix)
        -- Now: TBL ++ (NM ++ entries-chars es ++ " ;\n") ++ suffix
        -- Expand to: TBL ++ NM ++ entries-chars es ++ " ;\n" ++ suffix
        (trans
          (cong (toList "VAL_TABLE_ " ++ₗ_)
                (++ₗ-assoc nm-chars
                           (entries-chars es ++ₗ toList " ;\n")
                           suffix))
          (trans
            (cong (λ x → toList "VAL_TABLE_ " ++ₗ (nm-chars ++ₗ x))
                  (++ₗ-assoc (entries-chars es)
                             (toList " ;\n") suffix))
            refl)))

-- ============================================================================
-- Per-iteration: parseValueEntry consumes one entry
-- ============================================================================

-- One entry consumes ` <nat> "<desc>"`.  The `SuffixStops (λ c → c ≈ᵇ
-- '"') rest` precondition is on the rest after the closing quote —
-- needed by `parseStringLit-roundtrip`.
private
  parseValueEntry-step :
      ∀ (pos : Position) (v : ℕ) (d : List Char) (rest : List Char)
    → SuffixStops (λ c → c ≈ᵇ '"') rest
    → parseValueEntry pos
        (' ' ∷ showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars d ++ₗ rest)
      ≡ just (mkResult (v , d)
               (advancePositions
                  (advancePosition
                     (advancePositions
                        (advancePosition pos ' ')
                        (showℕ-dec-chars v))
                     ' ')
                  (quoteStringLit-chars d))
               rest)
  parseValueEntry-step pos v d rest rest-quote-ss =
    let pos₁ = advancePosition pos ' '
        pos₂ = advancePositions pos₁ (showℕ-dec-chars v)
        pos₃ = advancePosition pos₂ ' '
        pos₄ = advancePositions pos₃ (quoteStringLit-chars d)
        in₁  = showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars d ++ₗ rest
        in₂  = ' ' ∷ quoteStringLit-chars d ++ₗ rest
        in₃  = quoteStringLit-chars d ++ₗ rest
    in
    trans
      (bind-just-step parseWS
         (λ _ → parseNatural >>= λ v' → parseWS >>= λ _ →
                parseStringLit >>= λ d' → pure (v' , d'))
         pos (' ' ∷ in₁)
         (' ' ∷ []) pos₁ in₁
         (parseWS-one-space pos in₁
            (showNat-chars-head-stop-isHSpace v
               (' ' ∷ quoteStringLit-chars d ++ₗ rest))))
    (trans
      (bind-just-step parseNatural
         (λ v' → parseWS >>= λ _ →
                 parseStringLit >>= λ d' → pure (v' , d'))
         pos₁ in₁
         v pos₂ in₂
         (parseNatural-showNat-chars pos₁ v
            (' ' ∷ quoteStringLit-chars d ++ₗ rest)
            (∷-stop refl)))
    (trans
      (bind-just-step parseWS
         (λ _ → parseStringLit >>= λ d' → pure (v , d'))
         pos₂ in₂
         (' ' ∷ []) pos₃ in₃
         (parseWS-one-space pos₂ in₃
            (quoteStringLit-chars-head-isHSpace d rest)))
    (bind-just-step parseStringLit
         (λ d' → pure (v , d'))
         pos₃ in₃
         d pos₄ rest
         (parseStringLit-roundtrip pos₃ d rest rest-quote-ss))))

-- ============================================================================
-- many termination: parseValueEntry fails on ` ;\n...`
-- ============================================================================

-- On input `' ' ∷ ';' ∷ rest`, `parseValueEntry` consumes the leading
-- space via `parseWS`, then `parseNatural` rejects `;` and the whole
-- bind chain returns `nothing`.
private
  parseValueEntry-fails-on-semi :
      ∀ (pos : Position) (rest : List Char)
    → parseValueEntry pos (' ' ∷ ';' ∷ rest) ≡ nothing
  parseValueEntry-fails-on-semi pos rest =
    trans
      (bind-just-step parseWS
         (λ _ → parseNatural >>= λ v' → parseWS >>= λ _ →
                parseStringLit >>= λ d' → pure (v' , d'))
         pos (' ' ∷ ';' ∷ rest)
         (' ' ∷ []) (advancePosition pos ' ') (';' ∷ rest)
         (parseWS-one-space pos (';' ∷ rest) (∷-stop refl)))
      refl

  manyHelper-parseValueEntry-stop-semi :
      ∀ (pos : Position) (rest : List Char) (m : ℕ)
    → manyHelper parseValueEntry pos (' ' ∷ ';' ∷ rest) m
      ≡ just (mkResult [] pos (' ' ∷ ';' ∷ rest))
  manyHelper-parseValueEntry-stop-semi _   _    zero    = refl
  manyHelper-parseValueEntry-stop-semi pos rest (suc _)
    rewrite parseValueEntry-fails-on-semi pos rest = refl

-- ============================================================================
-- sameLengthᵇ progress lemmas
-- ============================================================================

private
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys < length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (_ ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  sameLengthᵇ-entry-iter-fail : ∀ (v : ℕ) (d : List Char) (rest : List Char)
    → sameLengthᵇ
        (' ' ∷ showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars d ++ₗ rest)
        rest
      ≡ false
  sameLengthᵇ-entry-iter-fail v d rest =
    sameLengthᵇ-lt
      (' ' ∷ showℕ-dec-chars v ++ₗ ' ' ∷ quoteStringLit-chars d ++ₗ rest)
      rest
      len-witness
    where
      len-witness :
        length rest <
        length (' ' ∷ showℕ-dec-chars v ++ₗ
                  ' ' ∷ quoteStringLit-chars d ++ₗ rest)
      len-witness
        rewrite length-++ (showℕ-dec-chars v)
                          {' ' ∷ quoteStringLit-chars d ++ₗ rest}
              | length-++ (quoteStringLit-chars d) {rest} =
          s≤s
            (≤-trans
              (m≤n+m (length rest)
                 (length (quoteStringLit-chars d)))
              (≤-trans
                (n≤1+n _)
                (m≤n+m _ (length (showℕ-dec-chars v)))))

-- ============================================================================
-- Position-walk after consuming entries
-- ============================================================================

afterEntries : Position → List (ℕ × List Char) → Position
afterEntries pos []              = pos
afterEntries pos ((v , d) ∷ es)  =
  afterEntries
    (advancePositions
       (advancePosition
          (advancePositions
             (advancePosition pos ' ')
             (showℕ-dec-chars v))
          ' ')
       (quoteStringLit-chars d))
    es

private
  afterEntries-advancePositions : ∀ (pos : Position) (es : List (ℕ × List Char))
    → afterEntries pos es ≡ advancePositions pos (entries-chars es)
  afterEntries-advancePositions pos []              = refl
  afterEntries-advancePositions pos ((v , d) ∷ es)  =
    let p₁ = advancePosition pos ' '
        p₂ = advancePositions p₁ (showℕ-dec-chars v)
        p₃ = advancePosition p₂ ' '
        p₄ = advancePositions p₃ (quoteStringLit-chars d)
    in
    trans
      (afterEntries-advancePositions p₄ es)
      (sym
        (trans
          (advancePositions-++ p₁
             (showℕ-dec-chars v)
             (' ' ∷ quoteStringLit-chars d ++ₗ entries-chars es))
          (advancePositions-++ p₃
             (quoteStringLit-chars d)
             (entries-chars es))))

-- ============================================================================
-- Inductive: many parses out all entries, then stops at ` ;\n`
-- ============================================================================

manyHelper-parseValueEntry-body :
    ∀ (pos : Position) (es : List (ℕ × List Char)) (suffix : List Char) (m : ℕ)
  → length es ≤ m
  → manyHelper parseValueEntry pos
      (entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix) m
    ≡ just (mkResult es
             (afterEntries pos es)
             (' ' ∷ ';' ∷ '\n' ∷ suffix))
manyHelper-parseValueEntry-body pos []        suffix m _ =
  manyHelper-parseValueEntry-stop-semi pos ('\n' ∷ suffix) m
manyHelper-parseValueEntry-body pos ((v , d) ∷ es) suffix (suc m') (s≤s len-le) =
  let
    p₁ = advancePosition pos ' '
    p₂ = advancePositions p₁ (showℕ-dec-chars v)
    p₃ = advancePosition p₂ ' '
    p₄ = advancePositions p₃ (quoteStringLit-chars d)
    iter-rest = entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix
    iter-rest-ss : SuffixStops (λ c → c ≈ᵇ '"') iter-rest
    iter-rest-ss = entries-rest-quote-stop es suffix
    iter-eq :
      parseValueEntry pos
        (' ' ∷ showℕ-dec-chars v ++ₗ
            ' ' ∷ quoteStringLit-chars d ++ₗ iter-rest)
      ≡ just (mkResult (v , d) p₄ iter-rest)
    iter-eq = parseValueEntry-step pos v d iter-rest iter-rest-ss
    shape-eq :
      entries-chars ((v , d) ∷ es) ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix
      ≡ ' ' ∷ showℕ-dec-chars v ++ₗ
            ' ' ∷ quoteStringLit-chars d ++ₗ iter-rest
    shape-eq =
      cong (' ' ∷_)
        (trans
          (++ₗ-assoc (showℕ-dec-chars v)
                     (' ' ∷ quoteStringLit-chars d ++ₗ entries-chars es)
                     (' ' ∷ ';' ∷ '\n' ∷ suffix))
          (cong (showℕ-dec-chars v ++ₗ_)
            (cong (' ' ∷_)
              (++ₗ-assoc (quoteStringLit-chars d)
                         (entries-chars es)
                         (' ' ∷ ';' ∷ '\n' ∷ suffix)))))
    rec-eq = manyHelper-parseValueEntry-body p₄ es suffix m' len-le
  in
  trans
    (cong (λ input → manyHelper parseValueEntry pos input (suc m'))
          shape-eq)
    (manyHelper-prog-cons parseValueEntry pos
       (' ' ∷ showℕ-dec-chars v ++ₗ
            ' ' ∷ quoteStringLit-chars d ++ₗ iter-rest)
       m' (v , d) p₄ iter-rest
       es (afterEntries p₄ es)
       (' ' ∷ ';' ∷ '\n' ∷ suffix)
       iter-eq
       (sameLengthᵇ-entry-iter-fail v d iter-rest)
       rec-eq)
  where
    entries-rest-quote-stop : ∀ (es : List (ℕ × List Char)) (suffix : List Char)
      → SuffixStops (λ c → c ≈ᵇ '"')
          (entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix)
    entries-rest-quote-stop []              _ = ∷-stop refl
    entries-rest-quote-stop ((_ , _) ∷ _)   _ = ∷-stop refl

-- ============================================================================
-- Main theorem: parseValueTable-roundtrip
-- ============================================================================

parseValueTable-roundtrip :
    ∀ (pos : Position) (vt : ValueTable) (suffix : List Char)
  → ValueTableNameStop vt
  → SuffixStops isNewlineStart suffix
  → parseValueTable pos (emitValueTable-chars vt ++ₗ suffix)
    ≡ just (mkResult vt
             (advancePositions pos (emitValueTable-chars vt))
             suffix)
parseValueTable-roundtrip pos vt suffix
    (c , cs , name-eq , c-non-hspace) nl-stop =
  trans (cong (parseValueTable pos) (emitValueTable-chars-shape vt suffix))
    (trans step-VAL_TABLE
      (trans step-parseWS-1
        (trans step-parseIdentifier
          (trans step-many-entries
            (trans step-parseWSOpt
              (trans step-char-semi
                (trans step-parseNewline
                  (trans step-many-parseNewline
                    step-pure))))))))
  where
    es : List (ℕ × List Char)
    es = ValueTable.entries vt

    nm-id : Identifier
    nm-id = ValueTable.name vt

    nm-chars : List Char
    nm-chars = Identifier.name (ValueTable.name vt)

    -- Intermediate positions.
    pos-vt    = advancePositions pos (toList "VAL_TABLE_")
    pos-ws₁   = advancePosition pos-vt ' '
    pos-name  = advancePositions pos-ws₁ nm-chars
    pos-ents  = afterEntries pos-name es
    pos-wsopt = advancePosition pos-ents ' '
    pos-semi  = advancePosition pos-wsopt ';'
    pos-lf₁   = advancePosition pos-semi '\n'

    -- Intermediate inputs.
    rest-vt    : List Char
    rest-vt    =
      ' ' ∷ (nm-chars ++ₗ
               (entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix))

    rest-ws₁   : List Char
    rest-ws₁   =
      nm-chars ++ₗ (entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix)

    rest-name  : List Char
    rest-name  = entries-chars es ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix

    rest-ents  : List Char
    rest-ents  = ' ' ∷ ';' ∷ '\n' ∷ suffix

    rest-wsopt : List Char
    rest-wsopt = ';' ∷ '\n' ∷ suffix

    rest-semi  : List Char
    rest-semi  = '\n' ∷ suffix

    -- Continuations after each bind.  Match the do-block desugaring
    -- of parseValueTable which uses `_>>=_ λ _ → ...` throughout (the
    -- Agda elaborator does not equate `_*>_` with `_>>=_ λ _ → _`
    -- syntactically, so the cont shapes must mirror the source).
    cont-vt : String → Parser ValueTable
    cont-vt _ =
      parseWS >>= λ _ →
      parseIdentifier >>= λ name →
      many parseValueEntry >>= λ entries →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = name ; entries = entries })

    cont-ws₁ : List Char → Parser ValueTable
    cont-ws₁ _ =
      parseIdentifier >>= λ name →
      many parseValueEntry >>= λ entries →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = name ; entries = entries })

    cont-name : Identifier → Parser ValueTable
    cont-name name =
      many parseValueEntry >>= λ entries →
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = name ; entries = entries })

    cont-ents : List (ℕ × List Char) → Parser ValueTable
    cont-ents entries =
      parseWSOpt >>= λ _ →
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id ; entries = entries })

    cont-wsopt : List Char → Parser ValueTable
    cont-wsopt _ =
      char ';' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id ; entries = es })

    cont-semi : Char → Parser ValueTable
    cont-semi _ =
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure (record { name = nm-id ; entries = es })

    cont-lf₁ : Char → Parser ValueTable
    cont-lf₁ _ =
      many parseNewline >>= λ _ →
      pure (record { name = nm-id ; entries = es })

    cont-manyLF : List Char → Parser ValueTable
    cont-manyLF _ = pure (record { name = nm-id ; entries = es })

    -- Step 1: consume "VAL_TABLE_".
    step-VAL_TABLE :
      parseValueTable pos (toList "VAL_TABLE_" ++ₗ rest-vt)
      ≡ cont-vt "VAL_TABLE_" pos-vt rest-vt
    step-VAL_TABLE =
      bind-just-step (string "VAL_TABLE_")
                     cont-vt
                     pos (toList "VAL_TABLE_" ++ₗ rest-vt)
                     "VAL_TABLE_" pos-vt rest-vt
                     (string-success pos "VAL_TABLE_" rest-vt)

    -- Step 2: parseWS consumes the single ` ` separator.
    --   `SuffixStops isHSpace rest-ws₁` — head of rest-ws₁ is the
    --   first char of nm-chars, which is `c` (non-hspace via
    --   ValueTableNameStop).
    ws₁-ss : SuffixStops isHSpace rest-ws₁
    ws₁-ss =
      subst (λ xs → SuffixStops isHSpace
                      (xs ++ₗ (entries-chars es ++ₗ
                                 ' ' ∷ ';' ∷ '\n' ∷ suffix)))
            (sym name-eq)
            (∷-stop c-non-hspace)

    step-parseWS-1 :
      cont-vt "VAL_TABLE_" pos-vt rest-vt
      ≡ cont-ws₁ (' ' ∷ []) pos-ws₁ rest-ws₁
    step-parseWS-1 =
      bind-just-step parseWS
                     cont-ws₁
                     pos-vt rest-vt
                     (' ' ∷ []) pos-ws₁ rest-ws₁
                     (parseWS-one-space pos-vt rest-ws₁ ws₁-ss)

    -- Step 3: parseIdentifier on nm-chars.
    --   `SuffixStops isIdentCont rest-name` — head of rest-name is
    --   either `' '` (entries-chars head when entries non-empty) or
    --   `' '` (synthesized terminator when entries empty).  Both
    --   non-identCont.
    ident-stop-ss : SuffixStops isIdentCont rest-name
    ident-stop-ss = entries-rest-identCont-stop es suffix
      where
        entries-rest-identCont-stop :
          ∀ (es' : List (ℕ × List Char)) (suffix' : List Char)
          → SuffixStops isIdentCont
              (entries-chars es' ++ₗ ' ' ∷ ';' ∷ '\n' ∷ suffix')
        entries-rest-identCont-stop []              _ = ∷-stop refl
        entries-rest-identCont-stop ((_ , _) ∷ _)   _ = ∷-stop refl

    step-parseIdentifier :
      cont-ws₁ (' ' ∷ []) pos-ws₁ rest-ws₁
      ≡ cont-name nm-id pos-name rest-name
    step-parseIdentifier =
      bind-just-step parseIdentifier
                     cont-name
                     pos-ws₁ rest-ws₁
                     nm-id pos-name rest-name
                     (parseIdentifier-roundtrip
                        pos-ws₁ nm-id rest-name
                        ident-stop-ss)

    -- Step 4: many parseValueEntry iterates through entries.
    step-many-entries :
      cont-name nm-id pos-name rest-name
      ≡ cont-ents es pos-ents rest-ents
    step-many-entries =
      bind-just-step (many parseValueEntry)
                     cont-ents
                     pos-name rest-name
                     es pos-ents rest-ents
                     (manyHelper-parseValueEntry-body
                        pos-name es suffix
                        (length rest-name)
                        body-fuel-bound)
      where
        le-monotone-++ : ∀ (xs ys : List Char)
          → length ys ≤ length (xs ++ₗ ys)
        le-monotone-++ []        ys = ≤-refl
        le-monotone-++ (x ∷ xs') ys = ≤-trans (le-monotone-++ xs' ys) (n≤1+n _)

        -- Each entry contributes ≥4 chars to entries-chars; in particular,
        -- `length es ≤ length (entries-chars es)` for any list of entries.
        length-es-le-entries-chars : ∀ (es' : List (ℕ × List Char))
          → length es' ≤ length (entries-chars es')
        length-es-le-entries-chars []              = z≤n
        length-es-le-entries-chars ((v , d) ∷ es') =
          s≤s
            (≤-trans
               (length-es-le-entries-chars es')
               (≤-trans
                  (le-monotone-++ (quoteStringLit-chars d) (entries-chars es'))
                  (≤-trans
                    (n≤1+n _)
                    (le-monotone-++ (showℕ-dec-chars v)
                       (' ' ∷ quoteStringLit-chars d ++ₗ entries-chars es')))))

        body-fuel-bound : length es ≤ length rest-name
        body-fuel-bound
          rewrite length-++ (entries-chars es)
                            {' ' ∷ ';' ∷ '\n' ∷ suffix} =
            ≤-trans
              (length-es-le-entries-chars es)
              (m≤m+n (length (entries-chars es))
                     (length (' ' ∷ ';' ∷ '\n' ∷ suffix)))

    -- Step 5: parseWSOpt consumes 1 hspace (the ` ` before `;`).
    wsopt-ss : SuffixStops isHSpace rest-wsopt
    wsopt-ss = ∷-stop refl

    step-parseWSOpt :
      cont-ents es pos-ents rest-ents
      ≡ cont-wsopt (' ' ∷ []) pos-wsopt rest-wsopt
    step-parseWSOpt =
      bind-just-step parseWSOpt
                     cont-wsopt
                     pos-ents rest-ents
                     (' ' ∷ []) pos-wsopt rest-wsopt
                     (manyHelper-satisfy-exhaust-many isHSpace pos-ents
                        (' ' ∷ []) rest-wsopt
                        (refl All.∷ All.[]) wsopt-ss)

    -- Step 6: char ';' matches.
    step-char-semi :
      cont-wsopt (' ' ∷ []) pos-wsopt rest-wsopt
      ≡ cont-semi ';' pos-semi rest-semi
    step-char-semi =
      bind-just-step (char ';')
                     cont-semi
                     pos-wsopt rest-wsopt
                     ';' pos-semi rest-semi
                     (char-matches ';' pos-wsopt rest-semi)

    -- Step 7: parseNewline matches '\n'.
    step-parseNewline :
      cont-semi ';' pos-semi rest-semi
      ≡ cont-lf₁ '\n' pos-lf₁ suffix
    step-parseNewline =
      bind-just-step parseNewline
                     cont-lf₁
                     pos-semi rest-semi
                     '\n' pos-lf₁ suffix
                     (parseNewline-match-LF pos-semi suffix)

    -- Step 8: many parseNewline stops at first non-LF char.
    step-many-parseNewline :
      cont-lf₁ '\n' pos-lf₁ suffix
      ≡ cont-manyLF [] pos-lf₁ suffix
    step-many-parseNewline =
      bind-just-step (many parseNewline)
                     cont-manyLF
                     pos-lf₁ suffix
                     [] pos-lf₁ suffix
                     (manyHelper-parseNewline-exhaust pos-lf₁ suffix
                        (length suffix) nl-stop)

    -- Step 9: pure-step.  Combine pos-lf₁'s chain of advancePosition /
    -- advancePositions calls into a single `advancePositions pos LIST`
    -- shape, then rewrite LIST to `emitValueTable-chars vt`.
    pos-final-eq : pos-lf₁ ≡ advancePositions pos (emitValueTable-chars vt)
    pos-final-eq =
      trans
        -- Step 9a: `pos-lf₁` ≡ `advancePositions pos (full-list)` via
        -- repeated `sym advancePositions-++`.  Definitional reductions
        -- cover the singleton `advancePosition X c = advancePositions
        -- X (c ∷ [])` step at each level.
        (trans
          (cong (λ p → advancePosition (advancePosition (advancePosition p ' ') ';') '\n')
                (afterEntries-advancePositions pos-name es))
          (sym pos-as-advancePositions))
        -- Step 9b: cong on shape-no-suffix (sym of the suffix-= shape
        -- lemma + ++-identityʳ).
        (cong (advancePositions pos) shape-no-suffix)
      where
        full-list : List Char
        full-list = toList "VAL_TABLE_" ++ₗ
                      ' ' ∷ nm-chars ++ₗ
                        entries-chars es ++ₗ
                          ' ' ∷ ';' ∷ '\n' ∷ []

        -- pos-lf₁ unfolded as `advancePositions pos full-list`.  Five
        -- `advancePositions-++` applications collapse the nested
        -- chain.  Singleton-list ≡ advancePosition steps are
        -- definitional.
        pos-as-advancePositions :
          advancePositions pos full-list
          ≡ advancePosition (advancePosition
              (advancePosition
                 (advancePositions pos-name (entries-chars es))
                 ' ') ';') '\n'
        pos-as-advancePositions =
          trans
            (advancePositions-++ pos
               (toList "VAL_TABLE_")
               (' ' ∷ nm-chars ++ₗ
                  entries-chars es ++ₗ
                  ' ' ∷ ';' ∷ '\n' ∷ []))
            (trans
              (advancePositions-++ pos-vt
                 (' ' ∷ [])
                 (nm-chars ++ₗ
                    entries-chars es ++ₗ
                    ' ' ∷ ';' ∷ '\n' ∷ []))
              (trans
                (advancePositions-++ pos-ws₁
                   nm-chars
                   (entries-chars es ++ₗ
                      ' ' ∷ ';' ∷ '\n' ∷ []))
                (advancePositions-++ pos-name
                   (entries-chars es)
                   (' ' ∷ ';' ∷ '\n' ∷ []))))

        -- `full-list ≡ emitValueTable-chars vt`.  Derived from the
        -- main `emitValueTable-chars-shape vt []` lemma + ++-identityʳ.
        shape-no-suffix : full-list ≡ emitValueTable-chars vt
        shape-no-suffix =
          trans
            (sym (emitValueTable-chars-shape vt []))
            (++-identityʳ (emitValueTable-chars vt))

    step-pure :
      cont-manyLF [] pos-lf₁ suffix
      ≡ just (mkResult vt
               (advancePositions pos (emitValueTable-chars vt))
               suffix)
    step-pure =
      trans
        (cong (λ p → just (mkResult (record { name = nm-id ; entries = es })
                                    p suffix))
              pos-final-eq)
        (cong (λ result →
                  just (mkResult result
                                 (advancePositions pos (emitValueTable-chars vt))
                                 suffix))
              eta)
      where
        eta : record { name = nm-id ; entries = es } ≡ vt
        eta = refl
