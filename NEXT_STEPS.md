# Next Steps: Propositional Operators

## ✅ Milestone Reached: Atomic Case Proven!

**Achievement**: Successfully proven `atomic-fold-equiv` without postulates using coinductive techniques!

## Current Position

**Phase 3 Status**:
- ✅ Step 1: Refactor (extract `foldStepEval-go`) - COMPLETE
- ✅ Step 2: Prove atomic case - COMPLETE
- ⏸️ Step 3: Prove propositional operators - IN PROGRESS

**File**: `src/Aletheia/LTL/Properties.agda`
- Lines 66-88: `foldStepEval-go` (top-level helper)
- Lines 125-141: `atomic-fold-equiv` (proven!)
- Lines 162, 165: Holes for Not operator (next task)

## Immediate Next Task

**Prove Not operator** following the atomic case pattern:

### Template
```agda
-- 1. Helper for foldStepEval-go
not-go-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (st : LTLEvalState) ...
  → ∞ ⊢ foldStepEval-go (Not φ) (NotState st) prev curr rest ≈ <target>

not-go-equiv φ st prev curr rest with stepEval (Not φ) evalAtomicPred (NotState st) prev curr
... | Continue st' = DB.later λ where .force → ...  -- Recursive case
... | Satisfied = DB.now refl
... | Violated _ = DB.now refl

-- 2. Main theorem
not-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not φ) trace ≈ checkColist (Not φ) trace
not-fold-equiv φ [] = DB.now refl
not-fold-equiv φ (f ∷ rest) = DB.later λ where .force → not-go-equiv φ (initState φ) nothing f (rest .force)
```

## Key Pattern (Proven to Work)

From atomic case:
1. **Extract to top-level**: Makes function visible in proofs
2. **Pattern match**: On key values to enable reduction
3. **Copattern matching**: `DB.later λ where .force → ...`
4. **Base cases**: `DB.now refl` when both sides reduce to same value

## Time Estimates

- Not operator: 1-2 hours
- And operator: 1-2 hours  
- Or operator: 1-2 hours
- **Total**: 3-5 hours to complete Phase 3

## Resources

- Session state: `/home/nicolas/dev/agda/aletheia/.session-state.md`
- Detailed plan: `/home/nicolas/.claude/plans/coinductive-proof-strategy.md`
- Stdlib examples: `/home/nicolas/.agda/agda-stdlib/src/Codata/Sized/Delay/Properties.agda`

## Build Command

```bash
timeout 180 agda +RTS -N32 -RTS src/Aletheia/LTL/Properties.agda
```

Expected: Only holes at lines 162, 165 (propositional operators)

---

**Start here next session**: Implement `not-go-equiv` and `not-fold-equiv`
