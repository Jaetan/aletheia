# Code Review: Naming Conventions

**Date**: 2025-12-26
**Purpose**: Review top-level definitions for descriptive naming
**Status**: 🔄 In Progress

## Summary

Total Agda modules: 33
Focus: Top-level exported functions with generic/non-descriptive names

## ✅ Completed Renaming

### Critical Issue Resolved

1. **✅ `go` → `evaluateLTLOnTrace` in `Aletheia/LTL/Coinductive.agda`**
   - **Previous**: `go` (too generic)
   - **Current**: `evaluateLTLOnTrace`
   - **Why changed**: "go" was extremely generic and didn't describe what the function does
   - **Usage**: Exported, used in Properties.agda proofs
   - **Impact**: HIGH - this is a core LTL evaluation function
   - **Status**: ✅ COMPLETED - All references updated and verified

### Moderate: Could Be More Descriptive

2. **`all` in `Aletheia/DBC/Properties.agda`**
   - **Current**: `all`
   - **Proposed**: `allSatisfy` or keep stdlib's `all`
   - **Note**: Might be shadowing stdlib `all`

## ✅ Good Names (Descriptive & Clear)

Examples of well-named functions:
- `extractSignalWithContext` - clearly describes what it does
- `checkColist` - describes checking a colist
- `foldStepEval-go` - descriptive helper name
- `nextactive-unwrap` - describes unwrapping NextActive state
- `swapBytes-involutive` - property name is clear

## 📊 Naming Patterns Observed

### Good Patterns:
- `parse*` - parsing functions clearly prefixed
- `check*` - checking/validation functions
- `extract*` - extraction functions
- `*-equiv` - equivalence lemmas
- `*-bounded` - boundedness properties
- `*-consistent` - consistency properties

### Patterns to Avoid:
- Single-word generic verbs (`go`, `run`, `exec`)
- Abbreviations without context (`proc`, `eval` alone)
- Non-descriptive helpers (`helper1`, `aux`)

## 🔍 Detailed Module Analysis

### Aletheia/LTL/Coinductive.agda

**Functions**:
- ❌ `go` → Should rename
- ✅ `checkColist` - Good
- ✅ `checkColistCE` - Good (CE = CounterExample)
- ✅ `checkDelayedColist` - Good
- ✅ `checkProperty` - Good
- ✅ `checkSignalPredicateStream` - Good (descriptive)
- ✅ `checkAllPropertiesIncremental` - Good

### Aletheia/LTL/Properties.agda

**Lemmas** (all have descriptive names):
- ✅ `atomic-fold-equiv` - Clear
- ✅ `not-atomic-fold-equiv` - Clear
- ✅ `and-atomic-fold-equiv` - Clear
- ✅ `or-atomic-fold-equiv` - Clear
- ✅ `next-fold-equiv` - Clear
- ✅ `nextactive-unwrap` - Clear (helper lemma)
- ✅ `prev-irrelevant` - Clear (postulated lemma)

**Helpers**:
- ✅ `foldStepEval-go` - Descriptive
- ✅ `evalAtomicPred` - Clear

### Aletheia/Parser/Combinators.agda

**Parser Combinators**:
- ✅ `satisfy`, `char`, `anyChar`, `oneOf`, `noneOf` - Standard combinator names
- ✅ `many`, `some`, `count` - Standard combinator names
- ✅ `digit`, `letter`, `alphaNum`, `spaces` - Clear

### Other Modules

Most other modules follow good naming conventions:
- CAN modules: `extractSignal`, `injectSignal`, `extractBits`, etc.
- DBC modules: `parseDBC`, `parseMessage`, `parseSignal`
- Protocol modules: `processJSONLine`, `handleDataFrame`

## 📋 Actionable Items

### HIGH Priority (Before Always proof)

1. **✅ COMPLETED: Rename `go` in Coinductive.agda**
   - ✅ Renamed to: `evaluateLTLOnTrace`
   - ✅ Updated all references in Properties.agda
   - ✅ Updated documentation/comments
   - ✅ Verified compilation (both files typecheck)

### MEDIUM Priority (After Phase 4)

2. **Review helper function names in where-clauses**
   - These were already renamed in recent refactoring:
     - `go` → `goSignal` in `checkSignalPredicateStream`
     - `go` → `goAllProps` in `checkAllPropertiesIncremental`
     - `go` → `goCE` in `checkColistCE`
   - ✅ DONE (already addressed in recent session)

### LOW Priority (Phase 5+)

3. **Consider renaming abbreviated helpers**
   - Review all `*-helper` functions for more descriptive names
   - Example: `stepEval-and-helper` could be `combineAndResults`

## 🎯 Recommendation

**Top priority**: Rename `go` → `evaluateLTLOnTrace` in Coinductive.agda

This is the most critical naming issue as:
1. It's a top-level exported function
2. It's used in proofs (Properties.agda)
3. "go" is extremely generic and doesn't convey what the function does
4. It's a core piece of the LTL evaluation logic

## ✓ Verification Status

- [x] All modules compile successfully
- [x] Lemmas are type-checked (Properties.agda compiles)
- [x] No warnings about unused definitions
- [x] ✅ `go` function renamed to `evaluateLTLOnTrace` (completed 2025-12-26)
- [x] All pre-Always-proof tasks completed - ready for Phase 4 temporal operator proofs
