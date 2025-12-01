# Phase 2A Cleanup Report

This document summarizes code review findings and cleanup recommendations for Phase 2A.

## 1. Dead Code / Unused Modules

### High Priority (Safe to Delete)

| Module | Lines | Issue |
|--------|-------|-------|
| `Aletheia.LTL.Checker` | 72 | Never imported; duplicates `SignalPredicate.checkProperty`; `mapAtoms` duplicates `Syntax.mapLTL` |
| `Aletheia.Logging` | 23 | Never imported; stub module with unused types |
| `Aletheia.LTL.Properties` | 8 | Empty placeholder with single TODO comment |
| `Aletheia.Parser.Examples` | ? | Never imported |
| `Aletheia.DBC.Validation` | ? | Never imported |

**Recommendation**: Delete these modules to reduce maintenance burden.

### Lower Priority

| Module | Issue |
|--------|-------|
| `Aletheia.Trace.Stream` | Only used by unused Checker.agda |
| `Aletheia.Trace.Context` | Limited usage, mostly internal |

## 2. Code Duplication

### Critical: mapAtoms vs mapLTL

`Checker.agda:35-45` duplicates `Syntax.agda:18-28` exactly:

```agda
-- In Syntax.agda (KEEP)
mapLTL : ∀ {A B : Set} → (A → B) → LTL A → LTL B

-- In Checker.agda (DELETE - exact duplicate)
mapAtoms : ∀ {A B : Set} → (A → B) → LTL A → LTL B
```

**Recommendation**: Delete `Checker.agda` entirely; it's unused and duplicates `SignalPredicate.checkProperty`.

## 3. Architecture Issues

### DSL Intermediate Layer

Current flow:
```
YAML string → Parser → Yaml AST → Convert → Python AST → Translate → LTL
```

The `Python.agda` intermediate representation adds complexity without benefit:
- `Yaml.agda` and `Python.agda` have nearly identical types
- `Convert.agda` just copies fields between equivalent types

**Recommendation** (Phase 2B): Simplify to:
```
YAML string → Parser → Yaml AST → Translate → LTL
```

This would eliminate ~150 lines of code and reduce cognitive overhead.

## 4. Root Directory Clutter

### Test Files (6 Python files)

These should be moved to `python/tests/` or deleted:

- `debug_yaml.py`
- `test_command_parser.agda`
- `test_compare_dbc.py`
- `test_debug_extract.py`
- `test_python_wrapper.py`
- `test_yaml_manual.py`

### Temporary YAML Files (20+ files)

Development artifacts that should be deleted:

```
test_dbc*.yaml
test_extract*.yaml
test_inject*.yaml
test_parsedbc*.yaml
test_factor*.yaml
test_minimal*.yaml
test_simple*.yaml
test_no_blank*.yaml
```

**Recommendation**: Delete all `test_*.yaml` files in root; add `.gitignore` pattern.

## 5. TODOs in Code

| File | TODO |
|------|------|
| `LTL/Properties.agda` | "Soundness and completeness proofs" |
| `LTL/DSL/Translate.agda` | "Prove that translation preserves semantics" |

**Recommendation**: These are Phase 3 items (verification). Keep the TODOs but move them to PHASE3_AUDIT.md for tracking.

## 6. Documentation Needs

### Missing Documentation

1. **LTL Property YAML Format** - No reference for users
   - What types are supported?
   - What operators?
   - Example properties?

2. **DSL Architecture** - Internal docs for developers
   - Why Yaml → Python → LTL?
   - What each module does?

3. **Module README** - No overview of `src/Aletheia/LTL/`

### Recommended Documentation

Create `docs/ltl-properties.md`:
```markdown
# LTL Property YAML Format

## Temporal Operators
- `always` - Property holds at all times
- `eventually` - Property holds at some time
- `never` - Property never holds
- `eventually_within` - Property holds within time window
- `always_within` - Property holds throughout time window

## Predicates
- `compare` - Signal comparison (LT, GT, EQ, LE, GE, NE)
- `between` - Signal in range [min, max]
- `changed_by` - Signal change rate ≤ delta

## Logical Operators
- `and`, `or` - Combine properties
- `implies` - Implication
- `not` - Negation

## Examples
...
```

## 7. Code Smells

### Minor Issues

1. **Hardcoded error messages** in SignalPredicate.agda return `false` instead of informative errors
   - Phase 2B should add structured error reporting

2. **Magic numbers** in timestamps (are they microseconds? milliseconds?)
   - Need constants or types to clarify units

3. **No input validation** in DSL parser
   - Invalid YAML gives cryptic parse errors

## 8. Limitations to Document

### Known Limitations (By Design)

| Limitation | Impact | Phase to Address |
|------------|--------|------------------|
| No CAN-FD support | 8-byte frames only | Phase 5 |
| No multiplexing | All signals present | Phase 5 |
| No counterexamples | Just true/false | Phase 2B |
| Invalid signal → false | No error message | Phase 2B |

### Semantic Issues

1. **ChangedBy first frame** - Returns `true` (vacuously true)
   - This is correct but should be documented

2. **Empty trace** - Raises RuntimeError
   - Should this return true for always, false for eventually?

3. **Timestamp units** - Parser uses ℕ but units unclear
   - Are they microseconds? Need consistent documentation

## 9. Cleanup Action Items

### Immediate (Do Now)

1. [ ] Delete unused modules: Checker, Logging, Properties, Examples, Validation
2. [ ] Delete temporary YAML files from root
3. [ ] Move root test files to `python/tests/` or delete
4. [ ] Add `.gitignore` patterns for `test_*.yaml`

### Phase 2B

1. [ ] Simplify DSL architecture (remove Python.agda intermediate layer)
2. [ ] Add structured error reporting
3. [ ] Create LTL property documentation

### Phase 3

1. [ ] Prove translation preserves semantics
2. [ ] Add soundness/completeness proofs for LTL semantics

## Summary

**Lines to delete**: ~200+ (unused modules + temp files)
**Architecture simplification potential**: ~150 lines
**Documentation to add**: 1-2 markdown files

The codebase is in good shape overall. The main issues are:
1. Development artifacts left in root directory
2. Unused modules from early development
3. One instance of code duplication (Checker.agda)

None of these affect functionality, but cleanup will improve maintainability.
