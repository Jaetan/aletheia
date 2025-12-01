# Directory Structure Reorganization Plan

## Current Issues

1. **Root directory cluttered** - 14 markdown files in root
2. **Test files scattered** - `test_*.py` in root, `tests/` in python/
3. **Log files everywhere** - `c.log` in root, src/, examples/
4. **Empty directory** - `src/Aletheia/LTL/DSL/` (after cleanup)
5. **Mixed concerns** - Documentation, tests, source all in root

## Proposed Structure

```
aletheia/
├── docs/                          # All documentation
│   ├── architecture/              # Architecture docs
│   │   ├── DESIGN.md              # Overall design
│   │   ├── ARCHITECTURAL_ANALYSIS.md
│   │   ├── PHASE2B_ARCHITECTURE.md
│   │   └── LTL_JSON_SCHEMA.md     # (move from docs/)
│   ├── development/               # Developer docs
│   │   ├── BUILDING.md
│   │   ├── DEVELOPMENT.md
│   │   ├── CLAUDE.md
│   │   └── CONTRIBUTING.md        # (to create)
│   ├── phases/                    # Phase completion docs
│   │   ├── PHASE1_AUDIT.md
│   │   ├── PHASE2A_CLEANUP.md
│   │   ├── PHASE2B1_COMPLETION.md
│   │   └── SESSION_SUMMARY.md
│   ├── cleanup/                   # Cleanup documentation
│   │   ├── CLEANUP_PLAN.md
│   │   └── CLEANUP_SUMMARY.md
│   └── README.md                  # Docs index
│
├── src/                           # Agda source code
│   ├── Aletheia/
│   │   ├── CAN/                   # CAN frame handling (6 modules)
│   │   │   ├── Encoding.agda      # Signal encoding/decoding
│   │   │   ├── Endianness.agda    # Byte order handling
│   │   │   ├── ExtractionResult.agda
│   │   │   ├── Frame.agda         # CAN frame types
│   │   │   ├── Signal.agda        # Signal types
│   │   │   └── SignalExtraction.agda
│   │   ├── Data/                  # Core data types (2 modules)
│   │   │   ├── DelayedColist.agda # Coinductive lists
│   │   │   └── Message.agda       # Protocol messages
│   │   ├── DBC/                   # DBC parser (5 modules)
│   │   │   ├── JSONParser.agda    # JSON DBC parser
│   │   │   ├── Parser.agda        # Core DBC parser
│   │   │   ├── ParserTraced.agda  # Debug parser
│   │   │   ├── Properties.agda    # Correctness proofs
│   │   │   └── Types.agda         # DBC types
│   │   ├── LTL/                   # Linear Temporal Logic (5 modules)
│   │   │   ├── Coinductive.agda   # Coinductive LTL
│   │   │   ├── Incremental.agda   # Incremental checker
│   │   │   ├── JSON.agda          # JSON parser
│   │   │   ├── SignalPredicate.agda
│   │   │   └── Syntax.agda        # LTL syntax
│   │   ├── Parser/                # Parser combinators (3 modules)
│   │   │   ├── Combinators.agda   # Core combinators
│   │   │   ├── Properties.agda    # Parser proofs
│   │   │   └── Tracing.agda       # Debug tracing
│   │   ├── Protocol/              # JSON protocol (4 modules)
│   │   │   ├── JSON.agda          # JSON types/parser
│   │   │   ├── Response.agda      # Response types
│   │   │   ├── Routing.agda       # Request routing
│   │   │   └── StreamState.agda   # State machine
│   │   ├── Trace/                 # Trace handling (6 modules)
│   │   │   ├── CANTrace.agda      # CAN trace types
│   │   │   ├── Context.agda       # Trace context
│   │   │   ├── Parser.agda        # Trace parser
│   │   │   ├── SizedStream.agda   # Sized streams
│   │   │   ├── Stream.agda        # Stream types
│   │   │   └── StreamParser.agda  # Stream parser
│   │   ├── Main.agda              # Entry point
│   │   └── Prelude.agda           # Common imports
│   └── PrecompileStdlib.agda      # Stdlib cache
│
├── haskell-shim/                  # Minimal Haskell I/O shim
│   ├── src/
│   │   └── Main.hs                # Haskell entry point
│   ├── aletheia.cabal             # Cabal config
│   └── Setup.hs
│
├── python/                        # Python API wrapper
│   ├── aletheia/                  # Package
│   │   ├── __init__.py
│   │   ├── _binary.py             # Binary interface
│   │   ├── dbc_converter.py       # DBC YAML→JSON
│   │   ├── decoder.py             # CAN decoder
│   │   ├── dsl.py                 # LTL DSL
│   │   ├── ltl.py                 # LTL helpers
│   │   ├── streaming_client.py    # Streaming client
│   │   └── verifier.py            # Verification API
│   ├── tests/                     # Python tests
│   │   ├── test_ltl_integration.py
│   │   ├── test_smoke.py
│   │   └── test_streaming_client.py
│   ├── pyproject.toml
│   └── README.md
│
├── tests/                         # Integration tests (NEW)
│   ├── integration/               # End-to-end tests
│   │   ├── test_integration.py    # (move from root)
│   │   ├── test_simple.py         # (move from root)
│   │   └── fixtures/              # Test data
│   │       ├── test_speed.dbc     # (move from root)
│   │       └── test_speed.dbc.json
│   └── README.md                  # Test documentation
│
├── examples/                      # Usage examples
│   ├── sample.dbc.yaml            # Example DBC
│   ├── sample_trace.yaml          # Example trace
│   ├── simple_verification.py     # Example script
│   └── README.md
│
├── build/                         # Build artifacts (gitignored)
├── _build/                        # Agda cache (gitignored)
│
├── aletheia.agda-lib              # Agda library config
├── shake.cabal                    # Shake build config
├── Shakefile.hs                   # Build system
└── README.md                      # Project README
```

## Module Organization (src/Aletheia/)

### Current: 33 modules in 8 directories

| Directory | Modules | Purpose |
|-----------|---------|---------|
| **CAN/** | 6 | CAN frame encoding/decoding |
| **Data/** | 2 | Core data types (Message, Colist) |
| **DBC/** | 5 | DBC file parsing and types |
| **LTL/** | 5 | Linear Temporal Logic |
| **Parser/** | 3 | Parser combinators |
| **Protocol/** | 4 | JSON streaming protocol |
| **Trace/** | 6 | Trace parsing and streams |
| *(root)* | 2 | Main entry point, Prelude |

**Total: 33 modules, well-organized by concern** ✓

## Actions Required

### 1. Create New Directory Structure
```bash
mkdir -p docs/{architecture,development,phases,cleanup}
mkdir -p tests/{integration,integration/fixtures}
```

### 2. Move Documentation Files
```bash
# Architecture docs
mv DESIGN.md ARCHITECTURAL_ANALYSIS.md PHASE2B_ARCHITECTURE.md docs/architecture/
mv docs/LTL_JSON_SCHEMA.md docs/architecture/

# Development docs
mv BUILDING.md DEVELOPMENT.md CLAUDE.md docs/development/

# Phase docs
mv PHASE1_AUDIT.md PHASE2A_CLEANUP.md PHASE2B1_COMPLETION.md SESSION_SUMMARY.md docs/phases/

# Cleanup docs
mv CLEANUP_PLAN.md CLEANUP_SUMMARY.md docs/cleanup/
```

### 3. Move Test Files
```bash
# Integration tests
mv test_integration.py test_simple.py tests/integration/

# Test fixtures
mv test_speed.dbc test_speed.dbc.json tests/integration/fixtures/
```

### 4. Clean Up Log Files
```bash
rm -f c.log src/c.log examples/c.log
echo "*.log" >> .gitignore
```

### 5. Remove Empty Directories
```bash
rmdir src/Aletheia/LTL/DSL/  # Empty after cleanup
```

### 6. Update .gitignore
```bash
cat >> .gitignore << 'GITIGNORE'
# Build artifacts
build/
_build/
dist-newstyle/
*.agdai
*.hi
*.o

# Python
venv/
__pycache__/
*.pyc
*.egg-info/

# Logs
*.log

# Editor
.vscode/
.idea/
*.swp
*~
GITIGNORE
```

## Benefits

1. **Clearer Structure**
   - Root only has essential files (README, configs, Shakefile)
   - Documentation organized by category
   - Tests in dedicated directory

2. **Easier Navigation**
   - All docs in one place
   - Test files grouped together
   - Clear separation of concerns

3. **Better for New Contributors**
   - Obvious where to find things
   - Less overwhelming root directory
   - Logical grouping

4. **Maintainable**
   - Easy to find related files
   - Clear naming conventions
   - Scalable structure

## Files in Root After Cleanup

```
aletheia/
├── docs/                    # All documentation
├── src/                     # All Agda source
├── haskell-shim/            # Haskell I/O
├── python/                  # Python API
├── tests/                   # Integration tests
├── examples/                # Usage examples
├── build/                   # (gitignored)
├── _build/                  # (gitignored)
├── aletheia.agda-lib        # Agda config
├── shake.cabal              # Build config
├── Shakefile.hs             # Build system
├── .gitignore               # Git ignore rules
└── README.md                # Project overview
```

**Clean, organized, professional** ✓

## Implementation Status

1. ✅ Create directory structure - COMPLETE
2. ✅ Move documentation files - COMPLETE
3. ✅ Move test files - COMPLETE
4. ✅ Clean up log files - COMPLETE
5. ✅ Remove empty directories - COMPLETE
6. ✅ Update .gitignore - COMPLETE
7. ✅ Update imports/paths in Python tests - COMPLETE
8. ✅ Rebuild and test - COMPLETE (all tests pass)
9. ⏳ Commit changes - PENDING

**Result**: Directory reorganization complete and verified working!
