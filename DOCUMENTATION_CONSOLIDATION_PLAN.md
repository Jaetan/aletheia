# Documentation Consolidation Plan

**Date**: 2025-12-02
**Current Status**: Phase 2B.1 Complete
**Goal**: Single source of truth for all information, eliminate duplication and outdated content

## Executive Summary

**Problems Identified**:
1. **Duplication**: Streaming protocol described in 3 places (DESIGN.md, PHASE2B_ARCHITECTURE.md, PHASE2B1_COMPLETION.md)
2. **Outdated**: DESIGN.md shows Phase 2A status but we completed Phase 2B.1
3. **Scattered**: 4 cleanup docs, 4 phase docs, some overlap
4. **Missing**: Python API docs, current JSON protocol spec, module headers
5. **Historical clutter**: Phase audit docs are historical records, not current docs

## Proposed Structure

### Keep and Update

#### 1. **ROOT: README.md** (project overview - keep as-is)
- Purpose: First-time visitor orientation
- Audience: New users, contributors
- Status: Likely needs updating for Phase 2B.1

#### 2. **ROOT: CLAUDE.md** ✅ (moved back to root)
- Purpose: Instructions for Claude Code
- Audience: AI assistant
- Status: Needs updating for Phase 2B.1 completion

#### 3. **docs/architecture/DESIGN.md** (master design document - CONSOLIDATE)
- Purpose: Complete system design, architecture, and phase plan
- Audience: Architects, contributors, users wanting deep understanding
- **Actions**:
  - Update to reflect Phase 2B.1 completion
  - Consolidate streaming protocol from PHASE2B_ARCHITECTURE.md
  - Update phase plan to show current status
  - Remove outdated YAML references
  - Keep as single source of truth for architecture

#### 4. **docs/architecture/PROTOCOL.md** (NEW - extract from DESIGN.md)
- Purpose: Current JSON streaming protocol specification
- Audience: Integration developers, Python API users
- **Content**:
  - JSON message formats (commands, responses, data frames)
  - State machine
  - Rational number encoding
  - LTL property format
  - Examples
- **Extract from**: DESIGN.md (streaming section), PHASE2B_ARCHITECTURE.md, LTL_JSON_SCHEMA.md

#### 5. **docs/architecture/ARCHITECTURAL_ANALYSIS.md** (keep as-is)
- Purpose: Deep dive on CAN protocol decisions (extended IDs, CAN-FD, multiplexing)
- Audience: Technical decision makers
- Status: ✅ Still relevant and unique information

#### 6. **docs/development/BUILDING.md** (keep, minor updates)
- Purpose: Build system instructions
- Status: Verify accuracy for current build

#### 7. **docs/development/DEVELOPMENT.md** (keep, verify)
- Purpose: Development workflow, conventions
- Status: Check for outdated info

#### 8. **docs/development/PYTHON_API.md** (NEW - critical gap)
- Purpose: Python API reference with examples
- Audience: Python users (primary user base)
- **Content**:
  - Quick start example
  - StreamingClient usage
  - LTL DSL (Signal, Predicate, Property)
  - StreamingClient usage
  - Error handling
  - Full working examples

### Consolidate and Remove

#### 9. **Phase Documentation** (consolidate → archive)
Current files in `docs/phases/`:
- PHASE1_AUDIT.md (28K) - Historical audit
- PHASE2A_CLEANUP.md (5.8K) - Historical cleanup
- PHASE2B1_COMPLETION.md (4.4K) - Completion summary
- SESSION_SUMMARY.md (789 bytes) - Outdated session notes

**Action**: Consolidate into single `docs/architecture/CHANGELOG.md`:
```markdown
# Aletheia Development Changelog

## Phase 2B.1: JSON Streaming Protocol (2025-11-29)
✅ **COMPLETE**
- Implemented pure JSON streaming protocol
- Rational number support with exact representation
- LTL property checking with violation detection
- Integration test suite complete

## Phase 2A: LTL Core (2025-11-18)
✅ **COMPLETE**
- LTL syntax and semantics
- Coinductive model checker
- JSON parser for LTL formulas
- Signal predicate evaluation

## Phase 1: Core Infrastructure (2025-11-13)
✅ **COMPLETE**
- Parser combinators (structural recursion)
- CAN encoding/decoding
- DBC parser
- Build system
```

**Rationale**: Phase audits are historical records. CHANGELOG captures key milestones without duplication.

#### 10. **Cleanup Documentation** (consolidate → single file)
Current files in `docs/cleanup/`:
- CLEANUP_PLAN.md (2.6K)
- CLEANUP_SUMMARY.md (4.1K)
- DIRECTORY_STRUCTURE_PLAN.md (9.8K)
- REORGANIZATION_SUMMARY.md (5.6K)

**Action**: Keep only `REORGANIZATION_SUMMARY.md`, delete others
**Rationale**: Reorganization is complete. No need for 4 docs describing the same work.

#### 11. **Architecture Duplication** (merge)
Files with duplication:
- PHASE2B_ARCHITECTURE.md (7.8K) - Streaming protocol design
- LTL_JSON_SCHEMA.md (3.4K) - LTL property JSON format

**Action**:
- Merge PHASE2B_ARCHITECTURE.md → DESIGN.md (streaming section)
- Merge LTL_JSON_SCHEMA.md → PROTOCOL.md (LTL format section)
- Delete originals

### Create New Documentation

#### 12. **docs/development/PYTHON_API.md** (NEW - HIGH PRIORITY)
Critical missing documentation. Template:

```markdown
# Python API Reference

## Quick Start

\`\`\`python
from aletheia import StreamingClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC and convert to JSON
dbc_json = dbc_to_json("vehicle.dbc")

# Create streaming client for LTL verification
with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([
        Signal("Speed").between(0, 300).always().to_dict()
    ])
    client.start_stream()

    # Send frames for verification
    frame = bytes([0x10, 0x27, 0, 0, 0, 0, 0, 0])
    response = client.send_frame(timestamp=100, can_id=0x100, data=frame)
    print(response)
\`\`\`

## API Reference

### StreamingClient
[Streaming protocol for LTL verification]

### Signal DSL
[Fluent interface for building LTL properties]

### dbc_converter
[Convert .dbc files to JSON format]

## Complete Examples
[Full working programs]
```

#### 13. **Module Header Comments** (Agda files)
Every Agda module needs header comment:

```agda
{-# OPTIONS --safe --without-K #-}

-- Module: Aletheia.Protocol.JSON
-- Purpose: JSON data types, parser, and formatter with rational number support.
-- Dependencies: Parser.Combinators, Data.Rational
-- Role: Core JSON handling for streaming protocol.
--
-- Rationals are represented as {"numerator": n, "denominator": d} objects
-- for exact representation of values like 1/3 that have no finite decimal.
module Aletheia.Protocol.JSON where
```

**Action**: Add headers to all 33 Agda modules (systematic pass)

## Implementation Plan

### Phase 1: Remove Dead Code (10 min)
- ✅ Remove SizedStream.agda (unused)
- ✅ Move CLAUDE.md to root

### Phase 2: Consolidate Cleanup Docs (15 min)
- Delete CLEANUP_PLAN.md, CLEANUP_SUMMARY.md, DIRECTORY_STRUCTURE_PLAN.md
- Keep REORGANIZATION_SUMMARY.md as the single record

### Phase 3: Consolidate Phase Docs (30 min)
- Create docs/architecture/CHANGELOG.md (extract key info from phase docs)
- Delete phase docs (move to archive if needed)

### Phase 4: Update Main Architecture Docs (1 hour)
- Update DESIGN.md:
  - Reflect Phase 2B.1 completion
  - Merge streaming protocol from PHASE2B_ARCHITECTURE.md
  - Update phase plan status
  - Remove YAML references
- Create PROTOCOL.md (extract from DESIGN.md, PHASE2B_ARCHITECTURE.md, LTL_JSON_SCHEMA.md)
- Delete PHASE2B_ARCHITECTURE.md and LTL_JSON_SCHEMA.md

### Phase 5: Create Python API Docs (2 hours)
- Create docs/development/PYTHON_API.md
- Include examples from existing test files
- Document all public API classes and functions
- Add complete working examples

### Phase 6: Add Module Header Comments (2 hours)
- Systematic pass through all 33 Agda modules
- Add header comment to each file explaining:
  - Purpose
  - Role in architecture
  - Key dependencies
  - Important design decisions

### Phase 7: Verify and Test (30 min)
- Check all internal doc links work
- Verify no broken references
- Build and test still pass
- Git commit with clear message

## Final Structure

```
aletheia/
├── README.md                              # Project overview
├── CLAUDE.md                              # Instructions for Claude Code
│
├── docs/
│   ├── architecture/
│   │   ├── DESIGN.md                      # Master design doc (UPDATED)
│   │   ├── PROTOCOL.md                    # JSON protocol spec (NEW)
│   │   ├── ARCHITECTURAL_ANALYSIS.md      # CAN decisions (keep)
│   │   └── CHANGELOG.md                   # Phase history (NEW)
│   │
│   ├── development/
│   │   ├── BUILDING.md                    # Build instructions
│   │   ├── DEVELOPMENT.md                 # Dev workflow
│   │   └── PYTHON_API.md                  # Python API reference (NEW)
│   │
│   └── cleanup/
│       └── REORGANIZATION_SUMMARY.md      # Repo restructuring record
│
├── src/Aletheia/
│   └── [All 33 modules with header comments]
│
└── [rest of project structure]
```

## Benefits

1. **Single Source of Truth**: Each piece of information appears exactly once
2. **Current**: All docs reflect Phase 2B.1 completion status
3. **Organized**: Clear hierarchy (architecture, development, cleanup)
4. **Accessible**: Python API docs for primary user base
5. **Maintainable**: Less duplication = easier to keep updated
6. **Professional**: Clean, focused documentation structure

## Verification Checklist

After implementation:
- [ ] No duplicate information across docs
- [ ] All docs reflect current state (Phase 2B.1 complete, JSON protocol)
- [ ] Python API fully documented with examples
- [ ] All 33 Agda modules have header comments
- [ ] All internal links work
- [ ] Build and tests pass
- [ ] Git history is clean

## Estimated Time

- **Quick cleanup** (Phase 1-3): 1 hour
- **Full consolidation** (Phase 1-7): 6 hours

## Priority Order

If doing incrementally:
1. **CRITICAL**: Python API docs (primary user-facing gap)
2. **HIGH**: Update DESIGN.md to reflect Phase 2B.1
3. **HIGH**: Create PROTOCOL.md (integration developers need this)
4. **MEDIUM**: Consolidate phase docs → CHANGELOG.md
5. **MEDIUM**: Add module header comments
6. **LOW**: Consolidate cleanup docs (already complete, just cleanup)
