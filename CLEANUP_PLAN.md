# Repository Cleanup Plan

## Files to Remove

### 1. Dead Code (Stubs with Holes)
- ❌ `src/Aletheia/DBC/Semantics.agda` - Just a stub with `{!!}`, only 14 lines

### 2. Old YAML Protocol (Superseded by JSON Protocol)
- ❌ `src/Aletheia/Protocol/Command.agda` - Old YAML Command type (replaced by Data.Message.StreamCommand)
- ❌ `src/Aletheia/Protocol/Handlers.agda` - Old YAML command handlers (replaced by Protocol.StreamState)
- ❌ `src/Aletheia/Protocol/Parser.agda` - Old YAML protocol parser (replaced by Protocol.Routing)

### 3. Old LTL DSL (YAML-based, unused)
- ❌ `src/Aletheia/LTL/DSL/Yaml.agda` - YAML-based LTL parser (replaced by LTL.JSON)
- ❌ `src/Aletheia/LTL/DSL/Parser.agda` - DSL parser for YAML
- ❌ `src/Aletheia/LTL/DSL/Translate.agda` - DSL translation for YAML

### 4. Debug/Test Files
- ❌ `src/Aletheia/DebugDBC.agda` - Debug utilities, 11 lines, not part of main flow

## Files to KEEP (Even if Unused by Runtime)

### Correctness Proofs (Needed for Phase 3)
- ✅ `src/Aletheia/DBC/Properties.agda` - DBC correctness properties
- ✅ `src/Aletheia/Parser/Properties.agda` - Parser correctness properties

### Alternative Implementations (Research/Documentation)
- ✅ `src/Aletheia/Trace/SizedStream.agda` - Sized stream implementation (research)

## Current vs Future Architecture

### OLD (YAML-based, Phase 1):
```
Protocol.Command → Protocol.Handlers → Protocol.Parser
         ↓
  LTL.DSL.Yaml → LTL.DSL.Parser → LTL.DSL.Translate
```

### NEW (JSON-based, Phase 2B):
```
Data.Message → Protocol.Routing → Protocol.JSON
         ↓
   LTL.JSON → LTL.Syntax
```

### SHARED:
```
Protocol.Response (used by both)
```

## Impact Analysis

### Files Being Removed: 7 total
- Protocol: 3 files (~250 lines)
- LTL.DSL: 3 files (~180 lines)  
- Dead code: 1 file (~14 lines)
- **Total: ~444 lines removed**

### Dependencies Cleaned:
- No more YAML dependencies in runtime code
- Simpler module structure
- Clear separation: JSON protocol (new) vs YAML (removed)

## Migration Notes

- Protocol.Response is KEPT (still used by new system for PropertyResult types)
- All functionality replaced:
  - StreamCommand (Data.Message) replaces Command
  - processStreamCommand (Protocol.StreamState) replaces handleCommand (Handlers)
  - parseRequest (Protocol.Routing) replaces YAML parsing
- LTL properties now parsed from JSON (LTL.JSON) instead of YAML DSL

## Testing Plan After Cleanup

1. Remove files
2. Rebuild: `cabal run shake -- build`
3. Run integration test: `python3 test_integration.py`
4. Verify no broken imports
