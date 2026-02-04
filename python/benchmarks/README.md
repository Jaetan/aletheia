# Aletheia Performance Benchmarks

This directory contains benchmarks for measuring Aletheia's performance characteristics.

## Benchmarks

### `throughput.py` - Frames per second

Measures raw throughput through the full pipeline (Python -> subprocess -> Haskell -> Agda -> back).

```bash
python3 throughput.py              # Default: 10K frames, 5 runs
python3 throughput.py --frames 50000 --runs 3
```

### `latency.py` - Per-operation latency

Measures latency distribution (p50, p90, p99, p99.9) to understand tail latency.

```bash
python3 latency.py                 # Default: 5K operations
python3 latency.py --ops 10000
```

### `scaling.py` - Scaling characteristics

Tests how performance scales with:
- Trace size (1K to 100K frames)
- Property count (1 to 10 properties)
- Property complexity

```bash
python3 scaling.py                 # Full benchmark
python3 scaling.py --quick         # Faster, reduced iterations
```

## Running All Benchmarks

```bash
cd python/benchmarks
python3 throughput.py && python3 latency.py && python3 scaling.py --quick
```

## Interpreting Results

**Current baseline** (Phase 3 start):
- Target: 1M frames/sec
- Current: ~10K frames/sec (100x improvement needed)

**Key metrics to track**:
1. **Throughput**: Frames/sec for streaming LTL verification
2. **Latency p99**: Tail latency affects real-time applications
3. **Scaling**: Should be O(1) per frame, sub-linear in property count

## Profiling

For deeper analysis, use GHC profiling on the Haskell binary:

```bash
# Build with profiling (modify haskell-shim/aletheia.cabal)
# ghc-options: -prof -fprof-auto

# Run with profiling output
./build/aletheia +RTS -p -RTS < test.jsonl
# Produces aletheia.prof
```

Profile output goes in `profiles/` directory.
