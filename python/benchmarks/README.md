# Aletheia Performance Benchmarks

This directory contains benchmarks for measuring Aletheia's performance characteristics.

## Benchmarks

### `throughput.py` - Frames per second

Measures raw throughput through the full pipeline (Python -> FFI -> Haskell/Agda -> back).

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

### `sysinfo.py` - System info & Docker sizing

Runs a quick benchmark (~5s) and reports memory usage, throughput, and Docker sizing recommendations. Useful for CI or container setup.

```bash
python3 sysinfo.py
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

## Current Performance

Achieved after FFI optimization (Step 3):

| Benchmark | Throughput | Latency |
|-----------|-----------|---------|
| Streaming LTL (3 properties) | 9,229 fps | 108 us/frame |
| Signal Extraction | 8,184 fps | 122 us/frame |
| Frame Building | 5,868 fps | 170 us/frame |

## Profiling

For deeper analysis, use GHC profiling:

```bash
# Build with profiling (modify haskell-shim/aletheia.cabal)
# ghc-options: -prof -fprof-auto

# Run benchmark with profiling enabled
cd python/benchmarks
python3 throughput.py
```

Profile output goes in `profiles/` directory.
