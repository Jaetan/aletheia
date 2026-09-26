# Coverage floors — operations guide

Every API binding's suite covers at least 80 percent of its lines and 60 percent of its branches, measured by the binding's own coverage tool ([AGENTS.md § Universal Rules](../../AGENTS.md#universal-rules-all-languages)). The lane that measures it is `tools/coverage_run.py`; the record it reads, floors and last measured figures, is [`docs/COVERAGE_BENCH.yaml`](../COVERAGE_BENCH.yaml).

## What is measured

| Binding | Tool | Scope | Second figure |
|---|---|---|---|
| Python | coverage.py, through pytest-cov | the `aletheia` package, its CLI included | branch arcs |
| Go | `go test -cover` | `go/aletheia`, `go/cmd/aletheia`, `go/excel`; the benchmark harness is held out | blocks of the profile |
| C++ | llvm-cov over clang's source-based instrumentation | `cpp/src` and `cpp/include`; suites, harnesses, fuzz targets and fetched libraries held out by path | branches |
| Rust | cargo-llvm-cov | both crates, `rust/src` and `rust/excel/src`, summed | regions |

The first figure is lines everywhere. The second is the finest unit short of a line that the binding's own tool counts, and the record names it per binding: coverage.py and llvm-cov count branches; Go's tool has no branch metric, and its profile's blocks are the bodies of arms; cargo-llvm-cov's branch instrumentation is nightly-only, so on the stable toolchain the second figure is llvm-cov's regions, a span with one execution count. A block and a region are not a branch, and the record says so where that is what the tool has.

## The gate

The floors gate; the recorded figures are measurements. A run over a floor and under the recorded figure passes and prints its distance. A run under a floor fails, as does a tool that will not run, a report the runner cannot read, and a total of zero. The runner archives each tool's own report and its reading of it under `benchmarks/coverage/<short-sha>/`, one JSON per binding and a `summary.json` carrying every verdict.

`tools/check_coverage_setup.py` runs in the always-on sweep and holds the record to its shape without running a suite: every scope path exists, every recorded figure is over its floor, the second figure is one of the units the runner produces, and the cargo-llvm-cov pin is the version the workflow installs.

## Running the lane

```bash
# Every binding the diff vs main could move (the same scoping the mutation lane uses).
tools/run_ci.py --coverage

# The runner directly: all bindings, or one.
ALETHEIA_COVERAGE_NO_DIFF_SCOPE=1 python/.venv/bin/python -m tools.coverage_run
python/.venv/bin/python -m tools.coverage_run --binding go
```

Each suite runs with `ALETHEIA_LIB` naming `build/libaletheia-ffi.so`, so run `cabal run shake -- build` first. The C++ measurement configures and builds its own tree, `cpp/build-coverage`, with `-DALETHEIA_COVERAGE=ON`; the Rust measurement builds under cargo-llvm-cov's own target directory. Both are why the lane is opt-in rather than part of the always-on sweep.

In CI the lane is the `coverage floors` job of `.github/workflows/pr-build-lanes.yml`, skipped on a documentation-only change like the other lanes there, and not yet a required check.

## Installing the tools

coverage.py and pytest-cov come with the `[dev]` extras; Go's tool comes with Go; `llvm-profdata-23` and `llvm-cov-23` come with the clang-23 package. cargo-llvm-cov is pinned exactly in the record and refused at any other version, as mutmut is for the mutation lane:

```bash
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov --version 0.8.7 --locked
```

## Re-taking the record

A change that moves a figure re-takes the record from the run's own fragment: the runner writes `baseline-<binding>.yaml` beside each report, and its `baseline:` block replaces the binding's in `docs/COVERAGE_BENCH.yaml`. A figure is never typed by hand; the static gate refuses a recorded figure under the floor, which is the one a run could not have produced.

## What a low file means

The floors are per binding, so a lane can pass with a file nobody tests. The per-file figures are in each binding's JSON under `per_file`, and a file well under the binding's figure is a finding for that file's review, worked the way the mutation lane's survivors are: a test per line feeding the input that reaches it. The Go mutation record's `not_covered` count is the same gap seen from the other side, the mutants gremlins made on lines no test executes.
