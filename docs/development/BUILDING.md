# Building Aletheia

**Last Updated**: 2026-09-24

This document is the step-by-step guide to building Aletheia from source, and it ends with the ledger of what the build and the bindings depend on, under which licences. Version and release metadata live in [DISTRIBUTION.md](DISTRIBUTION.md); status in [PROJECT_STATUS.md](../../PROJECT_STATUS.md).

> **Note on version pins.** The toolchain versions called out below (GHC 9.8.4, Cabal 3.16.1.0, Agda 2.8.0, agda-stdlib 2.4) are the *tested* combination, not the *only* combination that works. We pin them in CI and refresh them deliberately during AGENTS.md review rounds; the **Last Updated** stamp at the top of this file says when these versions were last revalidated. If you hit a build failure after a long gap, first check whether your local toolchain has drifted past the listed versions, then check whether this document has been updated more recently than your last build.

## Contents

- [Toolchain support policy](#toolchain-support-policy)
- [Prerequisites](#prerequisites)
- [Building Aletheia](#building-aletheia)
- [Common Build Commands](#common-build-commands)
- [Troubleshooting](#troubleshooting)
- [Development Build Tips](#development-build-tips)
- [Platform-Specific Notes](#platform-specific-notes)
- [Next Steps](#next-steps)
- [Dependencies and Licenses](#dependencies-and-licenses)

---

## Toolchain support policy

**This section is the single source of truth for the compiler/runtime support policy; other docs link here rather than restating it.**

Aletheia is built and tested against the **latest stable** compilers, currently **Clang 23**, **Python 3.14**, and **Go 1.26**. Older releases may work, but they are not supported: the project tracks the latest stable toolchain and moves forward to the next release when it ships, rather than promising a minimum-version floor. g++ is not supported for the C++ binding (the sanitizer lanes need clang's `-fsanitize-ignorelist`, and UB can differ between compiler versions, so the shipped compiler is pinned). Two caveats are hard requirements, not "may work": Python 3.14 (PEP 758 syntax is used) and a C++23 standard library for the C++ binding (`<expected>` / `<format>`). CI builds the C++ binding against libstdc++ 15, taken from the toolchain PPA because ubuntu-24.04 ships 14; that is the same "latest stable" rule the compilers follow, and it is what the C++23 library surface is tested against.

## Prerequisites

### System requirements

- **OS**: Linux, macOS, or Windows with WSL2
- **RAM**: 4GB recommended. A cold build peaks around 1.5GB (measured): the MAlonzo compile runs as a single GHC `--make` process, so workers do not stack, heap-capped at 3GB via `-M3G`. Ad-hoc `agda` type-checking is capped at 16GB (`-M16G`) only as a runaway-elaboration tripwire, not memory you must provision.
- **Disk**: ~2GB for dependencies and build artifacts

### System libraries

The build links against `libgmp` (arbitrary-precision arithmetic, through GHC's `ghc-bignum`; the Agda rationals lean on it heavily), and GHC needs `libncurses` / `libtinfo`. Install them before the language toolchains:

```bash
sudo apt-get install libgmp-dev libncurses-dev   # Debian/Ubuntu (some releases also need libtinfo-dev)
sudo dnf install gmp-devel ncurses-devel         # Fedora/RHEL
sudo pacman -S gmp ncurses                        # Arch
brew install gmp                                  # macOS
```

A missing `libgmp` surfaces as `ld: cannot find -lgmp` at link time (see [Troubleshooting](#missing-libgmp-ld-cannot-find--lgmp)).

### GHC (Glasgow Haskell Compiler)

**Version**: 9.8.x recommended (9.8.4 known-good)

```bash
# Using ghcup (recommended); 9.8.4 is the tested version, other 9.8.x should work
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.8.4
ghcup set ghc 9.8.4

# Verify installation
ghc --version
```

### Cabal

**Version**: 3.16.1.0 (recommended)

```bash
# Usually installed with ghcup
ghcup install cabal 3.16.1.0
ghcup set cabal 3.16.1.0

# Update package index
cabal update

# Verify installation
cabal --version
# Should output: cabal-install version 3.16.1.0
```

### Agda

**Version**: 2.8.0 (exact version required; MAlonzo code generation changed between versions, and the standard library 2.4 targets this release)

```bash
# Install via cabal
cabal install Agda-2.8.0

# Verify installation
agda --version
# Should output: Agda version 2.8.0

# Verify Agda is in PATH
which agda
```

**Note**: After installation, ensure `~/.cabal/bin` is in your PATH:

```bash
# bash/zsh: Add to ~/.bashrc or ~/.zshrc
export PATH="$HOME/.cabal/bin:$PATH"
source ~/.bashrc  # or source ~/.zshrc

# fish: Add to ~/.config/fish/config.fish
fish_add_path ~/.cabal/bin
```

### Agda standard library

**Version**: 2.4 (exact version required)

```bash
# Clone the standard library
mkdir -p ~/.agda
cd ~/.agda
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
git checkout v2.4

# Register the library with Agda
echo "$HOME/.agda/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries
echo "standard-library" >> ~/.agda/defaults
```

**Verify installation**:

```bash
# Create test file
cat > /tmp/test.agda <<EOF
module test where
open import Data.Nat
x : ℕ
x = 42
EOF

# Try to compile
cd /tmp
agda test.agda
# Should succeed with no errors
```

**Troubleshooting Agda stdlib**:

- **`Cannot find module Data.Nat`**: Check that `~/.agda/libraries` contains the full path to `standard-library.agda-lib` and that `~/.agda/defaults` contains `standard-library`.
- **Version mismatch errors**: Ensure you checked out `v2.4` (not `main`). Run `cd ~/.agda/agda-stdlib && git checkout v2.4`.

### Python

**Minimum version: 3.14** (required by `python/pyproject.toml`: `requires-python = ">=3.14"`). The build tooling invokes `python3.14` for the dev venv, and the project uses 3.14-only syntax (PEP 758).

```bash
# Check if Python is installed (must be 3.14+)
python3.14 --version
# Should output: Python 3.14.0 or higher
```

**Installing Python 3.14 on Ubuntu 26.04+** (in apt, no PPA needed):

```bash
sudo apt-get update
sudo apt-get install python3.14 python3.14-venv python3.14-dev
```

**Installing Python 3.14 on Ubuntu 24.04/22.04** (deadsnakes PPA required):

```bash
sudo apt-get update
sudo apt-get install software-properties-common
sudo add-apt-repository ppa:deadsnakes/ppa
sudo apt-get update
sudo apt-get install python3.14 python3.14-venv python3.14-dev
```

**Installing Python 3.14 on macOS**:

```bash
# Using Homebrew
brew install python@3.14

# Or using pyenv (recommended for multiple versions)
brew install pyenv
pyenv install 3.14
pyenv global 3.14
```

On other systems, download from python.org.

### CMake (for the C++ binding only)

**Version**: 3.25+ required

```bash
cmake --version
# Should output: cmake version 3.25 or higher
```

Only needed if building the C++ binding (`cpp/`). Not required for Agda/Python development.

### Go (for the Go binding only)

**Version**: 1.24+ required (the `go.mod` floor; the project tracks the latest stable Go, currently 1.26, per the [toolchain support policy](#toolchain-support-policy))

```bash
go version
# Should output: go version go1.24 or higher
```

Only needed if building/testing the Go binding (`go/`). Not required for Agda/Python/C++ development.

### Rust (for the Rust binding only)

**Version**: a Rust 2021-edition toolchain (`rustc` / `cargo`); CI runs the latest stable Rust.

```bash
rustc --version && cargo --version
```

Only needed if building/testing the Rust binding (`rust/`). Not required for Agda/Python/C++/Go development.

## Building Aletheia

### Clone the repository

```bash
git clone <repository-url>
cd aletheia
```

### Set up the Python virtual environment

Always use a virtual environment to avoid conflicts with system Python packages, and create it under `python/`: `run_ci.py`, the mutation/stability runners, and basedpyright's `venvPath` all resolve `python/.venv`.

```bash
cd python
python3.14 -m venv .venv

# Activate the virtual environment
source .venv/bin/activate          # fish: source .venv/bin/activate.fish

# Verify you're in the virtual environment
which python3
# Should show: /path/to/aletheia/python/.venv/bin/python3

# Upgrade pip in the virtual environment
pip install --upgrade pip setuptools wheel
cd ..  # back to the project root for the build steps below
```

You need to activate the virtual environment every time you work on the project (`source python/.venv/bin/activate` from the project root; fish: `activate.fish`), and `deactivate` leaves it. **If you see `ModuleNotFoundError: No module named 'aletheia'`** when running tests or `python3 -m aletheia`, you likely forgot to activate the venv. When adding Python packages, update `python/pyproject.toml`; the `.venv/` directory is gitignored and never committed.

### Build all components

The project uses [Shake](https://shakebuild.com/) as its build system. Shake is declared as a Cabal dependency in `shake.cabal` at the project root, so **no separate installation is needed**: `cabal run shake` fetches and builds Shake automatically on first use.

```bash
# Ensure you're in the project root directory
cd /path/to/aletheia

# Build everything (Agda → Haskell → libaletheia-ffi.so)
cabal run shake -- build

# This will:
# 1. Compile Agda sources to Haskell (MAlonzo)
# 2. Build shared library via Cabal → build/libaletheia-ffi.so
```

The build is incremental: how long a cold, a no-op and a one-module build take, and why the dependency graph makes that honest, is under [Incremental Builds](#incremental-builds) below.

### Verify the build

```bash
# Verify the shared library was built
ls -la build/libaletheia-ffi.so
# Should show the shared library file
```

### Install the Python package

With the virtual environment active:

```bash
# Install Python package using Shake
cabal run shake -- install-python

# Or manually:
cd python
pip install -e .
cd ..

# Verify installation: prints the version python/pyproject.toml declares
python3 -c "import aletheia; print(aletheia.__version__)"
```

### Run the tests

```bash
# Python tests
source python/.venv/bin/activate   # fish: source python/.venv/bin/activate.fish
cd python && pip install -e ".[dev]"
python3 -m pytest tests/ -v

# C++ tests
cd ../cpp && cmake -B build -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 && cmake --build build && ctest --test-dir build

# Go tests (requires cgo)
cd ../go && go test ./aletheia/ -v -count=1 -race
# The optional Excel loader is the separate go/excel module: cd excel && go test ./...

# Rust tests (default `yaml` feature; opt-in `async`)
cd ../rust && ALETHEIA_LIB=../build/libaletheia-ffi.so cargo test

# Try an example
cd ..
python3 examples/simple_verification.py
```

> **`ALETHEIA_LIB`** points a binding at the shared library when it is not on the loader path: required for the Rust `cargo test` above, and read first by the C++ real-FFI ctests and the Go tests, which otherwise fall back to the build tree (the Go tests skip the FFI cases when neither is found). Point it at `build/libaletheia-ffi.so`.

### System installation (optional)

For integrating `libaletheia-ffi.so` into C, C++, Go, or Rust projects, see [DISTRIBUTION.md](DISTRIBUTION.md).

For deployment outside the git repository (Docker, CI/CD, shared servers), Aletheia can be installed as a self-contained bundle with all GHC runtime libraries included. No GHC or Agda is needed at runtime, only Python 3.14+.

`patchelf` is required to patch the shared libraries' RPATH:

```bash
sudo apt install patchelf      # Ubuntu/Debian
# brew install patchelf        # macOS
# sudo dnf install patchelf    # Fedora
```

```bash
# Install to ~/.local (default)
cabal run shake -- install

# Install to a custom prefix
PREFIX=/opt/aletheia cabal run shake -- install

# Install + add shell alias for activating the venv
CONFIGURE_SHELL=1 cabal run shake -- install
```

Installed layout:

```
$PREFIX/
├── lib/aletheia/
│   ├── libaletheia-ffi.so              # patched RPATH=$ORIGIN
│   ├── libHSbase-*.so, libHSrts-*.so   # bundled GHC runtime
│   ├── venv/                           # Python 3.14+ venv with aletheia
│   └── manifest.txt                    # for uninstall
├── share/doc/aletheia/                 # documentation
└── share/aletheia/examples/            # example scripts
```

Activate and use:

```bash
# bash/zsh
source ~/.local/lib/aletheia/venv/bin/activate
python3 -c "from aletheia import AletheiaClient; print('OK')"
deactivate

# fish
source ~/.local/lib/aletheia/venv/bin/activate.fish
python3 -c "from aletheia import AletheiaClient; print('OK')"
deactivate
```

If you installed with `CONFIGURE_SHELL=1`, the `aletheia-env` alias activates the venv. Uninstall with the same prefix:

```bash
cabal run shake -- uninstall                          # default prefix
PREFIX=/opt/aletheia cabal run shake -- uninstall     # custom prefix
```

For Docker deployment (Dockerfile, build commands, runtime image), see [DISTRIBUTION.md](DISTRIBUTION.md#docker).

### Install git hooks (recommended for contributors)

Aletheia's CI is local-first: a pre-push hook runs the full offline correctness sweep before allowing push (`tools/run_ci.py`), and a pre-commit hook runs the compile-free FAST gate tier on the staged content and the IWYU import gate on staged `.agda` files, refusing the commit on any failure. Install both with:

```bash
tools/install_hooks.py
```

Idempotent (safe to re-run; preserves any existing hooks by backing them up). After install:

| Hook | When | What runs | Severity |
|---|---|---|---|
| `pre-commit` | `git commit` | `tools/run_ci.py --fast` on the staged content, then `tools/iwyu.py --check --wait-lock` on staged `.agda` files (the single scope-aware `.agdai` IWYU tool; it queues behind a running Agda tool) | **Blocking**: refuses the commit on any finding, and on a check that never reached a verdict |
| `pre-push` | `git push` | `tools/run_ci.py`, the full offline correctness sweep (~22-30 min warm) | **Blocking**: refuses push on any non-zero exit |

Bypass either hook with `--no-verify` when needed (e.g. doc-only fixes that don't affect gates):

```bash
git commit --no-verify   # skip the pre-commit FAST tier + IWYU gate
git push   --no-verify   # skip pre-push CI sweep
```

Both hooks are optional; the project is fully functional without them. They are strongly recommended for contributors because they catch many issues before they reach the maintainer's review. The sweep's gates, the IWYU gate among them, are described in [CI_LOCAL.md](CI_LOCAL.md).

## Common Build Commands

```bash
# Always ensure you're in the project root
cd /path/to/aletheia

# Activate Python virtual environment (for Python commands)
source python/.venv/bin/activate

# Build commands
cabal run shake -- build              # Full pipeline: Agda → Haskell → libaletheia-ffi.so (incremental)
cabal run shake -- build-agda         # Compile Agda to Haskell only (no .so)
cabal run shake -- gen-ffi-modules    # Regenerate the MAlonzo module list in aletheia.cabal (after adding/removing an Agda module)
cabal run shake -- iwyu               # Regenerate the relevant .agdai + run the import (IWYU) analysis, no full .hs/.so rebuild
cabal run shake -- install-python     # Build + install Python package (pip install -e .)
cabal run shake -- check-properties   # Type-check all proof modules
cabal run shake -- dist               # Package dist/aletheia.tar.gz (C/C++/Go/Rust)
cabal run shake -- docker             # Build Docker runtime image (requires dist)
cabal run shake -- clean              # Remove build artifacts, the Agda interfaces under _build/ included
cabal run shake -- install            # System install (default: ~/.local)
cabal run shake -- uninstall          # Remove system install
```

## Troubleshooting

### Virtual Environment Issues

**Error**: `pip: command not found` after activating venv, or imports that worked yesterday start failing, or `basedpyright` runs against the system Python instead of your venv (a system Python upgrade invalidates a venv).

**Solution**: Recreate the venv with a supported Python version (3.14+):

```bash
deactivate  # if already active
cd python
rm -rf .venv
python3.14 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install -e '.[all,dev]'
cd ..
```

**Error**: Python packages installed in wrong location

**Solution**: Verify virtual environment is active:

```bash
which python3
# Should show: .../aletheia/python/.venv/bin/python3
# NOT: /usr/bin/python3 or similar system path
```

### Agda Compilation Fails

**Error**: `Module not found: Data.Nat`

**Solution**: Ensure agda-stdlib is correctly registered:

```bash
cat ~/.agda/libraries  # Should list path to standard-library.agda-lib
cat ~/.agda/defaults   # Should contain "standard-library"
```

### Haskell Compilation Fails

**Error**: `Could not find module 'MAlonzo.Code.Aletheia.Main'`

**Solution**: Ensure Agda compilation succeeded first:

```bash
cabal run shake -- build-agda
ls build/MAlonzo/Code/Aletheia/Main.hs  # Should exist
```

### Python Can't Find Shared Library

**Error**: `FileNotFoundError: libaletheia-ffi.so not found`

**Solution**: Build with Shake (produces `build/libaletheia-ffi.so`), then check what the loader resolves:

```bash
cabal run shake -- build
python3 -c "from aletheia.client._ffi import find_ffi_library; print(find_ffi_library())"
```

### Shake Module Not Found

**Error**: `Could not find module 'Development.Shake'`

**Solution**: This is expected. The project uses a local `shake.cabal` file to manage Shake as a dependency. Always use `cabal run shake --` instead of `shake` directly.

### Missing libgmp (`ld: cannot find -lgmp`)

**Error**: Linker error at the end of `cabal build` or `cabal run shake -- build`, typically `ld: cannot find -lgmp`.

**Solution**: Install the GMP development package for your distribution ([System libraries](#system-libraries)), then run `cabal run shake -- clean && cabal run shake -- build`.

### Clang Version / C++23 Standard Library for C++ Binding

**Error**: `std::expected` / `std::format` / spaceship operator not found when building `cpp/`, `error: no member named 'byte' in namespace 'std'`, or `error: use of undeclared identifier 'std::format'`.

**Solution**: The C++ binding supports the **latest stable Clang only** (currently 23; see [Toolchain support policy](#toolchain-support-policy)), and g++ is not supported (the sanitizer lanes need clang's `-fsanitize-ignorelist`). It also needs a libstdc++/libc++ that provides C++23 (`<expected>`); older Clang may work but is unsupported. Check with:

```bash
clang++-23 --version   # expect 23.x (latest stable)
cmake -B cpp/build -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23
```

**Error**: `cmake` reports missing `nlohmann/json` or `Catch2`

**Solution**: These are fetched automatically via CMake FetchContent. Ensure CMake 3.25+ and an internet connection on first build, then configure and build as above.

### Go Build/Test Fails

**Error**: `go build -tags netgo` or a distroless container fails with `undefined: C.dlopen`.

**Solution**: The Go binding REQUIRES cgo: `FFIBackend` uses `dlopen`/`dlsym` via C trampolines. There is no pure-Go fallback. Use `CGO_ENABLED=1` (the default) and include `libaletheia-ffi.so` in the final image. For test runs that don't need the FFI backend, `MockBackend` is pure Go and can be used under `CGO_ENABLED=0`.

**Error**: `cgo: C compiler "gcc" not found`

**Solution**: Install build-essential: `sudo apt-get install build-essential`

**Error**: `cannot open shared object file: No such file or directory` at test time

**Solution**: Point `ALETHEIA_LIB` at the built library:

```bash
export ALETHEIA_LIB=/path/to/aletheia/build/libaletheia-ffi.so
cd go && go test ./aletheia/ -v -count=1 -race
```

### MAlonzo Symbol Not Found at FFI Load Time

**Error**: `aletheia_send_frame` or `aletheia_process` resolves, but the first call crashes with `Prelude.undefined` or a missing symbol like `_d_processJSONLine_*`.

**Solution**: MAlonzo mangles Agda names on every build. If you added or removed a top-level Agda definition before `processJSONLine` in `Main.agda`, the mangled suffix changed. `cabal run shake -- build` prints the exact `sed` command to update `haskell-shim/src/AletheiaFFI.hs`: apply it, rebuild, and the FFI surface converges again.

## Development Build Tips

### Incremental Builds

`cabal run shake -- build` rebuilds exactly what changed and nothing else:

| Scenario | Time | What happens |
|---|---|---|
| No-op (nothing changed) | ~0.1s | Shake digests the sources, sees no change, does nothing |
| One-module edit | ~12s | Agda regenerates the affected MAlonzo `.hs`; cabal/GHC recompiles only that module + relinks |
| Cold (`clean` first) | ~2m on a 24-core host | Every MAlonzo module compiles through GHC; a truly first-ever build also type-checks the Agda standard library (~20s, cached in `~/.agda` thereafter) |

**How the graph stays honest.** The `libaletheia-ffi.so` Shake rule depends on the `.agda` *sources* (content-hashed via `ChangeModtimeAndDigest`), on `aletheia.agda-lib` (the stdlib pin + `--erasure` flag), and on the FFI shim + `aletheia.cabal`, **not** on the generated MAlonzo `.hs`, which have no producing rule and so cannot be digested at the right moment. cabal then owns the `.hs → .so` edge incrementally via GHC's content-hash recompilation checker: no `touch`, no `rm -rf`. The full rationale lives in the "Development Workflow" notes in [`CLAUDE.md`](../../CLAUDE.md).

**The agda binary is tracked too.** The MAlonzo output is a function of the agda *version*, not only the sources, but the binary is not a file Shake can `need`, so an `AgdaVersion` oracle queries `agda --version` each build and re-fires `build-agda` + the `.so` rule when it changes. With `aletheia.agda-lib` tracked as a file, every build input is accounted for.

**After adding or removing an Agda module**, regenerate the foreign library's MAlonzo module list and commit `aletheia.cabal`:

```bash
cabal run shake -- gen-ffi-modules
```

`aletheia.cabal`'s `foreign-library` lists every MAlonzo module between `-- BEGIN/END GENERATED MALONZO MODULES` markers so cabal tracks the real `.hs → .so` graph (otherwise its up-to-date check skips GHC and ships a stale `.so`). Drift is caught at build time, by GHC's `-Werror=missing-home-modules` (a module added but not listed) or cabal's "module not found" (a listed module removed), so a forgotten regen fails loudly; it never silently ships stale.

**Import analysis without a rebuild.** `cabal run shake -- iwyu` regenerates the relevant `.agdai` interfaces via Agda's interface cache and runs the import (IWYU) analysis with no `.hs`/`.so` rebuild. The IWYU gate is described in [`CI_LOCAL.md`](CI_LOCAL.md).

**The build's incrementality is itself gated.** `tools/check_build_incremental.py` is a behavioral regression test that the build rebuilds what changed, only that, and never ships stale; it runs as `run_ci`'s `build` prerequisite. Its mechanics (when it runs, the `--build-staleness` modes) are documented in [`CI_LOCAL.md`](CI_LOCAL.md).

### Type-Checking Without Compilation

For faster iteration when developing Agda code, type-check one module, with everything it imports, without generating Haskell:

```bash
cd src
agda +RTS -M16G -RTS Aletheia/Main.agda              # Check Main and all dependencies
agda +RTS -M16G -RTS Aletheia/Protocol/Message.agda  # Check just Message module
```

**Important**: Always use `+RTS -M16G -RTS` for ad-hoc type-checking. `-M16G` caps the heap and doubles as a runaway-elaboration tripwire on the memory-limited WSL2 host: without it a runaway elaboration OOM-kills the host instead of failing the build. The `16G` figure is a ceiling to size to your machine, not a constant: set it to what the host can spare, **no more than half of available RAM** is a good rule, so a runaway trips the cap and fails the build cleanly while the other half stays free for the OS. `-N` (parallel GHC) is optional: it gives no measured single-module speedup, even the heaviest modules (`StreamState.agda`, `Main.agda`) type-check in a few seconds at `-N1` and marginally slower at higher `-N`, so parallelism belongs at the whole-build level (Shake's `shakeThreads=0`), not per-module invocations. See AGENTS.md § Agda > Verification for the review-tightening (`-M4G`) variant.

### Verbose Build Output

```bash
cabal run shake -- build -V   # Verbose output
cabal run shake -- build -VV  # Very verbose (shows all commands)
```

### Clean Builds

If you encounter strange errors, try a clean rebuild:

```bash
cabal run shake -- clean
cabal run shake -- build
```

## Platform-Specific Notes

### macOS

- Install command-line tools: `xcode-select --install`
- If using Homebrew GHC: ensure ghcup takes precedence in PATH
- Python 3.14 via Homebrew: `brew install python@3.14`

### Windows (WSL2)

- Use Ubuntu 22.04 LTS or later
- Ensure WSL2 has enough memory allocated (4GB is comfortable; the build peaks ~1.5GB)
- Line endings: the repository uses Unix (LF) line endings
- Python 3.14: see [Python](#python) for the apt and deadsnakes routes

### Linux

- GMP, ncurses and tinfo: see [System libraries](#system-libraries)
- Python 3.14: see [Python](#python) for the apt and deadsnakes routes

## Next Steps

After successful build:

1. **Try examples**: `python3 examples/simple_verification.py`
2. **Read the interfaces**: See [INTERFACES.md](../reference/INTERFACES.md) (Check API, YAML, Excel)
3. **Review architecture**: See [DESIGN.md](../architecture/DESIGN.md)
4. **Read the project pitch**: See [PITCH.md](../PITCH.md) for why Aletheia exists

## Dependencies and Licenses

This section lists the third-party software Aletheia depends on, its licences, and the resulting obligations when distributing Aletheia. Versions are not repeated here: each layer's pins live in the build file the layer names below, and the [Prerequisites](#prerequisites) carry the toolchain versions.

**Optional opt-in tooling not listed below**: `actionlint` (MIT), `act` (MIT) for the GHA meta-checks described in [CI_LOCAL.md](CI_LOCAL.md); `mutmut` (BSD-3), `gremlins` (Apache-2.0), `Mull` (MIT), `cargo-mutants` (MIT) for the mutation-testing lane described in [MUTATION.md](../operations/MUTATION.md). These are dev-only and are NOT linked into `libaletheia-ffi.so`, so they create no distribution obligation.

Aletheia itself is licensed under **BSD-2-Clause** (see [LICENSE.md](../../LICENSE.md)).

### Build-time only

These tools compile Aletheia but are **not** present in the distributed artifact, so they place no obligation on downstream users.

| Dependency | License | Role |
|---|---|---|
| Agda | MIT | Compiler (Agda → Haskell via MAlonzo) |
| Agda standard library | MIT | Type-checked at compile time (pinned in `aletheia.agda-lib`) |
| GHC | BSD-3-Clause | Compiler (Haskell → machine code) |
| Shake | BSD-3-Clause | Build orchestration (pinned in `shake.cabal`) |
| setuptools, wheel | MIT | Python build backend and wheel packaging (`python/pyproject.toml`, `[build-system]`) |

### Runtime, Haskell layer (`libaletheia-ffi.so`)

The compiled shared library links against these Haskell packages, at the versions the pinned GHC ships (`ldd build/libaletheia-ffi.so` lists them); the release bundle carries them as `.so` files with `RPATH=$ORIGIN`.

| Package | License |
|---|---|
| GHC RTS | BSD-3-Clause |
| base | BSD-3-Clause |
| ghc-prim | BSD-3-Clause |
| ghc-bignum | BSD-3-Clause |
| text | BSD-2-Clause |
| binary | BSD-3-Clause |
| containers | BSD-3-Clause |
| bytestring | BSD-3-Clause |
| array | BSD-3-Clause |
| deepseq | BSD-3-Clause |
| pretty | BSD-3-Clause |
| template-haskell | BSD-3-Clause |
| ghc-boot-th | BSD-3-Clause |

System libraries, dynamically linked and not bundled:

| Library | License | Notes |
|---|---|---|
| **libgmp** | **LGPL-3.0+** (GMP is dual-licensed GPL-2.0+ / LGPL-3.0+; taken under the LGPL) | Arbitrary-precision arithmetic (used by ghc-bignum) |
| libffi | MIT | Foreign function interface |
| glibc (libc, libm, libpthread, librt, libdl) | LGPL-2.1+ | C standard library |

### Runtime, C++ layer

The C++ binding (`cpp/`) wraps `libaletheia-ffi.so` via `dlopen`. It has no runtime dependencies beyond the system C++ standard library. Its build-time dependencies are fetched by CMake FetchContent at the versions `cpp/CMakeLists.txt` pins:

| Package | License | Purpose |
|---|---|---|
| nlohmann/json | MIT | JSON serialization/deserialization |
| yaml-cpp | MIT | YAML check-rule loader (statically linked into the C++ binding) |
| OpenXLSX | BSD-3-Clause | Excel template loader (statically linked into the C++ binding) |
| miniz, pugixml | MIT | OpenXLSX's own dependencies, fetched alongside it |
| Catch2 | BSL-1.0 | Unit testing (test-only, not shipped) |

The compiler and standard-library requirements are the [toolchain support policy](#toolchain-support-policy).

### Runtime, Go layer

The Go binding (`go/`) wraps `libaletheia-ffi.so` via cgo + `dlopen`, so it needs cgo (`CGO_ENABLED=1`) and `libdl` (part of glibc, always present). Its third-party modules are pinned in `go/go.mod` and `go/excel/go.mod`:

| Module | License | Pulled in by |
|---|---|---|
| gopkg.in/yaml.v3 | Apache-2.0, with the files ported from libyaml under MIT | `go/aletheia` (YAML check-rule loader) |
| github.com/xuri/excelize/v2 | BSD-3-Clause | `go/excel` (optional module, Excel template loader) |

The optional `go/excel` module is a separate Go module so the heavy `excelize` dependency (and its transitive `golang.org/x/{crypto,net,text}`, `richardlehane/{mscfb,msoleps}`, `tiendc/go-deepcopy`, `xuri/{efp,nfp}` chain) is not imposed on consumers of the core `go/aletheia` module.

### Runtime, Rust layer

The Rust binding (`rust/`) wraps `libaletheia-ffi.so` via the `libloading` crate (runtime `dlopen`/`dlsym`). Its crates are pinned in `rust/Cargo.toml`:

| Crate | License | Role |
|---|---|---|
| libloading | ISC | Runtime `dlopen` of `libaletheia-ffi.so` |
| serde_json | MIT OR Apache-2.0 | JSON protocol serialization/deserialization |
| yaml-rust2 | MIT OR Apache-2.0 | YAML check-rule loader (optional `yaml` feature, on by default) |
| futures-channel | MIT OR Apache-2.0 | Async client reply channel (optional `async` feature) |
| futures-util | MIT OR Apache-2.0 | Stream combinators for the lazy async batch send (optional `async` feature) |

`serde` (MIT OR Apache-2.0) is pulled in transitively by `serde_json`. Dev-only (test/bench, not shipped): `futures` and `yaml-rust2`.

The optional `aletheia-excel` crate (`rust/excel/`) is a separate crate so the `.xlsx` dependency chain is not imposed on core users; its third-party crates, pinned in `rust/excel/Cargo.toml`:

| Crate | License | Role |
|---|---|---|
| calamine | MIT | Read `.xlsx` workbooks (DBC + checks sheets) |
| rust_xlsxwriter | MIT OR Apache-2.0 | Write `.xlsx` templates |
| zip | MIT | `.xlsx` container format (used by the loaders) |

Both crates are edition 2021.

### Runtime, Python layer

The core package has no runtime dependencies outside the standard library; DBC parsing goes through the verified Agda kernel via the FFI. The optional extras in `python/pyproject.toml`:

| Package | Extra | License |
|---|---|---|
| **python-can** | `[can]` | **LGPL-3.0-only** |
| pyyaml | `[yaml]` | MIT |
| openpyxl | `[excel]` | MIT |

Transitive: `et_xmlfile` (MIT, from openpyxl); `packaging` (Apache-2.0 OR BSD-2-Clause), `typing_extensions` (PSF-2.0) and `wrapt` (BSD), from python-can.

### License obligations

**Permissive licenses (MIT, BSD-2-Clause, BSD-3-Clause, Apache-2.0, ISC, PSF-2.0, BSL-1.0)** require only attribution: include the original copyright notice and license text when redistributing (typically in a NOTICES or LICENSE file alongside the distribution). No restrictions on use, modification, or proprietary distribution.

**LGPL-3.0 (libgmp, python-can)**: two runtime dependencies use LGPL-3.0 (libgmp uses LGPL-3.0-or-later; python-can uses LGPL-3.0-only). The obligations:

1. **Dynamic linking**: users must be able to replace the LGPL component with a modified version. Satisfied automatically: libgmp is dynamically linked (via `ldd`), and python-can is a Python package imported at runtime.
2. **Source availability**: recipients of a binary distribution must be able to obtain the source code of the LGPL components. Pointing to the upstream repositories satisfies this: libgmp at https://gmplib.org/, python-can at https://github.com/hardbyte/python-can.
3. **License notice**: include the LGPL-3.0 license text (or a reference to it) alongside the distribution.
4. **No effect on Aletheia's own code**: LGPL does not require Aletheia's BSD-2-Clause source code to be disclosed. The LGPL "weak copyleft" applies only to the LGPL library itself, not to code that uses it through its public API.

**glibc (LGPL-2.1+)**: standard system library present on all Linux installations. Dynamic linking (confirmed via `ldd`) satisfies the LGPL requirements; no special action needed beyond what any Linux application already provides.
