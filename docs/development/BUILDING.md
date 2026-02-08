# Building Aletheia

---
**Version**: 0.3.2
**Last Updated**: 2026-02-08
**Phase**: See [PROJECT_STATUS.md](../../PROJECT_STATUS.md) for current phase
---

This document provides step-by-step instructions for building Aletheia from source.

## Prerequisites

### System Requirements

- **OS**: Linux, macOS, or Windows with WSL2
- **RAM**: 4GB minimum, 8GB recommended (Agda compilation can be memory-intensive)
- **Disk**: ~2GB for dependencies and build artifacts

### Required Software

#### 1. GHC (Glasgow Haskell Compiler)

**Version**: 9.4.x or 9.6.x recommended

**Installation**:
```bash
# Using ghcup (recommended)
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.6.7
ghcup set ghc 9.6.7

# Verify installation
ghc --version
```

#### 2. Cabal

**Version**: 3.12.1.0 (recommended)
```bash
# Usually installed with ghcup
ghcup install cabal 3.12.1.0
ghcup set cabal 3.12.1.0

# Update package index
cabal update

# Verify installation
cabal --version
# Should output: cabal-install version 3.12.1.0
```

#### 3. Agda

**Version**: 2.8.0 (exact version required)
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
# Add to ~/.bashrc or ~/.zshrc
export PATH="$HOME/.cabal/bin:$PATH"

# Then reload
source ~/.bashrc  # or source ~/.zshrc
```

#### 4. Agda Standard Library

**Version**: 2.3 (exact version required)
```bash
# Clone the standard library
mkdir -p ~/.agda
cd ~/.agda
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
git checkout v2.3

# Register the library with Agda
mkdir -p ~/.agda
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

#### 5. Python

**Minimum version: 3.12** (required by package dependencies)
**Recommended: 3.13.7** (latest stable)

The project uses modern Python type hints with `from __future__ import annotations`.

```bash
# Check if Python is installed (must be 3.12+)
python3 --version
# Should output: Python 3.12.0 or higher

# If you need to install Python 3.13.7:
# - On Ubuntu/Debian: Use deadsnakes PPA
# - On macOS: Use Homebrew or pyenv
# - On other systems: Download from python.org
```

**Installing Python 3.13.7 on Ubuntu/Debian**:
```bash
sudo apt-get update
sudo apt-get install software-properties-common
sudo add-apt-repository ppa:deadsnakes/ppa
sudo apt-get update
sudo apt-get install python3.13 python3.13-venv python3.13-dev
```

**Installing Python 3.13.7 on macOS**:
```bash
# Using Homebrew
brew install python@3.13

# Or using pyenv (recommended for multiple versions)
brew install pyenv
pyenv install 3.13.7
pyenv global 3.13.7
```

## Building Aletheia

### 1. Clone the Repository
```bash
git clone <repository-url>
cd aletheia
```

### 2. Set Up Python Virtual Environment

**IMPORTANT**: Always use a virtual environment to avoid conflicts with system Python packages.
```bash
# Create virtual environment
python3 -m venv .venv

# Activate the virtual environment
source .venv/bin/activate

# Verify you're in the virtual environment
which python3
# Should show: /path/to/aletheia/.venv/bin/python3

# Upgrade pip in the virtual environment
pip install --upgrade pip setuptools wheel
```

**Note**: You need to activate the virtual environment every time you work on the project:
```bash
cd /path/to/aletheia
source .venv/bin/activate
```

To deactivate when done:
```bash
deactivate
```

### 3. Build All Components

The project uses [Shake](https://shakebuild.com/) as its build system. Shake is declared as a
Cabal dependency in `shake.cabal` at the project root, so **no separate installation is needed** —
`cabal run shake` fetches and builds Shake automatically on first use.

```bash
# Ensure you're in the project root directory
cd /path/to/aletheia

# Build everything (Agda → Haskell → libaletheia-ffi.so)
cabal run shake -- build

# This will:
# 1. Compile Agda sources to Haskell (MAlonzo)
# 2. Build shared library via Cabal → build/libaletheia-ffi.so
#
# First build takes ~1 minute (compiles standard library + Shake itself)
# Subsequent builds are much faster (only changed modules)
```

### 4. Verify the Build
```bash
# Verify the shared library was built
python3 -c "from aletheia.client import _find_ffi_library; print(_find_ffi_library())"
# Should print path to libaletheia-ffi.so
```

### 5. Install Python Package

**IMPORTANT**: Make sure your virtual environment is activated!
```bash
# Verify virtual environment is active
which python3
# Should show: /path/to/aletheia/.venv/bin/python3

# Install Python package using Shake
cabal run shake -- install-python

# Or manually:
cd python
pip install -e .
cd ..

# Verify installation
python3 -c "import aletheia; print(aletheia.__version__)"
# Should output: 0.3.2
```

### 6. Run Tests
```bash
# Ensure virtual environment is active
source .venv/bin/activate

# Install test dependencies
cd python
pip install -e ".[dev]"

# Run tests
python3 -m pytest tests/ -v

# Try an example
cd ../examples
python3 simple_verification.py
```

### 7. System Installation (Optional)

For deployment outside the git repository (Docker, CI/CD, shared servers), Aletheia can be installed
as a self-contained bundle with all GHC runtime libraries included. No GHC or Agda is needed at
runtime — only Python 3.12+.

#### Prerequisites

```bash
# patchelf is required to patch shared library RUNPATH
sudo apt install patchelf      # Ubuntu/Debian
# brew install patchelf        # macOS
# sudo dnf install patchelf    # Fedora
```

#### Install

```bash
# Install to ~/.local (default)
cabal run shake -- install

# Install to a custom prefix
PREFIX=/opt/aletheia cabal run shake -- install

# Install + add shell alias for activating the venv
CONFIGURE_SHELL=1 cabal run shake -- install
```

#### Installed Layout

```
$PREFIX/
├── lib/aletheia/
│   ├── libaletheia-ffi.so              # patched RUNPATH=$ORIGIN
│   ├── libHSbase-*.so, libHSrts-*.so   # bundled GHC runtime (~31 MB)
│   ├── venv/                           # Python 3.12+ venv with aletheia
│   └── manifest.txt                    # for uninstall
├── share/doc/aletheia/                 # documentation
└── share/aletheia/examples/            # example scripts
```

#### Activate and Use

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

If you installed with `CONFIGURE_SHELL=1`, you can use:
```bash
aletheia-env   # alias that activates the venv
```

#### Uninstall

```bash
cabal run shake -- uninstall                          # default prefix
PREFIX=/opt/aletheia cabal run shake -- uninstall     # custom prefix
```

#### Docker Multi-Stage Build

```dockerfile
# Stage 1: Build with GHC + Agda
FROM haskell:9.6.7 AS builder

RUN cabal update && cabal install Agda-2.8.0
RUN apt-get update && apt-get install -y patchelf python3 python3-venv

WORKDIR /build
COPY . .
RUN cabal run shake -- build
RUN PREFIX=/opt/aletheia cabal run shake -- install

# Stage 2: Runtime (no GHC needed)
FROM python:3.13-slim

COPY --from=builder /opt/aletheia /opt/aletheia

# Activate and use
ENV PATH="/opt/aletheia/lib/aletheia/venv/bin:$PATH"
RUN python3 -c "from aletheia import AletheiaClient; print('OK')"
```

## Common Build Commands
```bash
# Always ensure you're in the project root
cd /path/to/aletheia

# Activate Python virtual environment (for Python commands)
source .venv/bin/activate

# Build commands
cabal run shake -- build              # Full pipeline: Agda → Haskell → libaletheia-ffi.so
cabal run shake -- build-agda         # Compile Agda to Haskell only (no .so)
cabal run shake -- install-python     # Build + install Python package (pip install -e .)
cabal run shake -- check-properties   # Type-check all proof modules
cabal run shake -- clean              # Remove build artifacts
cabal run shake -- install            # System install (default: ~/.local)
cabal run shake -- uninstall          # Remove system install
```

## Creating Convenient Aliases (Optional)

To avoid typing repeatedly:
```bash
# Add to ~/.bashrc or ~/.zshrc

# Alias for shake
alias shake='cabal run shake --'

# Function to activate aletheia environment
aletheia-env() {
    cd /path/to/aletheia && source .venv/bin/activate
}

# Reload shell
source ~/.bashrc  # or source ~/.zshrc

# Now you can use:
aletheia-env      # cd to project and activate venv
shake build       # Build project
shake clean       # Clean build
```

## Workflow Summary
```bash
# Starting a work session
cd /path/to/aletheia
source .venv/bin/activate

# Make changes to Agda/Haskell/Python code
# ... edit files ...

# Build and test
cabal run shake -- build
cd python && python3 -m pytest tests/ -v

# When done
deactivate
```

## Troubleshooting

### Virtual Environment Issues

**Error**: `pip: command not found` after activating venv

**Solution**: Ensure venv was created with a supported Python version (3.12+):
```bash
rm -rf .venv
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
```

**Error**: Python packages installed in wrong location

**Solution**: Verify virtual environment is active:
```bash
which python3
# Should show: .../aletheia/.venv/bin/python3
# NOT: /usr/bin/python3 or similar system path
```

### Agda Compilation Fails

**Error**: `Module not found: Data.Nat`

**Solution**: Ensure agda-stdlib is correctly registered:
```bash
cat ~/.agda/libraries  # Should list path to standard-library.agda-lib
cat ~/.agda/defaults   # Should contain "standard-library"
```

**Error**: `Unknown field 'version'` in aletheia.agda-lib

**Solution**: This is just a warning and can be ignored. The `.agda-lib` format doesn't support a `version` field.

### Haskell Compilation Fails

**Error**: `Could not find module 'MAlonzo.Code.Aletheia.Main'`

**Solution**: Ensure Agda compilation succeeded first:
```bash
cabal run shake -- build-agda
ls build/MAlonzo/Code/Aletheia/Main.hs  # Should exist
```

### Python Can't Find Shared Library

**Error**: `FileNotFoundError: libaletheia-ffi.so not found`

**Solution**: Build with Shake (produces `build/libaletheia-ffi.so`):
```bash
cabal run shake -- build
```

### Shake Module Not Found

**Error**: `Could not find module 'Development.Shake'`

**Solution**: This is expected. The project uses a local `shake.cabal` file to manage Shake as a dependency. Always use `cabal run shake --` instead of `shake` directly.

### Out of Memory During Agda Compilation

**Solution**: The standard library compilation is memory-intensive on first build. Try:
```bash
# Close other applications
# Or increase swap space
# Subsequent builds are much faster (only recompile changed files)
```

## Development Build Tips

### Incremental Builds

Shake tracks dependencies automatically. After modifying an Agda file:
```bash
cabal run shake -- build  # Only rebuilds affected modules
```

### Type-Checking Without Compilation

For faster iteration when developing Agda code:
```bash
cd src
agda +RTS -N -RTS Aletheia/YourModule.agda  # Type-check only (parallel)
```

**Important**: Always use `+RTS -N -RTS` for parallel type-checking. Without it, modules like `StreamState.agda` and `Main.agda` can take >2 minutes instead of ~17 seconds.

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

### Checking Individual Modules
```bash
cd src
agda +RTS -N -RTS Aletheia/Main.agda              # Check Main and all dependencies
agda +RTS -N -RTS Aletheia/Protocol/Command.agda  # Check just Command module
```

## Platform-Specific Notes

### macOS

- Install command-line tools: `xcode-select --install`
- If using Homebrew GHC: ensure ghcup takes precedence in PATH
- Python 3.13 via Homebrew: `brew install python@3.13`

### Windows (WSL2)

- Use Ubuntu 22.04 LTS or later
- Ensure WSL2 has sufficient memory allocated (8GB recommended)
- Line endings: the repository uses Unix (LF) line endings
- Install Python 3.13 from deadsnakes PPA (see Ubuntu instructions above)

### Linux

- Install GMP development libraries: `sudo apt-get install libgmp-dev`
- Install ncurses: `sudo apt-get install libncurses-dev`
- On some distributions, you may need: `sudo apt-get install libtinfo-dev`
- For Python 3.13: use deadsnakes PPA on Ubuntu/Debian (see above)

## Build Performance

### First Build
- Agda compilation: ~45-60 seconds (compiles standard library)
- Haskell compilation: ~5-10 seconds
- **Total**: ~1 minute

### Incremental Builds
- Only changed Agda modules: ~5-15 seconds
- Only Haskell changes: ~3-5 seconds
- Python package install: ~2 seconds

## Next Steps

After successful build:

1. **Try examples**: `python3 examples/simple_verification.py`
2. **Read the interfaces**: See [INTERFACES.md](INTERFACES.md) (Check API, YAML, Excel)
3. **Review architecture**: See [DESIGN.md](../architecture/DESIGN.md)
4. **Read the project pitch**: See [PITCH.md](../PITCH.md) for why Aletheia exists

## Getting Help

If you encounter issues not covered here:

1. Check that all prerequisites are installed with correct versions
2. Verify Python virtual environment is active: `which python3`
3. Try a clean build: `cabal run shake -- clean && cabal run shake -- build`
4. Verify shared library: `python3 -c "from aletheia.client import _find_ffi_library; print(_find_ffi_library())"`
5. Check the project structure matches the expected layout

## Summary of Key Commands
```bash
# Initial setup (once)
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip setuptools wheel
cd python && pip install -e ".[dev]" && cd ..
cabal update

# Regular development workflow
cd /path/to/aletheia
source .venv/bin/activate         # Activate Python environment
cabal run shake -- build          # Full pipeline → build/libaletheia-ffi.so
cd python && python3 -m pytest tests/ -v  # Run tests

# When done
deactivate                       # Deactivate virtual environment
```

## Virtual Environment Best Practices

1. **Always activate** the virtual environment before running Python commands
2. **Never commit** the `.venv/` directory to git (already in `.gitignore`)
3. **Recreate venv** if you upgrade Python: `rm -rf .venv && python3 -m venv .venv && source .venv/bin/activate && pip install -e ".[dev]"`
4. **Document dependencies**: When adding Python packages, update `python/pyproject.toml`

---

**Build system working correctly? ✓**
**FFI shared library built? ✓**
**Virtual environment configured? ✓**
**Ready for development!**
