# Aletheia — multi-stage build from source
#
# Stage 1: Build with GHC + Agda (large, discarded)
# Stage 2: Runtime with Python only (small, kept)
#
# Usage:
#   docker build -t aletheia .
#   docker run --rm aletheia python3 -c "from aletheia import AletheiaClient; print('OK')"

# ── Stage 1: Builder ─────────────────────────────────────────────────────────
FROM haskell:9.6.7 AS builder

# Install Agda
RUN cabal update && cabal install Agda-2.8.0

# Install agda-stdlib v2.3
RUN mkdir -p ~/.agda && \
    git clone --branch v2.3 --depth 1 https://github.com/agda/agda-stdlib.git ~/.agda/agda-stdlib && \
    echo "$HOME/.agda/agda-stdlib/standard-library.agda-lib" > ~/.agda/libraries && \
    echo "standard-library" > ~/.agda/defaults

# Build tools
RUN apt-get update && \
    apt-get install -y --no-install-recommends patchelf python3 python3-venv && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /build
COPY . .

# Build Agda → Haskell → libaletheia-ffi.so, then package dist tarball
RUN cabal run shake -- build && cabal run shake -- dist

# ── Stage 2: Runtime ─────────────────────────────────────────────────────────
FROM python:3.13-slim

# Only non-default system dependency
RUN apt-get update && \
    apt-get install -y --no-install-recommends libgmp10 && \
    rm -rf /var/lib/apt/lists/*

# Copy pre-built shared libraries and C header
COPY --from=builder /build/dist/aletheia /opt/aletheia

# Install Python package
COPY --from=builder /build/python /tmp/python
RUN pip install --no-cache-dir /tmp/python && rm -rf /tmp/python

# Tell aletheia where to find the .so (no _install_config.py needed)
ENV ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so

# Smoke test — verifies .so loads and Python package works
RUN python3 -c "from aletheia import AletheiaClient; print('OK')"

# No ENTRYPOINT — this is a library image, not a service
WORKDIR /work
