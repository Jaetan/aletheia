# RELEASE.md

The release pipeline for Aletheia.  Cuts a tagged distribution tarball,
records a CycloneDX SBOM, signs the tarball with cosign, and produces
the verifiable artifact set consumers should rely on.

Closes R18 cluster 3 (UR-3 reproducible-build hash + SBOM + signing) +
CICD cat 5 sub-items.  Cross-references:

- [`docs/development/DISTRIBUTION.md`](DISTRIBUTION.md) — what the
  tarball contains and how consumers integrate it.
- [`AGENTS.md` § Universal Rules → Reproducible build verification](../../AGENTS.md)
  — the rule this document operationalises.
- [`AGENTS.md` § CI/CD § cat 5](../../AGENTS.md) — artifact / release surface.

## Quick reference

```bash
# Cut a signed release distribution (~2 min cold):
export ALETHEIA_COSIGN_KEY=$HOME/.config/aletheia/cosign.key
export COSIGN_PASSWORD=...                       # the passphrase for the key
export ALETHEIA_COSIGN_TLOG=1                    # release: push entry to Sigstore Rekor
cabal run shake -- dist

# Outputs:
#   dist/aletheia.tar.gz            — the distribution tarball
#   dist/aletheia.tar.gz.sha256     — sha256 sidecar (sha256sum -c compatible)
#   dist/aletheia.tar.gz.sig        — cosign signature
#   dist/aletheia/MANIFEST.txt      — toolchain pin + per-file hashes (in-tarball)
#   dist/aletheia/aletheia-sbom.cdx.json — CycloneDX 1.5 SBOM (in-tarball)

# Verify (consumer side):
sha256sum -c dist/aletheia.tar.gz.sha256
cosign verify-blob \
  --key keys/cosign.pub \
  --signature dist/aletheia.tar.gz.sig \
  dist/aletheia.tar.gz
```

## Reproducible build verification

`cabal run shake -- build` produces the same `libaletheia-ffi.so`
sha256 across two clean builds on the same toolchain pin (GHC, cabal,
Agda, agda-stdlib).  Drift indicates build-time non-determinism — see
the rule in AGENTS.md § Universal Rules.

The gate is **not in the default `tools/run_ci.py` battery** because
it costs two cold builds (~10 min wall-clock).  Run it on demand:

```bash
tools/check_reproducible_build.py

# Or with --keep-artifacts to retain the temp dir for forensic diff:
tools/check_reproducible_build.py --keep-artifacts
```

Empirically verified: same-host `libaletheia-ffi.so` is bit-identical
across two clean builds without any reproducibility flags (R18 cluster
3, sha256 `e095fb1c93bda5f390cffb401f88251ec75a6b33c1eaecf5f6da536817cd2265`).
The flags below harden against regressions.

### Hardening flags wired into the build

- **GHC**: `--ghc-options=-optc-ffile-prefix-map=$REPO_ROOT=.` (passed
  via `Shakefile.hs`'s cabal-build invocation; takes effect when GHC's
  bundled C compiler embeds debug info).  GHC ≥ 9.10's
  `-fdebug-prefix-map` would be the direct flag; we pin GHC 9.6.7
  which lacks it, so we go through the C-compiler pass-through.
- **C++ binding**: `-ffile-prefix-map=${CMAKE_SOURCE_DIR}=.` on
  `aletheia-cpp` library target (covers `__FILE__` macros + DWARF).
- **Tarball**: `tar --sort=name --mtime=@<commit-epoch> --owner=0
  --group=0 --numeric-owner --use-compress-program='gzip -n'` strips
  every wall-clock and per-user field; the commit time is sourced
  from `git log -1 --format=%ct HEAD`.
- **SBOM**: timestamp + UUID5 derived from git commit time and version
  (no `uuid.uuid4()` entropy, no `datetime.now()`).

## Signing

### One-time key generation

The cosign keypair lives outside the repo.  Canonical paths:

```bash
mkdir -p ~/.config/aletheia
cd ~/.config/aletheia
COSIGN_PASSWORD="<choose a passphrase>" cosign generate-key-pair

cp cosign.pub /path/to/aletheia/keys/cosign.pub   # commit to repo
# cosign.key stays at ~/.config/aletheia/cosign.key, never committed
```

Set environment variables persistently (e.g., `~/.config/fish/conf.d/aletheia.fish`):

```fish
set -gx ALETHEIA_COSIGN_KEY $HOME/.config/aletheia/cosign.key
# Set COSIGN_PASSWORD via your secret-manager of choice — never hard-code.
```

### Per-release sign+verify

`cabal run shake -- dist` calls `cosign sign-blob` automatically when
`$ALETHEIA_COSIGN_KEY` is set and `cosign` is on `PATH`.  The default
behaviour skips Rekor tlog upload (`--tlog-upload=false`) so dev
iteration doesn't push every artifact hash to a public log.  For an
actual release, opt back in:

```bash
ALETHEIA_COSIGN_TLOG=1 cabal run shake -- dist
```

Verify:

```bash
# Local dev (signed without tlog → consumer must skip tlog check):
cosign verify-blob \
  --insecure-ignore-tlog \
  --key keys/cosign.pub \
  --signature dist/aletheia.tar.gz.sig \
  dist/aletheia.tar.gz

# Release (signed with tlog upload):
cosign verify-blob \
  --key keys/cosign.pub \
  --signature dist/aletheia.tar.gz.sig \
  dist/aletheia.tar.gz
```

A non-zero exit means the tarball does **not** match the signature —
treat that as supply-chain compromise, not a tooling bug.

### Installing cosign

Single Go binary; no system package needed.  Per CICD-5.9, the tool the
release-verification chain trusts must itself be fetched verifiably —
sigstore publishes a signed `cosign_checksums.txt` alongside each release:

```bash
COSIGN_VERSION=2.4.1
COSIGN_SHA256=8b24b946dd5809c6bd93de08033bcf6bc0ed7d336b7785787c080f574b89249b
curl -fsSLo /tmp/cosign \
  "https://github.com/sigstore/cosign/releases/download/v${COSIGN_VERSION}/cosign-linux-amd64"
echo "${COSIGN_SHA256}  /tmp/cosign" | sha256sum -c -
install -m 755 /tmp/cosign ~/.local/bin/cosign
rm /tmp/cosign
```

Pin matches `keys/README.md`.  Refresh both files together when bumping
cosign — the canonical hash for each platform lives in upstream's
`cosign_checksums.txt` next to the release binaries.

### Key rotation

1. Generate a fresh keypair on the release host (see "One-time key
   generation" above).
2. Replace `keys/cosign.pub` in the repo with the new public key.
3. Document the rotation in `CHANGELOG.md` under `### Security`.
4. Re-sign existing releases or mark them as legacy and regenerate.

## SBOM

`tools/sbom_generate.py` emits CycloneDX 1.5 JSON describing:

- The toolchain pin (GHC, cabal, Agda, agda-stdlib versions).
- The main artifact (`libaletheia-ffi.so` + sha256).
- Each GHC runtime `libHS*.so` shipped under `dist/aletheia/lib/` with
  per-file sha256.

The SBOM is the audit trail for the LGPL-contingency
`--bignum=native` rebuild deliverable (`PROJECT_STATUS.md` § Phase 6
candidate goals, item 3) — before/after `.so` hashes documented in the
SBOM make the rebuild verification falsifiable.

Output path inside the tarball: `aletheia/aletheia-sbom.cdx.json`.

## Verifying release artifacts (consumer side)

```bash
# 1. Fetch tarball + sidecar files
curl -fsSLO https://aletheia-releases.example/aletheia.tar.gz{,.sha256,.sig}

# 2. Verify integrity
sha256sum -c aletheia.tar.gz.sha256

# 3. Verify provenance (release builds include Rekor tlog entry)
cosign verify-blob \
  --key https://aletheia-releases.example/cosign.pub \
  --signature aletheia.tar.gz.sig \
  aletheia.tar.gz

# 4. Inspect the SBOM
tar -xOzf aletheia.tar.gz aletheia/aletheia-sbom.cdx.json | jq .

# 5. Inspect the toolchain manifest
tar -xOzf aletheia.tar.gz aletheia/MANIFEST.txt
```

A failure in any of these is a stop-the-world event for the consumer.

## Release checklist

Before tagging a release:

- [ ] Working tree clean (`git status --porcelain` empty).  A dirty
      tree shows up as `Git tree: dirty` in the MANIFEST and signals
      that the dist may not match any committed source.
- [ ] `tools/run_ci.py` passes end-to-end (33 always-on steps, ~22-30 min warm).
- [ ] `tools/check_reproducible_build.py` passes (~10 min cold).
- [ ] `CHANGELOG.md` has an entry under `## [X.Y.Z] — Unreleased`
      describing the release.
- [ ] Version bumped to `X.Y.Z` in every package-metadata file:
      `python/pyproject.toml` (`version = "X.Y.Z"`),
      `haskell-shim/aletheia.cabal` (`version: X.Y.Z.0` — note the 4-part form),
      `cpp/CMakeLists.txt` (`project(aletheia-cpp VERSION X.Y.Z ...)`).
      (Go derives its version from the git tag — no in-file semver to bump.)
- [ ] Cosign keypair is the current key (`keys/cosign.pub` matches
      `~/.config/aletheia/cosign.key`).
- [ ] `ALETHEIA_COSIGN_TLOG=1` exported (release flow uses Rekor).
- [ ] `cabal run shake -- dist` produces all four artifact files.
- [ ] Manual verify of all three checks (sha256, cosign, SBOM look-OK).
- [ ] Tag the release commit + push tarball + signature + sha256 +
      `keys/cosign.pub` to the release host.
- [ ] Edit `CHANGELOG.md` to flip `## [X.Y.Z] — Unreleased` to
      `## [X.Y.Z] — YYYY-MM-DD`.

## Troubleshooting

### "cosign not found" warning at dist

Install cosign per "Installing cosign" above.  Skip-with-warning is
deliberate so that dev builds don't fail when cosign is absent — but
a release build without cosign produces no signature.

### "ALETHEIA_COSIGN_KEY env var not set"

Set the env var to your private key path.  See "One-time key
generation".

### Verify warns about `--insecure-ignore-tlog`

For dev signing (`--tlog-upload=false` default), tlog verification is
not possible — pass `--insecure-ignore-tlog` to verify.  The warning
text is correct: skipping tlog removes one layer of evidence.  Use
`ALETHEIA_COSIGN_TLOG=1` at sign time when you want full provenance.

### Tarball hash differs across two clean dist runs

Run `tools/check_reproducible_build.py` first to bisect: if the
underlying `.so` is reproducible, then the drift is in dist packaging
(SBOM, MANIFEST, tar/gzip).  Hardening flags listed under
"Reproducible build verification" address every known dist-side
source — `cmp -l` the two tarballs to find new drift surfaces.
