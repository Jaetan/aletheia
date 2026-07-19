# RELEASE.md

The release pipeline for Aletheia.  Cuts a tagged distribution tarball,
native packages (`.deb` + `.rpm`) over the same payload, and a runtime
container image on GHCR; records a CycloneDX SBOM; signs every artifact
with cosign (keyless in CI, key-based for local cuts); and produces the
verifiable artifact set consumers should rely on.

Cross-references:

- [`docs/development/DISTRIBUTION.md`](DISTRIBUTION.md) — what the
  tarball contains and how consumers integrate it.
- [`AGENTS.md` § Universal Rules → Reproducible build verification](../../AGENTS.md)
  — the rule this document operationalises.
- [`AGENTS.md` § CI/CD § cat 5](../../AGENTS.md) — artifact / release surface.

## Release paths

There are two ways to cut a release.  Both produce the same reproducible
tarball + SBOM signed with cosign; they differ only in **where signing happens
and what trust anchor verifies it**:

| Path | Trigger | Signing | Consumer verifies with |
|---|---|---|---|
| **CI (default)** | Push a `v*` tag | **Keyless** — Sigstore via the GitHub Actions OIDC identity; no key in CI | the workflow identity (`--certificate` + `--certificate-identity-regexp …`) |
| **Local (fallback)** | Run `shake dist` by hand | The maintainer's cosign key from the local keyring | `keys/cosign.pub` (`--key …`) |

The **CI path is the default.**  Pushing a `v*` tag runs
[`.github/workflows/release.yml`](../../.github/workflows/release.yml), which
builds via `shake dist`, keyless-signs the tarball, **self-verifies it against
its own OIDC identity**, **validates the bundle end-to-end from every binding**
(see [Release-path bundle validation](#release-path-bundle-validation) —
publish is gated on these checks), and publishes a **draft** GitHub Release for
the maintainer to review and flip public.  Keyless means no signing key or
passphrase ever lives in CI; the key stays in the local keyring, used only by
the fallback path.

Use the **local path** for releases cut off CI (a hotfix from the maintainer's
machine, or CI unavailable).

## Quick reference

### CI release (default) — push a tag

```bash
# After bumping versions + CHANGELOG (see the checklist), tag and push:
git tag -s vX.Y.Z -m "Aletheia vX.Y.Z"
git push origin vX.Y.Z
# release.yml builds, keyless-signs, self-verifies, and publishes a DRAFT
# Release.  Review it on GitHub, then flip it from draft to published.
#
# Dry-run the whole pipeline WITHOUT publishing (build + sign + self-verify):
#   gh workflow run release.yml     # or the Actions tab → Release → Run workflow
```

### Local release (fallback) — cut by hand

```bash
# Cut a signed release distribution (~2 min cold):
export ALETHEIA_COSIGN_KEY=$HOME/.config/aletheia/cosign.key
export COSIGN_PASSWORD=...                       # from your keyring / secret-manager
export ALETHEIA_COSIGN_TLOG=1                    # release: push entry to Sigstore Rekor
cabal run shake -- dist

# Outputs:
#   dist/aletheia.tar.gz            — the distribution tarball
#   dist/aletheia.tar.gz.sha256     — sha256 sidecar (sha256sum -c compatible)
#   dist/aletheia.tar.gz.sig        — cosign signature
#   dist/aletheia/MANIFEST.txt      — toolchain pin + per-file hashes (in-tarball)
#   dist/aletheia/aletheia-sbom.cdx.json — CycloneDX 1.5 SBOM (in-tarball)

# Verify (local path, key-based):
sha256sum -c dist/aletheia.tar.gz.sha256
cosign verify-blob \
  --key keys/cosign.pub \
  --signature dist/aletheia.tar.gz.sig \
  dist/aletheia.tar.gz
```

## Release-path bundle validation

Publish is gated on more than the signature.  After the keyless self-verify,
`release.yml` smoke-tests the bundled Python package (unpack → `source env.sh`
from a foreign cwd → load the `.so` → construct a real client) and then runs
the bundle validator ([`tools/bundle_validate.py`](../../tools/bundle_validate.py))
against the freshly built tarball with every compiled binding required
(`--require cpp,go,rust`).  The validator:

- unpacks the tarball and runs `install.sh` **and** `install.fish`, capturing
  their printed per-language recipes and checking the blocks are identical
  across shells;
- **executes the exact recipe lines the installers print** — never a re-typed
  copy — so an installer edit that breaks a recipe fails the gate instead of
  drifting past what users read;
- sources `env.sh` / `env.fish` from a foreign cwd and asserts they agree on
  an **absolute** `ALETHEIA_LIB`;
- builds and runs one small consumer program per compiled binding (C++, Go,
  Rust) through the verified kernel: env-constructor → parse a real `.dbc` →
  set an LTL property → stream a conforming and a violating frame → assert
  exactly one violation → end the stream.

A release can also rot *between* cuts (recipes, toolchains, staging, the
published assets themselves), so the same validation runs on a weekly schedule
([`.github/workflows/bundle-validation.yml`](../../.github/workflows/bundle-validation.yml)):
one job builds an unsigned `shake dist` from the default branch and validates
it — catching staging/recipe/binding rot while no release is in flight — and a
second job downloads the **latest published** GitHub Release, verifies it
exactly as a consumer would (sha256 sidecar + keyless cosign against the
release workflow identity — the commands under
[Verifying release artifacts](#verifying-release-artifacts-consumer-side)),
and validates that tarball: a true replay of the consumer's download path.
The scheduled lane also runs the validator's `--self-test`, which corrupts
copies of the bundle and asserts each corrupted copy FAILS validation — the
gate's teeth are themselves gated.

## Native packages (.deb / .rpm)

After the bundle validation, the release workflow builds native Linux
packages from the **same staged payload the tarball ships** —
`cabal run shake -- packages` maps `dist/aletheia` wholesale to
`/opt/aletheia` through the single `contents:` entry in
[`packaging/nfpm.yaml`](../../packaging/nfpm.yaml) (nfpm renders both
formats from that one manifest; nfpm itself is installed SHA-pinned, like
cosign).  The `packages` rule self-checks that the packed payload lists the
kernel `.so` under `/opt/aletheia/lib`, and the workflow then `dpkg -i`
install-smokes the `.deb` on the runner (env.sh → kernel load → clean
removal) and structurally checks the `.rpm` payload listing before anything
is published.

Artifacts per package: the `.deb`/`.rpm` itself, a `.sha256` sidecar, and a
keyless cosign `.sig` + `.crt` pair — verified in CI by the same
self-verify loop as the tarball, and by consumers with the same
`cosign verify-blob` recipe (see
[Verifying release artifacts](#verifying-release-artifacts-consumer-side)).

**Reproducibility scope (honest):** the packages are **hash-pinned per
release, not bit-reproducible**.  Empirically (nfpm 2.47.0, both formats):
without `SOURCE_DATE_EPOCH` two packagings of the same staged tree already
differ (nfpm stamps wall-clock into package metadata); with it — the
`packages` rule sets it to the commit epoch, matching the dist rule's
no-wall-clock stance — both formats are bit-identical across re-packagings
of the *same* staged tree, but nfpm does not clamp payload file mtimes, so
a re-staged tree yields different package bytes.  Verify the pinned hash
and signature, not a rebuild.  (The tarball's stronger guarantee is
unchanged — see
[Reproducible build verification](#reproducible-build-verification).)

Locally, `cabal run shake -- packages` produces the same artifact set
(unsigned-with-warning unless a signing mode is configured); it requires
`nfpm` on `PATH` — the pinned version + SHA-256 are recorded in
`packaging/nfpm.yaml`'s header comment.

## Container image on GHCR

On a `v*` tag push, after the draft Release is published, the workflow
pushes the runtime image (built from `Dockerfile.runtime` over the same
`dist/aletheia` payload) to GitHub Container Registry:

- `ghcr.io/jaetan/aletheia:X.Y.Z` (the release version) and `:latest`;
- the image **digest** is keyless-signed (`cosign sign`) under the same
  workflow OIDC identity as the blob artifacts — the digest, not a tag,
  because tags are movable and the digest is content-addressed.

The image build is itself a publish gate and runs *before* anything is
published: throwaway verify stages must build the bundled Rust crate and
C++ binding (clang-22), and build **and run** a Go consumer, against the
image's own `/opt/aletheia` — so an image whose bindings cannot consume its
kernel never ships.  The push happens last because it is the one
non-draft publish surface: GHCR has no draft state, a failed push is
idempotently retryable, and by that point every verification gate has
passed.

Consumers verify the image against the workflow identity:

```bash
cosign verify \
  --certificate-identity-regexp \
    '^https://github\.com/Jaetan/aletheia/\.github/workflows/release\.yml@refs/tags/v' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  ghcr.io/jaetan/aletheia:X.Y.Z
```

`cosign verify` resolves the tag to its digest and verifies the signature
over that digest; pin the digest in your own `FROM`/`COPY --from`
references for full immutability
([DISTRIBUTION.md § Docker](DISTRIBUTION.md#docker)).

**Maintainer note — one-time GHCR visibility flip:** the *first* push
creates the `aletheia` package on GHCR as **private**.  Consumers cannot
pull until you flip it once: GitHub → your profile → Packages →
`aletheia` → Package settings → Change visibility → Public.  Subsequent
release pushes keep the visibility; no further action needed.

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
across two clean builds without any reproducibility flags (sha256
`e095fb1c93bda5f390cffb401f88251ec75a6b33c1eaecf5f6da536817cd2265`).
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

### Keyless signing (CI — the default)

The CI release path signs **keyless** via Sigstore: cosign mints an ephemeral
key from the GitHub Actions ambient OIDC token (the `id-token: write` permission
in `release.yml`), obtains a short-lived Fulcio certificate bound to the
workflow identity, signs, records the entry in the Rekor transparency log, and
discards the key.  **No signing key or passphrase exists in CI.**

`shake dist` selects this mode when `ALETHEIA_COSIGN_KEYLESS=1` is set (the
workflow sets it).  It emits two sidecars — `aletheia.tar.gz.sig` and
`aletheia.tar.gz.crt` (the certificate) — and always uploads to Rekor (the
short-lived cert is only verifiable via its log entry).

Consumers verify against the **workflow identity**, not a public key:

```bash
cosign verify-blob \
  --certificate aletheia.tar.gz.crt \
  --signature aletheia.tar.gz.sig \
  --certificate-identity-regexp \
    '^https://github\.com/Jaetan/aletheia/\.github/workflows/release\.yml@refs/tags/v' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  aletheia.tar.gz
```

The exact command for any given artifact is embedded in its `MANIFEST.txt`
(the `shake dist` mode-aware verify block), so it always matches how that
tarball was actually signed.

### One-time key generation

The key-based path below is the **local fallback** (see "Release paths").



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
# 1. Fetch the tarball + sidecars from the GitHub Release.  Replace vX.Y.Z with
#    the tag (or use .../releases/latest/download/<file> for the newest).
BASE=https://github.com/Jaetan/aletheia/releases/download/vX.Y.Z
curl -fsSLO "$BASE/aletheia.tar.gz"
curl -fsSLO "$BASE/aletheia.tar.gz.sha256"
curl -fsSLO "$BASE/aletheia.tar.gz.sig"

# 2. Verify integrity
sha256sum -c aletheia.tar.gz.sha256

# 3. Verify provenance.  The tarball's MANIFEST.txt carries the exact command
#    matching how THIS artifact was signed — use the block for your release:
#
#    (a) CI release (default) — keyless (Sigstore), with a .crt sidecar:
curl -fsSLO "$BASE/aletheia.tar.gz.crt"
cosign verify-blob \
  --certificate aletheia.tar.gz.crt \
  --signature aletheia.tar.gz.sig \
  --certificate-identity-regexp \
    '^https://github\.com/Jaetan/aletheia/\.github/workflows/release\.yml@refs/tags/v' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  aletheia.tar.gz
#
#    (b) Locally-cut release — key-based, no .crt.  Verify against the project's
#        published key (keys/cosign.pub from the source tree):
cosign verify-blob \
  --key keys/cosign.pub \
  --signature aletheia.tar.gz.sig \
  aletheia.tar.gz

# 4. Inspect the SBOM
tar -xOzf aletheia.tar.gz aletheia/aletheia-sbom.cdx.json | jq .

# 5. Inspect the toolchain manifest
tar -xOzf aletheia.tar.gz aletheia/MANIFEST.txt
```

The native packages verify with the **same recipe** — substitute the
package file name for `aletheia.tar.gz` (each has its own `.sha256`,
`.sig`, and `.crt` sidecars on the Release). Worked example:
[DISTRIBUTION.md § Installing from a native package](DISTRIBUTION.md#installing-from-a-native-package-deb--rpm).
The container image verifies with `cosign verify` against the same
workflow identity (see
[Container image on GHCR](#container-image-on-ghcr)).

A failure in any of these is a stop-the-world event for the consumer.

## Release checklist

### Before cutting a release (both paths)

- [ ] Working tree clean (`git status --porcelain` empty).  A dirty
      tree shows up as `Git tree: dirty` in the MANIFEST and signals
      that the dist may not match any committed source.
- [ ] `tools/run_ci.py` passes end-to-end (the always-on gate sweep, ~22-30 min warm).
- [ ] `tools/check_reproducible_build.py` passes (~10 min cold).
- [ ] `CHANGELOG.md` has the release's notes accumulated under `## [Unreleased]`
      (Keep-a-Changelog shape — one `### Added/Changed/Fixed/…` header per
      category), and **rename `## [Unreleased]` to `## [X.Y.Z] — YYYY-MM-DD`** with a
      fresh empty `## [Unreleased]` above it — in THIS prepare-release commit, not
      after publishing. The version bump touches watched `.cabal` files, so
      `check_changelog` requires the CHANGELOG edit here (this is how v3.0.0 was cut).
- [ ] Version bumped to `X.Y.Z` in every package-metadata file:
      `python/pyproject.toml` (`version = "X.Y.Z"`),
      `haskell-shim/aletheia.cabal` (`version: X.Y.Z.0` — 4-part form; this is
      also the single source `libaletheia-ffi.so` and the SBOM read their
      version from, via `tools/sbom_generate.py`),
      `cpp/CMakeLists.txt` (`project(aletheia-cpp VERSION X.Y.Z ...)`),
      `rust/Cargo.toml` and `rust/excel/Cargo.toml` (`version = "X.Y.Z"`),
      then `cargo update -p aletheia` (in `rust/`) and
      `cargo update -p aletheia -p aletheia-excel` (in `rust/excel/`) to refresh
      the local-package entries in `rust/Cargo.lock` + `rust/excel/Cargo.lock`
      without disturbing pinned dependencies,
      and `shake.cabal` (`version: X.Y.Z.0` — the build orchestrator, bumped in
      lockstep at every prior release).
      (Go derives its version from the git tag — no in-file semver to bump.)
- [ ] **Redeploy the freshly-built kernel before pushing.** The version bump
      rebuilds `libaletheia-ffi.so` with the new version string, which stales any
      prior deployment — a `~/.local/lib/aletheia/` install and a `dist/` tree —
      so the pre-push `check-install-freshness` gate fails until they are
      refreshed. Run `cabal run shake -- install` **and** `cabal run shake -- dist`
      after the bump. (A fresh CI checkout has neither, so this is a local-only
      pre-push concern; it does not affect the GitHub checks.)

### CI release (default)

- [ ] Tag the release commit and push: `git tag -s vX.Y.Z -m "Aletheia vX.Y.Z"`
      then `git push origin vX.Y.Z`.
- [ ] `release.yml` goes green — it builds, keyless-signs, **self-verifies
      every signed artifact** (tarball + `.deb` + `.rpm`) against the workflow
      OIDC identity, **validates the bundle** across the bindings (see
      [Release-path bundle validation](#release-path-bundle-validation)),
      **install-smokes the `.deb`**, and **builds the runtime image** (whose
      verify stages exercise every compiled binding against it).  Publish is
      gated on all of these, so a green run means every artifact is
      verifiable *and* consumable.
- [ ] Review the resulting **draft** GitHub Release, then flip it from draft to
      published.  (Smoke-test beforehand with `gh workflow run release.yml` — the
      full build + sign + self-verify as a dry-run, no publish or push.)
- [ ] **First release with an image only:** flip the GHCR package visibility
      to Public (see the maintainer note under
      [Container image on GHCR](#container-image-on-ghcr)).

### Local release (fallback — cut off CI)

- [ ] Cosign keypair is the current key (`keys/cosign.pub` matches
      `~/.config/aletheia/cosign.key`).
- [ ] `ALETHEIA_COSIGN_TLOG=1` exported (release flow uses Rekor).
- [ ] `cabal run shake -- dist` produces the tarball + `.sha256` + `.sig`
      (plus MANIFEST + SBOM inside the tarball; no `.crt` — that is keyless-only).
- [ ] Manual verify (sha256, cosign `--key keys/cosign.pub`, SBOM look-OK).
- [ ] Create the GitHub Release and upload the tarball + sidecars:
      `gh release create vX.Y.Z dist/aletheia.tar.gz dist/aletheia.tar.gz.sha256 dist/aletheia.tar.gz.sig`.

### After publishing (both paths)

- [ ] The `CHANGELOG.md` `[Unreleased]` → `[X.Y.Z]` rename + fresh `[Unreleased]`
      are already done in the prepare-release commit above (forced there by
      `check_changelog`); no post-publish CHANGELOG edit is needed.

## Troubleshooting

### "Tarball NOT signed" warning at dist

`shake dist` skips signing (with a warning, so dev builds don't fail) when
cosign is absent, or when neither `ALETHEIA_COSIGN_KEYLESS=1` (CI keyless) nor
`ALETHEIA_COSIGN_KEY` (local key) is set.  A **release** build must be signed:

- **CI:** the `release.yml` job sets `ALETHEIA_COSIGN_KEYLESS=1` and installs
  cosign (SHA-pinned) on PATH — no action needed.
- **Local:** set `ALETHEIA_COSIGN_KEY` to your private key path (see "One-time
  key generation") and install cosign per "Installing cosign".

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
