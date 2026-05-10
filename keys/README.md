# Aletheia release-signing keys

`cosign.pub` is the **cosign keypair public key** that signs Aletheia
release artifacts (`dist/aletheia.tar.gz.sig`).  The matching private
key is **not committed**; it lives at `$ALETHEIA_COSIGN_KEY` on the
release host (canonical path `~/.config/aletheia/cosign.key`).

## Verifying a signed release

Install [cosign](https://github.com/sigstore/cosign) (single Go binary).
Per CICD-5.9: the tool the entire release-verification chain trusts must
itself be fetched verifiably — sigstore publishes a signed
`cosign_checksums.txt` alongside each release.

```bash
COSIGN_VERSION=2.4.1
COSIGN_SHA256=8b24b946dd5809c6bd93de08033bcf6bc0ed7d336b7785787c080f574b89249b
curl -fsSLo /tmp/cosign \
  "https://github.com/sigstore/cosign/releases/download/v${COSIGN_VERSION}/cosign-linux-amd64"
echo "${COSIGN_SHA256}  /tmp/cosign" | sha256sum -c -
install -m 755 /tmp/cosign ~/.local/bin/cosign
rm /tmp/cosign
```

Refresh both `COSIGN_VERSION` and `COSIGN_SHA256` on version bumps; the
canonical hash for each platform lives in upstream's
`cosign_checksums.txt` next to the release binaries.

Then verify against the committed public key:

```bash
cosign verify-blob \
  --key keys/cosign.pub \
  --signature dist/aletheia.tar.gz.sig \
  dist/aletheia.tar.gz
# => Verified OK
```

A non-zero exit means the tarball does **not** match the signature —
treat that as supply-chain compromise, not a bug.

## Rotating the keypair

1. Generate a fresh keypair on the release host:
   ```bash
   cd ~/.config/aletheia && cosign generate-key-pair
   ```
2. Replace `keys/cosign.pub` in this repo with the new public key.
3. Document the rotation in `CHANGELOG.md` under `### Security`.
4. Re-sign existing releases (or mark them as legacy and regenerate).

## Why a static keypair, not Sigstore keyless

Keyless OIDC signing requires GitHub Actions or a similar OIDC issuer
in the signing path.  Aletheia's CI architecture is local-first by
design (offline `tools/run_ci.py`; minimal `.github/workflows/`); a
release happens on the maintainer's host.  A maintainer-held cosign
keypair is the correct shape for that flow.

If the project ever shifts to a CI-driven release lane, swap to keyless
and retire `keys/cosign.pub` — the verification command becomes
`cosign verify-blob --certificate-identity ... --certificate-oidc-issuer ...`.

## Reference

- AGENTS.md § Universal Rules → Reproducible build verification
- AGENTS.md § CI/CD § cat 5 → "Signed artifacts (Sigstore / cosign)"
- docs/development/RELEASE.md § Signing
