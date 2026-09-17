#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/reference/RUST_API.md.
# Claim: every Rust fence in the guide compiles against the crate, and each one
# that is a whole program also runs against the built kernel. No harness read
# this document: the C++ guide's fences are compiled by the doc-example tests
# and the Python guide's are run by pytest, and the Rust guide's were read by
# nobody. It took a parse result apart as a pair where it answers one value with
# two fields, and its DBC text was refused at its second line for want of the
# sections the verified parser requires; both had been so since the guide was
# written.
# A fence of bare statements is a program with its wrapper left out, so it is
# given one and compiled. It is not run: several call into the kernel, which
# answers RtsNotInitialized until a client has loaded the library, and that is
# the fence's context rather than a defect in it.
# Non-zero exit: a fence no longer compiles, or a whole program no longer runs.
# Exits 0 with a note when cargo or a built kernel is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
root=$PWD
guide=docs/reference/RUST_API.md
[ -f "$guide" ] || exit 2
command -v cargo > /dev/null || { echo "no cargo, claim untestable"; exit 0; }
[ -f build/libaletheia-ffi.so ] || { echo "no kernel built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/crate/src/bin"

if ! "$py" - "$guide" "$work/crate/src/bin" "$work/wholes.txt" > "$work/count.txt" 2>&1 <<'PY'
import re
import sys

guide, out, wholes_path = sys.argv[1], sys.argv[2], sys.argv[3]
blocks = re.findall(r"```rust\n(.*?)```", open(guide, encoding="utf-8").read(), re.S)
wholes = []
for i, body in enumerate(blocks):
    whole = "fn main" in body
    if not whole:
        head, rest = body.split("\n", 1)
        body = f"{head}\nfn main() -> Result<(), aletheia::Error> {{\n{rest}    Ok(())\n}}\n"
    else:
        wholes.append(f"program{i}")
    open(f"{out}/program{i}.rs", "w", encoding="utf-8").write(body)
open(wholes_path, "w", encoding="utf-8").write("".join(f"{w}\n" for w in wholes))
print(len(blocks))
PY
then
    echo "the guide could not be read:"
    head -3 "$work/count.txt" | sed 's/^/  /'
    exit 2
fi
count=$(cat "$work/count.txt")

if [ "$count" -eq 0 ]; then
    echo "the guide no longer prints a Rust fence"
    exit 1
fi

cat > "$work/crate/Cargo.toml" <<TOML
[package]
name = "rust-api-guide"
version = "0.0.0"
edition = "2021"

[dependencies]
aletheia = { path = "$root/rust" }
TOML

if ! (cd "$work/crate" && CARGO_NET_OFFLINE=true CARGO_TARGET_DIR="$work/target" \
    cargo build --quiet) > "$work/build.log" 2>&1; then
    echo "a fence in the guide does not compile:"
    head -12 "$work/build.log" | sed 's/^/  /'
    exit 1
fi

status=0
whole_count=0
while IFS= read -r name; do
    [ -n "$name" ] || continue
    whole_count=$((whole_count + 1))
    bin=$work/target/debug/$name
    [ -x "$bin" ] || { echo "$name was not built"; status=1; continue; }
    if ! ALETHEIA_LIB=$root/build/libaletheia-ffi.so LD_LIBRARY_PATH=$root/build \
        "$bin" > "$work/run.log" 2>&1; then
        echo "$name compiled but did not run:"
        head -4 "$work/run.log" | sed 's/^/  /'
        status=1
    fi
done < "$work/wholes.txt"

[ "$whole_count" -gt 0 ] || { echo "the guide no longer prints a whole program"; exit 1; }
[ "$status" -eq 0 ] || exit 1
echo "PASS: $count Rust fences compile, and the $whole_count that are whole programs run"
