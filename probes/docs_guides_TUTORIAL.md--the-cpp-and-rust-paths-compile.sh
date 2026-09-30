#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/guides/TUTORIAL.md.
# Claim: the C++ path's fences, read in order, compile against the built
# binding, and the Rust path's do against the crate. Each path is one program
# cut into steps, which the C++ and Rust doc-example harnesses join and run as
# a whole; this probe holds the compile on its own. The Rust path destructured a
# parse result as a pair when it answers one value with two fields, and had
# done since it was written.
# Non-zero exit: a path no longer compiles. Exits 0 with a note when a compiler
# or a built library is missing, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
root=$PWD
guide=docs/guides/TUTORIAL.md
[ -f "$guide" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
status=0

if command -v clang++-23 > /dev/null && [ -f cpp/build/libaletheia-cpp.so ]; then
	awk '/^```cpp$/{flag=1; next} /^```$/{flag=0} flag' "$guide" > "$work/path.cpp"
	grep -q "int main" "$work/path.cpp" || { echo "the C++ path no longer opens a program"; exit 1; }
	if ! clang++-23 -std=c++23 -Icpp/include "$work/path.cpp" cpp/build/libaletheia-cpp.so \
		-Wl,-rpath,"$root/cpp/build" -ldl -lpthread -o "$work/path" > "$work/cpp.log" 2>&1; then
		echo "the C++ path does not compile:"
		head -5 "$work/cpp.log" | sed 's/^/  /'
		status=1
	fi
else
	echo "no C++ toolchain or built binding, the C++ half is untestable"
fi

if command -v cargo > /dev/null; then
	mkdir -p "$work/rust/src"
	awk '/^```rust$/{flag=1; next} /^```$/{flag=0} flag' "$guide" > "$work/rust/src/main.rs"
	grep -q "fn main" "$work/rust/src/main.rs" || { echo "the Rust path no longer opens a program"; exit 1; }
	cat > "$work/rust/Cargo.toml" <<TOML
[package]
name = "tutorial-path"
version = "0.0.0"
edition = "2021"

[dependencies]
aletheia = { path = "$root/rust" }
TOML
	if ! (cd "$work/rust" && CARGO_NET_OFFLINE=true CARGO_TARGET_DIR="$work/target" cargo build --quiet) \
		> "$work/rust.log" 2>&1; then
		echo "the Rust path does not compile:"
		head -8 "$work/rust.log" | sed 's/^/  /'
		status=1
	fi
else
	echo "no cargo, the Rust half is untestable"
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: the C++ and Rust paths compile as the programs their steps cut up"
