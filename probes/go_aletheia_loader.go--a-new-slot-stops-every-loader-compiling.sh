#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/loader.go against go/aletheia/yaml.go and go/excel/excel.go.
# Claim: a condition that reads a value slot no loader can answer cannot be
# added quietly. The slots are an interface each loader implements, so a slot
# added to it stops every loader compiling until that loader answers it, which
# is the property a switch over condition words cannot give: a word the shared
# table accepts and a loader's switch does not handle used to fall through and
# build a check with the zero rational in every slot.
# The check is run on a copy of the tree, a method being added to each of the
# two interfaces in turn and both modules built; the tree itself is untouched.
# Non-zero exit: a loader still compiles against a slot it does not answer.
# Exits 2 without Go.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
cp -r go "$work/go" || exit 2

# The tree as copied must build, or the check below proves nothing.
(cd "$work/go" && CGO_ENABLED=0 go build ./... > /dev/null 2>&1) || {
    echo "the copied tree does not build before any slot is added"
    exit 1
}
(cd "$work/go/excel" && CGO_ENABLED=0 go build ./... > /dev/null 2>&1) || {
    echo "the copied Excel module does not build before any slot is added"
    exit 1
}

bad=0
for iface in SimpleValues ThenValues; do
    cp go/aletheia/loader.go "$work/loader.orig"
    python3 - "$work/go/aletheia/loader.go" "$iface" <<'PY'
import sys

path, iface = sys.argv[1], sys.argv[2]
text = open(path, encoding="utf-8").read()
anchor = f"type {iface} interface {{\n"
assert text.count(anchor) == 1, f"{iface} is not declared once"
text = text.replace(anchor, anchor + "\tDurationSlot() (int64, error)\n")
open(path, "w", encoding="utf-8").write(text)
PY
    if (cd "$work/go" && CGO_ENABLED=0 go build ./aletheia/ > /dev/null 2>&1); then
        echo "the binding's own loader still compiles with a slot it does not answer ($iface)"
        bad=1
    fi
    if (cd "$work/go/excel" && CGO_ENABLED=0 go build ./... > /dev/null 2>&1); then
        echo "the Excel loader still compiles with a slot it does not answer ($iface)"
        bad=1
    fi
    cp "$work/loader.orig" "$work/go/aletheia/loader.go"
done

[ "$bad" -eq 0 ] || exit 1
echo "PASS: a slot added to either interface stops both loaders compiling"
