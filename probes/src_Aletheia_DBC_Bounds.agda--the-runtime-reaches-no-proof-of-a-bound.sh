#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/DBC/Bounds.agda and src/Aletheia/DBC/Validator/Targets.agda.
# Claim: the proofs a bounded DBC and a name lookup carry are erased, so the
# compiled checker and the compiled lookups reach no proof module: the
# generated Bounds and Targets modules import neither the bounds' proofs
# (Aletheia.DBC.Bounds.Properties) nor the AVL membership proofs
# (Data.Tree.AVL.Sets.Membership.Properties) that the lookups' evidence comes
# from. Non-zero exit: a generated module imports one of them. Exits 0 with a
# note when the kernel is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
for module in Bounds Validator/Targets; do
	generated=build/MAlonzo/Code/Aletheia/DBC/$module.hs
	[ -f "$generated" ] || { echo "kernel not built, claim untestable"; exit 0; }
	if grep -nE '^import qualified MAlonzo\.Code\.(Aletheia\.DBC\.Bounds\.Properties|Data\.Tree\.AVL\.Sets\.Membership\.Properties)$' "$generated"; then
		echo "$generated imports a proof module"
		status=1
	fi
done
[ $status -eq 0 ] && echo "PASS: the generated checker and lookups import no proof module"
exit $status
