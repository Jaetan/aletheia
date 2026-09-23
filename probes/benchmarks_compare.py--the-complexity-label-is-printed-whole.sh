#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/compare.py.
# Claim: every complexity label benchmarks/SCHEMA.yaml pins is printed whole in
# the property-complexity table. The identifying column was twelve characters
# wide, so "Two predicates (AND)" printed as "Two predicat".
# Non-zero exit: a label the schema pins does not appear whole in the output.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
out=$("$py" benchmarks/compare.py benchmarks/results/*_scaling_baseline.json 2>&1) || { echo "compare.py failed"; exit 1; }
status=0
while IFS= read -r label; do
    grep -qF "$label" <<< "$out" || { echo "label not printed whole: $label"; status=1; }
done < <("$py" -c "import yaml; print('\n'.join(yaml.safe_load(open('benchmarks/SCHEMA.yaml'))['modes']['scaling']['complexity_labels']))")
exit $status
