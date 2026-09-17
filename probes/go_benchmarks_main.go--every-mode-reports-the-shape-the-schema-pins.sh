#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go.
# Claim: each of the three modes emits the payload benchmarks/SCHEMA.yaml pins,
# which is what makes the four bindings comparable: the lane names verbatim and
# in order, the row keys, the four scaling sweeps with their quick row counts
# and their five complexity labels. The claim is also an ordering one, because a
# shape check alone passes a report whose smallest and largest are swapped: a
# row's minimum is below its mean is below its maximum, and its percentiles
# rise. Throughput is run three times and latency over fifty operations so that
# a row's smallest and largest are two different numbers and the ordering has
# something to say. The schema is read here, never restated, so a lane renamed in one place
# fails rather than drifts.
# The binary is built, never found: one left over from before a wire change
# reports numbers that are void rather than stale.
# Non-zero exit: a mode's payload has left the schema. Exits 2 without Go or
# without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/benchmark" ./benchmarks) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
"$work/benchmark" throughput --frames 100 --runs 3 --warmup 0 --json > "$work/throughput.json" 2> /dev/null || exit 1
"$work/benchmark" latency --ops 50 --warmup 0 --json > "$work/latency.json" 2> /dev/null || exit 1
"$work/benchmark" scaling --quick --runs 1 --json > "$work/scaling.json" 2> /dev/null || exit 1

"$py" - "$work" <<'PY'
import json
import sys

import yaml

work = sys.argv[1]
schema = yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))["modes"]
bad = []


def rows(mode):
    return json.load(open(f"{work}/{mode}.json", encoding="utf-8"))["results"]


def check_keys(where, row, keys):
    if sorted(row) != sorted(keys):
        bad.append(f"{where}: keys {sorted(row)} != {sorted(keys)}")


def rising(where, row, fields, *, distinct=False):
    values = [row[f] for f in fields]
    if values != sorted(values):
        bad.append(f"{where}: {dict(zip(fields, values))} does not rise")
    # A spread of one sample orders trivially, so the extremes are asked to be
    # two numbers where the run size guarantees they are.
    if distinct and values[0] == values[-1]:
        bad.append(f"{where}: {fields[0]} and {fields[-1]} are both {values[0]}, so nothing was compared")


for mode in ("throughput", "latency"):
    spec = schema[mode]
    got = rows(mode)
    names = [r["name"] for r in got]
    if names != spec["lane_names"]:
        bad.append(f"{mode}: lanes {names} != {spec['lane_names']}")
    for row in got:
        check_keys(f"{mode} {row['name']}", row, spec["row_keys"])

for row in rows("throughput"):
    rising(f"throughput {row['name']}", row, ["fps_min", "fps_mean", "fps_max"], distinct=True)
for row in rows("latency"):
    rising(f"latency {row['name']}", row, ["min_us", "mean_us", "max_us"], distinct=True)
    rising(f"latency {row['name']}", row, ["p50_us", "p90_us", "p99_us", "p999_us"])

# The schema pins the rounding too: one decimal for a rate or a duration, three
# for a ratio. A value carrying more is a binding that rounds differently from
# the others, which shows up as a difference nobody measured.
rounding = yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))["experiment"]["rounding"]
places = {"fps": rounding["fps"], "fps_mean": rounding["fps"], "fps_stdev": rounding["fps"],
          "fps_min": rounding["fps"], "fps_max": rounding["fps"],
          "us_per_frame": rounding["us_per_frame"], "relative": rounding["relative"]}


def check_rounding(where, row):
    for field, value in row.items():
        want = places.get(field)
        if want is not None and round(value, want) != value:
            bad.append(f"{where}: {field} is {value}, not rounded to {want} places")


for mode in ("throughput", "latency"):
    for row in rows(mode):
        check_rounding(f"{mode} {row['name']}", row)

spec = schema["scaling"]
sweeps = rows("scaling")
if sorted(sweeps) != sorted(spec["sub_benchmarks"]):
    bad.append(f"scaling: sweeps {sorted(sweeps)} != {sorted(spec['sub_benchmarks'])}")
for name, rowset in sweeps.items():
    want = spec["quick_row_counts"][name]
    if len(rowset) != want:
        bad.append(f"scaling {name}: {len(rowset)} rows, schema says {want}")
    for row in rowset:
        check_keys(f"scaling {name}", row, spec["row_keys"][name])
        check_rounding(f"scaling {name}", row)
labels = [r["complexity"] for r in sweeps["property_complexity"]]
if labels != spec["complexity_labels"]:
    bad.append(f"scaling: labels {labels} != {spec['complexity_labels']}")

if bad:
    print("the Go benchmark has left benchmarks/SCHEMA.yaml:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print("PASS: the three modes report the shape the schema pins")
PY
