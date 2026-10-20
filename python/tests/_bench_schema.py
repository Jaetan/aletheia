# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The cross-binding benchmark schema, ``benchmarks/SCHEMA.yaml``, in the fields the tests read."""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, Final, NewType, TypedDict, cast

import yaml

if TYPE_CHECKING:
    from aletheia.common_types import Prose

SCHEMA: Final = Path(__file__).resolve().parents[2] / "benchmarks" / "SCHEMA.yaml"

# A binding as result files name it (``cpp``), a benchmark mode (``throughput``),
# a lane of the throughput mode, a sweep of the scaling mode (``dbc_size``), a
# key of a sweep's rows (``seconds``), and a size a load sweep runs at.
BindingId = NewType("BindingId", str)
ModeName = NewType("ModeName", str)
LaneName = NewType("LaneName", str)
SweepName = NewType("SweepName", str)
RowKey = NewType("RowKey", str)
SweepSize = NewType("SweepSize", int)


class Envelope(TypedDict):
    """The bindings that write a result file and the modes one can be of."""

    languages: list[BindingId]
    benchmarks: list[ModeName]


class ThroughputMode(TypedDict):
    """The throughput lanes, in order."""

    lane_names: list[LaneName]


class ScalingMode(TypedDict):
    """Each sweep's row keys, in the schema's order, and the property-complexity labels."""

    row_keys: dict[SweepName, list[RowKey]]
    complexity_labels: list[Prose]


class Modes(TypedDict):
    """The modes whose fields the tests read."""

    throughput: ThroughputMode
    scaling: ScalingMode


class Sizes(TypedDict):
    """The sizes a load sweep runs at, in a full run and under ``--quick``."""

    full: list[SweepSize]
    quick: list[SweepSize]


class Experiment(TypedDict):
    """The sizes of the load sweeps."""

    dbc_sizes: Sizes
    literal_lengths: Sizes


class Schema(TypedDict):
    """The schema, in the fields the tests read."""

    envelope: Envelope
    modes: Modes
    experiment: Experiment


def schema() -> Schema:
    """Load the schema."""
    return cast("Schema", yaml.safe_load(SCHEMA.read_text(encoding="utf-8")))
