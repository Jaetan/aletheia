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
# and a lane of the throughput mode.
BindingId = NewType("BindingId", str)
ModeName = NewType("ModeName", str)
LaneName = NewType("LaneName", str)


class Envelope(TypedDict):
    """The bindings that write a result file and the modes one can be of."""

    languages: list[BindingId]
    benchmarks: list[ModeName]


class ThroughputMode(TypedDict):
    """The throughput lanes, in order."""

    lane_names: list[LaneName]


class ScalingMode(TypedDict):
    """The labels of the property-complexity sweep."""

    complexity_labels: list[Prose]


class Modes(TypedDict):
    """The modes whose fields the tests read."""

    throughput: ThroughputMode
    scaling: ScalingMode


class Schema(TypedDict):
    """The schema, in the fields the tests read."""

    envelope: Envelope
    modes: Modes


def schema() -> Schema:
    """Load the schema."""
    return cast("Schema", yaml.safe_load(SCHEMA.read_text(encoding="utf-8")))
