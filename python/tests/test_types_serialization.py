# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Mutation-killing tests for aletheia.types.dump_json / FractionJSONEncoder.

``dump_json`` passes ``indent`` through, ``FractionJSONEncoder`` writes
non-ASCII text as UTF-8 whatever its caller asks, for cross-binding wire-byte
parity, and ``FractionJSONEncoder.default`` delegates unhandled types to the
base encoder.  These branches are not asserted by the happy-path callers, so
the indent / UTF-8 / delegated-type mutants survive without dedicated checks.
"""

from __future__ import annotations

import json

import pytest

from aletheia.types import FractionJSONEncoder, dump_json


def test_dump_json_indent_produces_pretty_output() -> None:
    """Pass ``indent`` through to json.dumps (a 2-space-indented body)."""
    result = dump_json({"a": 1, "b": 2}, indent=2)
    assert '\n  "' in result


def test_dump_json_compact_by_default() -> None:
    """Default to compact output (no indent) when ``indent`` is omitted."""
    result = dump_json({"a": 1, "b": 2})
    assert "\n" not in result


def test_dump_json_preserves_non_ascii() -> None:
    r"""Emit non-ASCII as raw UTF-8, not \uXXXX escapes."""
    result = dump_json({"name": "café"})
    assert "café" in result
    assert "\\u" not in result


def test_the_encoder_writes_utf8_whatever_its_caller_asks() -> None:
    r"""Keep UTF-8 when the caller asks for escapes, a lone string included."""
    assert (
        json.dumps({"name": "café"}, cls=FractionJSONEncoder, ensure_ascii=True)
        == '{"name": "café"}'
    )
    assert json.dumps("café", cls=FractionJSONEncoder, ensure_ascii=True) == '"café"'


def test_dump_json_rejects_unserializable_type() -> None:
    """Delegate an unhandled type to the base encoder, which names the type."""
    with pytest.raises(TypeError, match="set"):
        dump_json({1, 2, 3})
