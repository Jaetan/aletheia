# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Reject-branch coverage for ``decode_wire_rational``'s dict path.

``decode_wire_rational`` accepts a bare int or a
``{"numerator": n, "denominator": d}`` object off the internal wire. Its dict
branch (``extract_rational_from_dict``) rejects a dict missing either field or
carrying a non-int component — reject branches that previously had no killing
test (only the non-positive-denominator case was exercised). These tests feed
the production decoder the shapes a malformed core response would carry. Parity
with Go #86's ``parseRational`` dict-missing-field tests.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from aletheia import ProtocolError
from aletheia.client._helpers.rational import decode_wire_rational


class TestDecodeWireRationalDictRejects:
    """Pin the malformed-rational-dict reject branches of the wire decoder."""

    @pytest.mark.parametrize(
        ("value", "match"),
        [
            pytest.param({"numerator": 5}, "denominator to be int", id="missing-denominator"),
            pytest.param({"denominator": 5}, "numerator to be int", id="missing-numerator"),
            pytest.param(
                {"numerator": "5", "denominator": 1}, "numerator to be int", id="non-int-numerator"
            ),
            pytest.param(
                {"numerator": 1, "denominator": "2"},
                "denominator to be int",
                id="non-int-denominator",
            ),
        ],
    )
    def test_malformed_rational_dict_rejected(self, value: dict[str, object], match: str) -> None:
        """A rational dict missing a field or with a non-int component is a wire violation."""
        with pytest.raises(ProtocolError, match=match):
            decode_wire_rational(value)

    def test_wellformed_rational_dict_accepted(self) -> None:
        """The positive companion: a complete int-component dict decodes exactly."""
        assert decode_wire_rational({"numerator": 3, "denominator": 4}) == Fraction(3, 4)
