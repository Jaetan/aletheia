"""Stable aliases for benchmark and harness helpers.

These re-export the engine-layer driver from :mod:`aletheia.checks_runner`
so benchmark scripts and external test harnesses can exercise the same
streaming pipeline the CLI runs without depending on the CLI's
presentation layer.  Stability guarantees match ``aletheia.checks_runner``
itself (implementation surface, not a long-term public API) — minor
releases may adjust signatures with documented migration notes.

Per ``feedback_test_interface_via_di.md``: when a harness needs to call a
``_`` -prefixed helper, the answer is interface-promotion through a stable
alias module, never ``# pylint: disable=protected-access``.

Note: ``MockBackend`` was promoted to a public class in R20 cluster P
(commit ``4dd3c05``) and now lives at :class:`aletheia.client.MockBackend`
with re-export at :class:`aletheia.MockBackend`; see
``docs/FEATURE_MATRIX.yaml`` row ``mock_backend`` (entry
``aletheia.MockBackend``).  This ``aletheia.testing`` module is the
benchmark / engine re-export surface and does NOT re-host
``MockBackend`` — users import the mock directly from ``aletheia`` (or
``aletheia.client``).  PY-S-17.2 closure (R21).
"""
from __future__ import annotations

from .checks_runner import CheckRunResult, Violation, run_checks

__all__ = ["CheckRunResult", "Violation", "run_checks"]
