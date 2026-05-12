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

Note: ``docs/FEATURE_MATRIX.yaml`` row ``mock_backend_for_testing`` mentions
``aletheia.testing`` as the hypothetical home for a Python ``MockBackend``
class.  This module shares that namespace but does not host the mock backend
— that promotion remains the "separate design decision" the matrix row
references.  Adding a ``MockBackend`` here later is allowed; the current
contents (engine-layer re-exports) are independent of that decision.
"""
from __future__ import annotations

from .checks_runner import CheckRunResult, Violation, run_checks

__all__ = ["CheckRunResult", "Violation", "run_checks"]
