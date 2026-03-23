"""Tests for formula enrichment: pretty-printer, signal collector, diagnostics."""

from __future__ import annotations

from aletheia.client._client import (
    _build_diagnostic,
    _collect_signals,
    _format_enriched_reason,
    _format_formula,
)
from aletheia.client._types import PropertyDiagnostic
from aletheia.dsl import Signal, Property


# ===========================================================================
# Formula pretty-printer
# ===========================================================================


class TestFormatFormula:
    """Test _format_formula on all formula and predicate types."""

    def test_always_less_than(self) -> None:
        f = Signal("Speed").less_than(220).always().to_dict()
        assert _format_formula(f) == "always(Speed < 220)"

    def test_never_pattern(self) -> None:
        f = Signal("Speed").greater_than(100).never().to_dict()
        assert _format_formula(f) == "never Speed > 100"

    def test_eventually(self) -> None:
        f = Signal("Mode").equals(1).eventually().to_dict()
        assert _format_formula(f) == "eventually(Mode = 1)"

    def test_metric_always(self) -> None:
        f = Signal("Speed").less_than(220).for_at_least(5000).to_dict()
        assert _format_formula(f) == "always within 5s (Speed < 220)"

    def test_metric_eventually(self) -> None:
        f = Signal("Mode").equals(1).within(2000).to_dict()
        assert _format_formula(f) == "eventually within 2s (Mode = 1)"

    def test_next(self) -> None:
        f = Signal("Speed").less_than(220).next().to_dict()
        assert _format_formula(f) == "next(Speed < 220)"

    def test_and(self) -> None:
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        assert _format_formula(f) == "always(Speed < 220 and RPM > 500)"

    def test_or(self) -> None:
        f = Signal("Speed").less_than(220).or_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        assert _format_formula(f) == "always(Speed < 220 or RPM > 500)"

    def test_until(self) -> None:
        speed = Signal("Speed").less_than(50).always()
        brake = Signal("Brake").equals(1).always()
        f = speed.until(brake).to_dict()
        assert _format_formula(f) == "always(Speed < 50) until always(Brake = 1)"

    def test_release(self) -> None:
        a = Signal("A").equals(1).always()
        b = Signal("B").equals(0).always()
        f = a.release(b).to_dict()
        assert _format_formula(f) == "always(A = 1) release always(B = 0)"

    def test_not(self) -> None:
        # not(atomic).always() triggers Never pattern detection
        f = Signal("Speed").less_than(220).not_().always().to_dict()
        assert _format_formula(f) == "never Speed < 220"

    def test_not_non_atomic(self) -> None:
        # not(non-atomic) doesn't trigger Never pattern
        inner = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        )
        f = inner.not_().always().to_dict()
        assert _format_formula(f) == "always(not(Speed < 220 and RPM > 500))"

    # Predicate types (wrapped in always for to_dict)
    def test_equals_predicate(self) -> None:
        f = Signal("S").equals(42).always().to_dict()
        assert "S = 42" in _format_formula(f)

    def test_less_than_predicate(self) -> None:
        f = Signal("S").less_than(10).always().to_dict()
        assert "S < 10" in _format_formula(f)

    def test_greater_than_predicate(self) -> None:
        f = Signal("S").greater_than(5).always().to_dict()
        assert "S > 5" in _format_formula(f)

    def test_less_than_or_equal_predicate(self) -> None:
        f = Signal("S").less_than_or_equal(100).always().to_dict()
        assert "S <= 100" in _format_formula(f)

    def test_greater_than_or_equal_predicate(self) -> None:
        f = Signal("S").greater_than_or_equal(0).always().to_dict()
        assert "S >= 0" in _format_formula(f)

    def test_between_predicate(self) -> None:
        f = Signal("S").between(10, 14.5).always().to_dict()
        result = _format_formula(f)
        assert "10 <= S <= 14.5" in result

    def test_changed_by_predicate(self) -> None:
        f = Signal("S").changed_by(5).always().to_dict()
        result = _format_formula(f)
        assert "S" in result
        assert "> 5" in result

    def test_metric_until(self) -> None:
        speed = Signal("Speed").less_than(50).always()
        brake = Signal("Brake").equals(1).always()
        f = speed.metric_until(1000, brake).to_dict()
        result = _format_formula(f)
        assert "until within 1s" in result

    def test_metric_release(self) -> None:
        a = Signal("A").equals(1).always()
        b = Signal("B").equals(0).always()
        f = a.metric_release(500, b).to_dict()
        result = _format_formula(f)
        assert "release within 500ms" in result


# ===========================================================================
# Signal collection
# ===========================================================================


class TestCollectSignals:
    """Test _collect_signals."""

    def test_multi_signal(self) -> None:
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        signals = _collect_signals(f)
        assert signals == ["Speed", "RPM"]

    def test_dedup(self) -> None:
        f = Signal("Speed").less_than(220).and_(
            Signal("Speed").greater_than(0)
        ).always().to_dict()
        signals = _collect_signals(f)
        assert signals == ["Speed"]

    def test_nested(self) -> None:
        f = Signal("Speed").less_than(220).always().to_dict()
        signals = _collect_signals(f)
        assert signals == ["Speed"]

    def test_never_pattern(self) -> None:
        f = Signal("Speed").greater_than(100).never().to_dict()
        signals = _collect_signals(f)
        assert signals == ["Speed"]


# ===========================================================================
# Build diagnostic
# ===========================================================================


class TestBuildDiagnostic:
    """Test _build_diagnostic always succeeds."""

    def test_simple(self) -> None:
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = _build_diagnostic(f)
        assert isinstance(diag, PropertyDiagnostic)
        assert diag.signals == ["Speed"]
        assert "Speed" in diag.formula_desc
        assert "220" in diag.formula_desc

    def test_multi_signal(self) -> None:
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        diag = _build_diagnostic(f)
        assert diag.signals == ["Speed", "RPM"]
        assert "Speed" in diag.formula_desc
        assert "RPM" in diag.formula_desc


# ===========================================================================
# Enriched reason formatting
# ===========================================================================


class TestFormatEnrichedReason:
    """Test _format_enriched_reason."""

    def test_with_values(self) -> None:
        diag = PropertyDiagnostic(
            signals=["Speed"],
            formula_desc="always(Speed < 220)",
        )
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = _format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "formula:" in reason
        assert "always(Speed < 220)" in reason

    def test_multi_signal(self) -> None:
        diag = PropertyDiagnostic(
            signals=["Speed", "RPM"],
            formula_desc="always(Speed < 220 and RPM > 500)",
        )
        values: dict[str, float | None] = {"Speed": 245.0, "RPM": 3000.0}
        reason = _format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "RPM = 3000" in reason
        assert "formula:" in reason

    def test_no_values(self) -> None:
        diag = PropertyDiagnostic(
            signals=["Speed"],
            formula_desc="always(Speed < 220)",
        )
        reason = _format_enriched_reason(diag, {})
        assert reason == "violated: always(Speed < 220)"

    def test_dsl_roundtrip(self) -> None:
        """DSL formula -> diagnostic -> enriched reason."""
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = _build_diagnostic(f)
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = _format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "always(Speed < 220)" in reason
