"""Tests for formula enrichment: pretty-printer, signal collector, diagnostics."""

from aletheia import PropertyDiagnostic
from aletheia.client._enrichment import (
    build_diagnostic,
    collect_signals,
    format_enriched_reason,
    format_formula,
)
from aletheia.dsl import Signal


# ===========================================================================
# Formula pretty-printer
# ===========================================================================


class TestFormatFormula:
    """Test _format_formula on all formula and predicate types."""

    def test_always_less_than(self) -> None:
        """Verify always less than."""
        f = Signal("Speed").less_than(220).always().to_dict()
        assert format_formula(f) == "always(Speed < 220)"

    def test_never_pattern(self) -> None:
        """Verify never pattern."""
        f = Signal("Speed").greater_than(100).never().to_dict()
        assert format_formula(f) == "never Speed > 100"

    def test_eventually(self) -> None:
        """Verify eventually."""
        f = Signal("Mode").equals(1).eventually().to_dict()
        assert format_formula(f) == "eventually(Mode = 1)"

    def test_metric_always(self) -> None:
        """Verify metric always."""
        f = Signal("Speed").less_than(220).for_at_least(5000).to_dict()
        assert format_formula(f) == "always within 5s (Speed < 220)"

    def test_metric_eventually(self) -> None:
        """Verify metric eventually."""
        f = Signal("Mode").equals(1).within(2000).to_dict()
        assert format_formula(f) == "eventually within 2s (Mode = 1)"

    def test_next(self) -> None:
        """Verify next."""
        f = Signal("Speed").less_than(220).next().to_dict()
        assert format_formula(f) == "next(Speed < 220)"

    def test_and(self) -> None:
        """Verify and."""
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        assert format_formula(f) == "always(Speed < 220 and RPM > 500)"

    def test_or(self) -> None:
        """Verify or."""
        f = Signal("Speed").less_than(220).or_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        assert format_formula(f) == "always(Speed < 220 or RPM > 500)"

    def test_until(self) -> None:
        """Verify until."""
        speed = Signal("Speed").less_than(50).always()
        brake = Signal("Brake").equals(1).always()
        f = speed.until(brake).to_dict()
        assert format_formula(f) == "always(Speed < 50) until always(Brake = 1)"

    def test_release(self) -> None:
        """Verify release."""
        a = Signal("A").equals(1).always()
        b = Signal("B").equals(0).always()
        f = a.release(b).to_dict()
        assert format_formula(f) == "always(A = 1) release always(B = 0)"

    def test_not(self) -> None:
        # not(atomic).always() triggers Never pattern detection
        """Verify not."""
        f = Signal("Speed").less_than(220).not_().always().to_dict()
        assert format_formula(f) == "never Speed < 220"

    def test_not_non_atomic(self) -> None:
        # not(non-atomic) doesn't trigger Never pattern
        """Verify not non atomic."""
        inner = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        )
        f = inner.not_().always().to_dict()
        assert format_formula(f) == "always(not(Speed < 220 and RPM > 500))"


class TestFormatPredicate:
    """Test format_formula output for each predicate kind (wrapped in always)."""

    def test_equals_predicate(self) -> None:
        """Verify equals predicate."""
        f = Signal("S").equals(42).always().to_dict()
        assert "S = 42" in format_formula(f)

    def test_less_than_predicate(self) -> None:
        """Verify less than predicate."""
        f = Signal("S").less_than(10).always().to_dict()
        assert "S < 10" in format_formula(f)

    def test_greater_than_predicate(self) -> None:
        """Verify greater than predicate."""
        f = Signal("S").greater_than(5).always().to_dict()
        assert "S > 5" in format_formula(f)

    def test_less_than_or_equal_predicate(self) -> None:
        """Verify less than or equal predicate."""
        f = Signal("S").less_than_or_equal(100).always().to_dict()
        assert "S <= 100" in format_formula(f)

    def test_greater_than_or_equal_predicate(self) -> None:
        """Verify greater than or equal predicate."""
        f = Signal("S").greater_than_or_equal(0).always().to_dict()
        assert "S >= 0" in format_formula(f)

    def test_between_predicate(self) -> None:
        """Verify between predicate."""
        f = Signal("S").between(10, 14.5).always().to_dict()
        result = format_formula(f)
        assert "10 <= S <= 14.5" in result

    def test_changed_by_predicate(self) -> None:
        """Verify changed by predicate."""
        f = Signal("S").changed_by(5).always().to_dict()
        result = format_formula(f)
        assert "\u0394S >= 5" in result

    def test_changed_by_negative_predicate(self) -> None:
        """Verify changed by negative predicate."""
        f = Signal("S").changed_by(-5).always().to_dict()
        result = format_formula(f)
        assert "\u0394S <= -5" in result

    def test_stable_within_predicate(self) -> None:
        """Verify stable within predicate."""
        f = Signal("S").stable_within(2.0).always().to_dict()
        result = format_formula(f)
        assert "|\u0394S| <= 2" in result

    def test_metric_until(self) -> None:
        """Verify metric until."""
        speed = Signal("Speed").less_than(50).always()
        brake = Signal("Brake").equals(1).always()
        f = speed.metric_until(1000, brake).to_dict()
        result = format_formula(f)
        assert "until within 1s" in result

    def test_metric_release(self) -> None:
        """Verify metric release."""
        a = Signal("A").equals(1).always()
        b = Signal("B").equals(0).always()
        f = a.metric_release(500, b).to_dict()
        result = format_formula(f)
        assert "release within 500ms" in result


# ===========================================================================
# Signal collection
# ===========================================================================


class TestCollectSignals:
    """Test _collect_signals."""

    def test_multi_signal(self) -> None:
        """Verify multi signal."""
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        signals = collect_signals(f)
        assert signals == ["Speed", "RPM"]

    def test_dedup(self) -> None:
        """Verify dedup."""
        f = Signal("Speed").less_than(220).and_(
            Signal("Speed").greater_than(0)
        ).always().to_dict()
        signals = collect_signals(f)
        assert signals == ["Speed"]

    def test_nested(self) -> None:
        """Verify nested."""
        f = Signal("Speed").less_than(220).always().to_dict()
        signals = collect_signals(f)
        assert signals == ["Speed"]

    def test_never_pattern(self) -> None:
        """Verify never pattern."""
        f = Signal("Speed").greater_than(100).never().to_dict()
        signals = collect_signals(f)
        assert signals == ["Speed"]


# ===========================================================================
# Build diagnostic
# ===========================================================================


class TestBuildDiagnostic:
    """Test _build_diagnostic always succeeds."""

    def test_simple(self) -> None:
        """Verify simple."""
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = build_diagnostic(f)
        assert isinstance(diag, PropertyDiagnostic)
        assert diag.signals == ("Speed",)
        assert "Speed" in diag.formula_desc
        assert "220" in diag.formula_desc

    def test_multi_signal(self) -> None:
        """Verify multi signal."""
        f = Signal("Speed").less_than(220).and_(
            Signal("RPM").greater_than(500)
        ).always().to_dict()
        diag = build_diagnostic(f)
        assert diag.signals == ("Speed", "RPM")
        assert "Speed" in diag.formula_desc
        assert "RPM" in diag.formula_desc


# ===========================================================================
# Enriched reason formatting
# ===========================================================================


class TestFormatEnrichedReason:
    """Test _format_enriched_reason."""

    def test_with_values(self) -> None:
        """Verify with values."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "formula:" in reason
        assert "always(Speed < 220)" in reason

    def test_multi_signal(self) -> None:
        """Verify multi signal."""
        diag = PropertyDiagnostic(
            signals=("Speed", "RPM"),
            formula_desc="always(Speed < 220 and RPM > 500)",
        )
        values: dict[str, float | None] = {"Speed": 245.0, "RPM": 3000.0}
        reason = format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "RPM = 3000" in reason
        assert "formula:" in reason

    def test_no_values(self) -> None:
        """Verify no values."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        reason = format_enriched_reason(diag, {})
        assert reason == "violated: always(Speed < 220)"

    def test_core_reason_appended(self) -> None:
        """Verify core reason appended."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = format_enriched_reason(diag, values, core_reason="liveness timeout")
        assert reason.endswith("[core: liveness timeout]")
        assert "Speed = 245" in reason

    def test_core_reason_empty_is_omitted(self) -> None:
        """Verify core reason empty is omitted."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = format_enriched_reason(diag, values, core_reason="")
        assert "[core:" not in reason

    def test_core_reason_with_no_values(self) -> None:
        """Verify core reason with no values."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        reason = format_enriched_reason(diag, {}, core_reason="never observed")
        assert "violated:" in reason
        assert reason.endswith("[core: never observed]")

    def test_dsl_roundtrip(self) -> None:
        """DSL formula -> diagnostic -> enriched reason."""
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = build_diagnostic(f)
        values: dict[str, float | None] = {"Speed": 245.0}
        reason = format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "always(Speed < 220)" in reason
