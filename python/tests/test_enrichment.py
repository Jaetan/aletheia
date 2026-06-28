# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for formula enrichment: pretty-printer, signal collector, diagnostics."""

from fractions import Fraction

import pytest

from aletheia import FFIError, PropertyDiagnostic
from aletheia.client._enrichment import (
    build_diagnostic,
    collect_signals,
    format_enriched_reason,
    format_formula,
)
from aletheia.dsl import Signal

# Every test here renders rational thresholds via the kernel (format_formula /
# build_diagnostic), which since point 2 requires a live GHC RTS — the renderer no
# longer self-initialises. Request the lazy ``rts_up`` fixture (conftest.py)
# module-wide so the RTS comes up when these tests RUN, not at collection time.
pytestmark = pytest.mark.usefixtures("rts_up")


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

    def test_weak_next(self) -> None:
        """Verify weak_next (byte-parity with Go enrich.go / C++ enrich.cpp)."""
        f = Signal("Speed").less_than(220).weak_next().to_dict()
        assert format_formula(f) == "weak_next(Speed < 220)"

    def test_and(self) -> None:
        """Verify and."""
        f = Signal("Speed").less_than(220).and_(Signal("RPM").greater_than(500)).always().to_dict()
        assert format_formula(f) == "always(Speed < 220 and RPM > 500)"

    def test_or(self) -> None:
        """Verify or."""
        f = Signal("Speed").less_than(220).or_(Signal("RPM").greater_than(500)).always().to_dict()
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
        inner = Signal("Speed").less_than(220).and_(Signal("RPM").greater_than(500))
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
        f = Signal("S").between(10, Fraction("14.5")).always().to_dict()
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
        f = Signal("S").stable_within(2).always().to_dict()
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


class TestFormatRational:
    """FFI plumbing + DSL float ingress for the rational renderer.

    The renderer's MATH and SHAPE — every ``(numerator, denominator) → string``
    fact (decimal-vs-N/D fallback, trailing-zero trimming, sign, the k>18
    cross-binding guard) — are proven and pinned ONCE in the Agda kernel:
    ``RationalRenderer.Faithful.formatℚ-chars-represents`` (faithfulness) plus
    the ``RationalRenderer.Properties`` shape golden.  All three bindings render
    through that one kernel via ``aletheia_format_rational``, so the math is not
    re-asserted per binding (it used to be triplicated across Python/Go/C++).
    What stays here is binding-specific: that the FFI call plumbs a rendered
    rational into formula display for both output shapes, and that the Python DSL
    converts float inputs to exact Fractions before rendering.
    """

    def test_ffi_plumbs_non_terminating_as_fraction(self) -> None:
        """FFI plumbing: a non-terminating value reaches the formula in N/D shape."""
        f = Signal("S").equals(Fraction(1, 3)).always().to_dict()
        assert "S = 1/3" in format_formula(f)

    def test_ffi_plumbs_terminating_as_decimal(self) -> None:
        """FFI plumbing: a terminating value reaches the formula in decimal shape."""
        f = Signal("Voltage").greater_than_or_equal(Fraction(23, 2)).always().to_dict()
        assert "Voltage >= 11.5" in format_formula(f)

    def test_dsl_float_0_1_renders_as_decimal(self) -> None:
        """DSL float ingress: Signal.equals(0.1) scales to Fraction(1, 10), not IEEE 754 noise.

        Python's float→Fraction conversion uses 10^9 scaling (matching Go and
        C++), so 0.1 becomes Fraction(1, 10); without it the renderer would emit
        the 56-char exact decimal of the IEEE 754 binary fraction.
        """
        f = Signal("S").equals(Fraction("0.1")).always().to_dict()
        assert "S = 0.1" in format_formula(f)

    def test_dsl_large_integer_no_scientific(self) -> None:
        """DSL float ingress: large integer values stay exact, no scientific notation."""
        f = Signal("S").equals(1234567).always().to_dict()
        assert "S = 1234567" in format_formula(f)

    def test_dsl_high_precision_decimal_exact(self) -> None:
        """DSL float ingress: up to 9 significant figures convert exactly (10^9 scaling)."""
        f = Signal("S").equals(Fraction("0.123456789")).always().to_dict()
        assert "S = 0.123456789" in format_formula(f)


# ===========================================================================
# Signal collection
# ===========================================================================


class TestCollectSignals:
    """Test _collect_signals."""

    def test_multi_signal(self) -> None:
        """Verify multi signal."""
        f = Signal("Speed").less_than(220).and_(Signal("RPM").greater_than(500)).always().to_dict()
        signals = collect_signals(f)
        assert signals == ["Speed", "RPM"]

    def test_dedup(self) -> None:
        """Verify dedup."""
        f = Signal("Speed").less_than(220).and_(Signal("Speed").greater_than(0)).always().to_dict()
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

    def test_weak_next(self) -> None:
        """Verify weak_next subtree signals are walked, not dropped."""
        f = Signal("Speed").less_than(220).weak_next().to_dict()
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
        f = Signal("Speed").less_than(220).and_(Signal("RPM").greater_than(500)).always().to_dict()
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
        values: dict[str, Fraction | None] = {"Speed": Fraction(245)}
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
        values: dict[str, Fraction | None] = {"Speed": Fraction(245), "RPM": Fraction(3000)}
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
        values: dict[str, Fraction | None] = {"Speed": Fraction(245)}
        reason = format_enriched_reason(diag, values, core_reason="liveness timeout")
        assert reason.endswith("[core: liveness timeout]")
        assert "Speed = 245" in reason

    def test_core_reason_empty_is_omitted(self) -> None:
        """Verify core reason empty is omitted."""
        diag = PropertyDiagnostic(
            signals=("Speed",),
            formula_desc="always(Speed < 220)",
        )
        values: dict[str, Fraction | None] = {"Speed": Fraction(245)}
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

    def test_observed_value_renders_exactly_via_kernel(self) -> None:
        """The observed value uses the kernel formatℚ (exact), not lossy %g.

        Pins the r25 B5a fix (delegate rational rendering to the proven core): a
        large integer that old `%g` mangled to scientific notation
        (1234567 → "1.23457e+06") and a non-terminating fraction it rounded
        ("0.333333") now render exactly.
        """
        diag = PropertyDiagnostic(signals=("Big", "Third"), formula_desc="f")
        values: dict[str, Fraction | None] = {"Big": Fraction(1234567), "Third": Fraction(1, 3)}
        reason = format_enriched_reason(diag, values)
        assert "Big = 1234567" in reason  # not "1.23457e+06"
        assert "Third = 1/3" in reason  # not "0.333333"

    def test_dsl_roundtrip(self) -> None:
        """DSL formula -> diagnostic -> enriched reason."""
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = build_diagnostic(f)
        values: dict[str, Fraction | None] = {"Speed": Fraction(245)}
        reason = format_enriched_reason(diag, values)
        assert "Speed = 245" in reason
        assert "always(Speed < 220)" in reason


class TestRendererVocalWhenRTSDown:
    """Point 2: the renderer is vocal when the GHC RTS is uninitialised.

    Raises ``FFIError`` when the RTS is down and on a null kernel return — never a
    silent self-init or a fabricated ``"0"`` (parity with Go #104 / C++ #105). The
    eval path (observed values of an already-processed frame) degrades instead of
    propagating.
    """

    def test_format_formula_raises_when_rts_uninitialized(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A reachable-path render with the RTS down raises, not a fabricated value."""
        # Patch the STATE, not hs_initialized itself, so the real source-of-truth
        # chain (RTSState.initialized -> hs_initialized -> the guard) is exercised.
        monkeypatch.setattr("aletheia.client._ffi.RTSState.initialized", False)
        f = Signal("Speed").less_than(220).always().to_dict()
        with pytest.raises(FFIError, match="runtime not initialized"):
            format_formula(f)

    def test_format_formula_raises_on_null_render(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """A null kernel pointer raises ``FFIError``, not a silent ``"0"``."""

        # The RTS is genuinely up (the rts_up fixture), so hs_initialized() really
        # returns True; stub only the renderer lib to return a null pointer.
        class _NullLib:
            """Renderer-lib stub whose ``aletheia_format_rational`` returns null."""

            def aletheia_format_rational(self, _num: object, _den: object) -> None:
                """Return None to simulate the catastrophic null-pointer return."""

            def aletheia_free_str(self, _ptr: object) -> None:
                """No-op: nothing to free when the pointer is null."""

        monkeypatch.setattr(
            "aletheia.client._enrichment.get_renderer_lib",
            _NullLib,
        )
        f = Signal("Speed").less_than(220).always().to_dict()
        with pytest.raises(FFIError, match="null"):
            format_formula(f)

    def test_enriched_reason_degrades_on_render_failure(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Eval path: a render failure degrades the whole reason.

        Still appends ``[core: ...]`` and never sinks the already-processed frame.
        """
        f = Signal("Speed").less_than(220).always().to_dict()
        diag = build_diagnostic(f)  # real render (RTS up via the module fixture)

        def _boom(_value: Fraction) -> str:
            msg = "simulated null render"
            raise FFIError(msg)

        monkeypatch.setattr("aletheia.client._enrichment.format_rational", _boom)
        values: dict[str, Fraction | None] = {"Speed": Fraction(245)}
        reason = format_enriched_reason(diag, values, core_reason="kernel: X")
        assert reason == "violated: " + diag.formula_desc + " [core: kernel: X]"
