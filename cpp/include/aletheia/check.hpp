// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Industry-vocabulary Check API for CAN signal verification.
//
// Provides fluent, domain-specific wrappers over the LTL layer so that
// automotive technicians can define signal checks without knowing
// temporal logic.
//
// ```cpp
// auto speed_limit = check::signal("Speed").never_exceeds(PhysicalValue::of(220, 1));
// // A Result<CheckResult>: within refuses a negative or overflowing bound.
// auto brake_light = check::when("Brake").exceeds(PhysicalValue::of(50, 1))
//                        .then("BrakeLight").equals(PhysicalValue::of(1, 1))
//                        .within(std::chrono::milliseconds{100});
// ```
//
// Every check compiles to the same LtlFormula used by the LTL layer.
//
#pragma once

// check.hpp wraps LtlFormula construction and uses SignalName/PhysicalValue
// throughout its builder API, so callers that include check.hpp always need
// the ltl and types vocabulary.
#include <aletheia/detail/checked.hpp>
#include <aletheia/error.hpp>
#include <aletheia/ltl.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp> // IWYU pragma: export

#include <chrono>
#include <cstdint>
#include <expected>
#include <format>
#include <limits>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia::detail {

// One piece of a check's condition description: literal text, or a threshold
// the kernel renders when the description is read, so building a check needs
// no runtime and only reading its description can fail. Go (descPart), Rust
// (DescPart) and Python (_DescPart) hold a description the same way.
using DescPart = std::variant<std::string, Rational>;

// The text `parts` spell, every threshold rendered by the kernel: the text, or
// the renderer's error. Defined in enrich.cpp.
[[nodiscard]] auto render_desc(std::span<const DescPart> parts) -> Result<std::string>;

// The refusal's text for a range whose lo is above its hi, naming the builder
// `op` and both bounds, or nullopt; Rust and Go word it the same. Defined in
// enrich.cpp.
[[nodiscard]] auto range_refusal(std::string_view op, PhysicalValue lo, PhysicalValue hi)
    -> std::optional<std::string>;

// An operator prefix followed by one threshold, such as "<= " and the value.
[[nodiscard]] inline auto op_desc(std::string op, PhysicalValue v) -> std::vector<DescPart> {
    return {DescPart{std::move(op)}, DescPart{v.get()}};
}

[[nodiscard]] inline auto between_desc(PhysicalValue lo, PhysicalValue hi)
    -> std::vector<DescPart> {
    return {DescPart{"between "}, DescPart{lo.get()}, DescPart{" and "}, DescPart{hi.get()}};
}

[[nodiscard]] inline auto within_desc(std::vector<DescPart> parts, std::chrono::milliseconds ms)
    -> std::vector<DescPart> {
    parts.emplace_back(std::format(" within {}ms", ms.count()));
    return parts;
}

// Convert a millisecond bound into the Timestamp (microsecond) domain, refusing
// a negative bound and an ms→µs multiply that would overflow int64.  The overflow
// is reachable from untrusted input (e.g. a YAML check with `within_ms:
// 9300000000000000`), where `duration_cast<microseconds>` would otherwise be
// signed-integer UB.  Mirrors the Go (`check.go`, `MaxInt64/usPerMillisecond`)
// and Rust overflow guards.
[[nodiscard]] inline auto checked_ms_to_us(std::chrono::milliseconds ms) -> Result<Timestamp> {
    if (ms.count() < 0)
        return validation_refusal("time must be non-negative");
    if (ms.count() > std::numeric_limits<Timestamp::rep>::max() / us_per_millisecond)
        return validation_refusal("time overflows microsecond conversion");
    return std::chrono::duration_cast<Timestamp>(ms);
}

} // namespace aletheia::detail

namespace aletheia {

// ---------------------------------------------------------------------------
// CheckResult: terminal object wrapping a formula with optional metadata
// ---------------------------------------------------------------------------

class CheckResult {
public:
    explicit CheckResult(LtlFormula f) : formula_(std::move(f)) {}

    CheckResult(LtlFormula f, std::string sig, std::string desc)
        : formula_(std::move(f))
        , signal_name_(std::move(sig))
        , condition_desc_{detail::DescPart{std::move(desc)}} {}

    auto named(std::string name) -> CheckResult& {
        name_ = std::move(name);
        return *this;
    }

    auto severity(std::string level) -> CheckResult& {
        check_severity_ = std::move(level);
        return *this;
    }

    [[nodiscard]] auto to_formula() const -> LtlFormula { return ltl::clone(formula_); }

    [[nodiscard]] auto formula() const -> const LtlFormula& { return formula_; }

    [[nodiscard]] auto name() const -> const std::string& { return name_; }
    [[nodiscard]] auto check_severity() const -> const std::string& { return check_severity_; }
    [[nodiscard]] auto signal_name() const -> const std::string& { return signal_name_; }
    // The condition in words, its thresholds rendered by the kernel on every
    // read: the text, or an error of kind Ffi while the GHC runtime is down.
    [[nodiscard]] auto condition_desc() const -> Result<std::string> {
        return detail::render_desc(condition_desc_);
    }

private:
    friend class CheckSignal;
    friend class CheckSignalPredicate;
    friend class SettlesBuilder;
    friend class ThenCondition;

    CheckResult(LtlFormula f, std::string sig, std::vector<detail::DescPart> desc)
        : formula_(std::move(f))
        , signal_name_(std::move(sig))
        , condition_desc_(std::move(desc)) {}

    LtlFormula formula_;
    std::string name_;
    std::string check_severity_;
    std::string signal_name_;
    std::vector<detail::DescPart> condition_desc_;
};

// ---------------------------------------------------------------------------
// Single-signal check builders
// ---------------------------------------------------------------------------

class CheckSignalPredicate {
public:
    [[nodiscard]] auto always() && -> CheckResult {
        return {std::move(formula_), std::move(signal_name_), std::move(condition_desc_)};
    }

private:
    friend class CheckSignal;

    CheckSignalPredicate(LtlFormula f, std::string sig, std::vector<detail::DescPart> desc)
        : formula_(std::move(f))
        , signal_name_(std::move(sig))
        , condition_desc_(std::move(desc)) {}

    LtlFormula formula_;
    std::string signal_name_;
    std::vector<detail::DescPart> condition_desc_;
};

class SettlesBuilder {
public:
    SettlesBuilder(std::string sig, PhysicalValue lo, PhysicalValue hi)
        : signal_name_(std::move(sig))
        , lo_(lo)
        , hi_(hi) {}

    // The check, or a Validation error for an inverted range, a negative bound
    // or one whose microseconds overflow int64.
    [[nodiscard]] auto within(std::chrono::milliseconds ms) const -> Result<CheckResult> {
        if (auto refusal = detail::range_refusal("settles_between", lo_, hi_))
            return detail::validation_refusal(std::move(refusal).value());
        auto const us = detail::checked_ms_to_us(ms);
        if (!us)
            return std::unexpected(detail::error_of(us));
        auto f = ltl::always_within(us.value(),
                                    ltl::atomic(ltl::between(SignalName{signal_name_}, lo_, hi_)));
        return CheckResult{std::move(f), signal_name_,
                           detail::within_desc(detail::between_desc(lo_, hi_), ms)};
    }

private:
    std::string signal_name_;
    PhysicalValue lo_;
    PhysicalValue hi_;
};

class CheckSignal {
public:
    explicit CheckSignal(std::string name) : name_(std::move(name)) {}

    // G(signal <= value): never goes above value, and value itself is allowed
    // (inclusive — matches the Agda core's LessThanOrEqual and the dual
    // never_below's >=; "never exceeds 220" lets 220 pass).
    [[nodiscard]] auto never_exceeds(PhysicalValue value) const -> CheckResult {
        auto f = ltl::always(ltl::atomic(ltl::less_than_or_equal(SignalName{name_}, value)));
        return {std::move(f), name_, detail::op_desc("<= ", value)};
    }

    [[nodiscard]] auto never_below(PhysicalValue value) const -> CheckResult {
        auto f = ltl::always(ltl::atomic(ltl::greater_than_or_equal(SignalName{name_}, value)));
        return {std::move(f), name_, detail::op_desc(">= ", value)};
    }

    // The check, or a Validation error for lo above hi.
    [[nodiscard]] auto stays_between(PhysicalValue lo, PhysicalValue hi) const
        -> Result<CheckResult> {
        if (auto refusal = detail::range_refusal("stays_between", lo, hi))
            return detail::validation_refusal(std::move(refusal).value());
        auto f = ltl::always(ltl::atomic(ltl::between(SignalName{name_}, lo, hi)));
        return CheckResult{std::move(f), name_, detail::between_desc(lo, hi)};
    }

    [[nodiscard]] auto never_equals(PhysicalValue value) const -> CheckResult {
        auto f = ltl::never(ltl::equals(SignalName{name_}, value));
        return {std::move(f), name_, detail::op_desc("!= ", value)};
    }

    [[nodiscard]] auto equals(PhysicalValue value) const -> CheckSignalPredicate {
        auto f = ltl::always(ltl::atomic(ltl::equals(SignalName{name_}, value)));
        return {std::move(f), name_, detail::op_desc("= ", value)};
    }

    // The builder; its within refuses lo above hi, so the chain is read once.
    [[nodiscard]] auto settles_between(PhysicalValue lo, PhysicalValue hi) const -> SettlesBuilder {
        return {name_, lo, hi};
    }

private:
    std::string name_;
};

// ---------------------------------------------------------------------------
// When / Then causal check builders
// ---------------------------------------------------------------------------

class ThenCondition {
public:
    // The check, or a Validation error for an inverted stays_between range, a
    // negative bound or one whose microseconds overflow int64.
    [[nodiscard]] auto within(std::chrono::milliseconds ms) const -> Result<CheckResult> {
        if (range_refusal_)
            return detail::validation_refusal(range_refusal_.value());
        auto const us = detail::checked_ms_to_us(ms);
        if (!us)
            return std::unexpected(detail::error_of(us));
        auto f = ltl::always(ltl::either(ltl::negate(ltl::atomic(trigger_)),
                                         ltl::within(us.value(), ltl::atomic(then_pred_))));
        return CheckResult{std::move(f), then_signal_, detail::within_desc(then_desc_, ms)};
    }

private:
    friend class ThenSignal;

    ThenCondition(Predicate trigger, Predicate then_pred, std::string then_signal,
                  std::vector<detail::DescPart> then_desc,
                  std::optional<std::string> range_refusal = std::nullopt)
        : trigger_(std::move(trigger))
        , then_pred_(std::move(then_pred))
        , then_signal_(std::move(then_signal))
        , then_desc_(std::move(then_desc))
        , range_refusal_(std::move(range_refusal)) {}

    Predicate trigger_;
    Predicate then_pred_;
    std::string then_signal_;
    std::vector<detail::DescPart> then_desc_;
    std::optional<std::string> range_refusal_;
};

class ThenSignal {
public:
    ThenSignal(Predicate trigger, std::string then_signal_name)
        : trigger_(std::move(trigger))
        , then_name_(std::move(then_signal_name)) {}

    [[nodiscard]] auto equals(PhysicalValue value) const -> ThenCondition {
        return {trigger_, ltl::equals(SignalName{then_name_}, value), then_name_,
                detail::op_desc("= ", value)};
    }

    [[nodiscard]] auto exceeds(PhysicalValue value) const -> ThenCondition {
        return {trigger_, ltl::greater_than(SignalName{then_name_}, value), then_name_,
                detail::op_desc("> ", value)};
    }

    // The condition; its within refuses lo above hi, so the chain is read once.
    [[nodiscard]] auto stays_between(PhysicalValue lo, PhysicalValue hi) const -> ThenCondition {
        return {trigger_, ltl::between(SignalName{then_name_}, lo, hi), then_name_,
                detail::between_desc(lo, hi), detail::range_refusal("then stays_between", lo, hi)};
    }

private:
    Predicate trigger_;
    std::string then_name_;
};

class WhenCondition {
public:
    explicit WhenCondition(Predicate trigger) : trigger_(std::move(trigger)) {}

    [[nodiscard]] auto then(std::string signal_name) const -> ThenSignal {
        return {trigger_, std::move(signal_name)};
    }

private:
    Predicate trigger_;
};

class WhenSignal {
public:
    explicit WhenSignal(std::string name) : name_(std::move(name)) {}

    [[nodiscard]] auto exceeds(PhysicalValue value) const -> WhenCondition {
        return WhenCondition{ltl::greater_than(SignalName{name_}, value)};
    }

    [[nodiscard]] auto equals(PhysicalValue value) const -> WhenCondition {
        return WhenCondition{ltl::equals(SignalName{name_}, value)};
    }

    [[nodiscard]] auto drops_below(PhysicalValue value) const -> WhenCondition {
        return WhenCondition{ltl::less_than(SignalName{name_}, value)};
    }

private:
    std::string name_;
};

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

namespace check {

[[nodiscard]] inline auto signal(std::string name) -> CheckSignal {
    return CheckSignal{std::move(name)};
}

[[nodiscard]] inline auto when(std::string signal_name) -> WhenSignal {
    return WhenSignal{std::move(signal_name)};
}

} // namespace check

} // namespace aletheia
