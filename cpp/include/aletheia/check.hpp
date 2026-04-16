// SPDX-License-Identifier: BSD-2-Clause
//
// Industry-vocabulary Check API for CAN signal verification.
//
// Provides fluent, domain-specific wrappers over the LTL layer so that
// automotive technicians can define signal checks without knowing
// temporal logic.
//
//   Check::signal("Speed").never_exceeds(PhysicalValue{220});
//   Check::when("Brake").exceeds(PhysicalValue{50})
//       .then("BrakeLight").equals(PhysicalValue{1}).within(100ms);
//
// Every check compiles to the same LtlFormula used by the LTL layer.
//
#pragma once

// check.hpp wraps LtlFormula construction and uses SignalName/PhysicalValue
// throughout its builder API, so callers that include check.hpp always need
// the ltl and types vocabulary.
#include <aletheia/ltl.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp> // IWYU pragma: export

#include <chrono>
#include <format>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>

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
        , condition_desc_(std::move(desc)) {}

    auto named(std::string name) -> CheckResult& {
        name_ = std::move(name);
        return *this;
    }

    auto severity(std::string level) -> CheckResult& {
        check_severity_ = std::move(level);
        return *this;
    }

    [[nodiscard]] auto to_formula() const -> std::optional<LtlFormula> {
        if (!formula_)
            return std::nullopt;
        return ltl::clone(*formula_);
    }

    [[nodiscard]] auto formula() const -> const std::optional<LtlFormula>& { return formula_; }

    [[nodiscard]] auto name() const -> const std::string& { return name_; }
    [[nodiscard]] auto check_severity() const -> const std::string& { return check_severity_; }
    [[nodiscard]] auto signal_name() const -> const std::string& { return signal_name_; }
    [[nodiscard]] auto condition_desc() const -> const std::string& { return condition_desc_; }

private:
    std::optional<LtlFormula> formula_;
    std::string name_;
    std::string check_severity_;
    std::string signal_name_;
    std::string condition_desc_;
};

// ---------------------------------------------------------------------------
// Single-signal check builders
// ---------------------------------------------------------------------------

class CheckSignalPredicate {
public:
    CheckSignalPredicate(LtlFormula f, std::string sig, std::string desc)
        : formula_(std::move(f))
        , signal_name_(std::move(sig))
        , condition_desc_(std::move(desc)) {}

    auto always() && -> CheckResult {
        return {std::move(formula_), std::move(signal_name_), std::move(condition_desc_)};
    }

private:
    LtlFormula formula_;
    std::string signal_name_;
    std::string condition_desc_;
};

class SettlesBuilder {
public:
    SettlesBuilder(std::string sig, PhysicalValue lo, PhysicalValue hi)
        : signal_name_(std::move(sig))
        , lo_(lo)
        , hi_(hi) {}

    [[nodiscard]] auto within(std::chrono::milliseconds ms) const -> CheckResult {
        if (ms.count() < 0)
            throw std::invalid_argument("time must be non-negative");
        auto us = std::chrono::duration_cast<Timestamp>(ms);
        auto f =
            ltl::always_within(us, ltl::atomic(ltl::between(SignalName{signal_name_}, lo_, hi_)));
        return {std::move(f), signal_name_,
                std::format("between {:g} and {:g} within {}ms", lo_.get().to_double(), hi_.get().to_double(), ms.count())};
    }

private:
    std::string signal_name_;
    PhysicalValue lo_;
    PhysicalValue hi_;
};

class CheckSignal {
public:
    explicit CheckSignal(std::string name) : name_(std::move(name)) {}

    [[nodiscard]] auto never_exceeds(PhysicalValue value) const -> CheckResult {
        auto f = ltl::always(ltl::atomic(ltl::less_than(SignalName{name_}, value)));
        return {std::move(f), name_, std::format("< {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto never_below(PhysicalValue value) const -> CheckResult {
        auto f = ltl::always(ltl::atomic(ltl::at_least(SignalName{name_}, value)));
        return {std::move(f), name_, std::format(">= {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto stays_between(PhysicalValue lo, PhysicalValue hi) const -> CheckResult {
        if (lo.get() > hi.get())
            throw std::invalid_argument("stays_between: lo must be <= hi");
        auto f = ltl::always(ltl::atomic(ltl::between(SignalName{name_}, lo, hi)));
        return {std::move(f), name_, std::format("between {:g} and {:g}", lo.get().to_double(), hi.get().to_double())};
    }

    [[nodiscard]] auto never_equals(PhysicalValue value) const -> CheckResult {
        auto f = ltl::never(ltl::equals(SignalName{name_}, value));
        return {std::move(f), name_, std::format("!= {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto equals(PhysicalValue value) const -> CheckSignalPredicate {
        auto f = ltl::always(ltl::atomic(ltl::equals(SignalName{name_}, value)));
        return {std::move(f), name_, std::format("= {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto settles_between(PhysicalValue lo, PhysicalValue hi) const -> SettlesBuilder {
        if (lo.get() > hi.get())
            throw std::invalid_argument("settles_between: lo must be <= hi");
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
    ThenCondition(Predicate trigger, Predicate then_pred, std::string then_signal,
                  std::string then_desc)
        : trigger_(std::move(trigger))
        , then_pred_(std::move(then_pred))
        , then_signal_(std::move(then_signal))
        , then_desc_(std::move(then_desc)) {}

    [[nodiscard]] auto within(std::chrono::milliseconds ms) const -> CheckResult {
        if (ms.count() < 0)
            throw std::invalid_argument("time must be non-negative");
        auto us = std::chrono::duration_cast<Timestamp>(ms);
        auto f = ltl::always(ltl::either(ltl::negate(ltl::atomic(trigger_)),
                                         ltl::within(us, ltl::atomic(then_pred_))));
        std::string desc;
        if (!then_desc_.empty())
            desc = then_desc_ + std::format(" within {}ms", ms.count());
        return {std::move(f), then_signal_, std::move(desc)};
    }

private:
    Predicate trigger_;
    Predicate then_pred_;
    std::string then_signal_;
    std::string then_desc_;
};

class ThenSignal {
public:
    ThenSignal(Predicate trigger, std::string then_signal_name)
        : trigger_(std::move(trigger))
        , then_name_(std::move(then_signal_name)) {}

    [[nodiscard]] auto equals(PhysicalValue value) const -> ThenCondition {
        return {trigger_, ltl::equals(SignalName{then_name_}, value), then_name_,
                std::format("= {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto exceeds(PhysicalValue value) const -> ThenCondition {
        return {trigger_, ltl::greater_than(SignalName{then_name_}, value), then_name_,
                std::format("> {:g}", value.get().to_double())};
    }

    [[nodiscard]] auto stays_between(PhysicalValue lo, PhysicalValue hi) const -> ThenCondition {
        if (lo.get() > hi.get())
            throw std::invalid_argument("stays_between: lo must be <= hi");
        return {trigger_, ltl::between(SignalName{then_name_}, lo, hi), then_name_,
                std::format("between {:g} and {:g}", lo.get().to_double(), hi.get().to_double())};
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

class Check {
public:
    static auto signal(std::string name) -> CheckSignal { return CheckSignal{std::move(name)}; }

    static auto when(std::string signal_name) -> WhenSignal {
        return WhenSignal{std::move(signal_name)};
    }
};

} // namespace aletheia
