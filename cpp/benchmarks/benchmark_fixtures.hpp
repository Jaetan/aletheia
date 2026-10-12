// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The DBC definitions, frames, signal values and LTL properties the benchmark
// modes measure against.

#include <aletheia/aletheia.hpp>

#include <vector>

namespace aletheia::bench {

auto make_can20_dbc() -> DbcDefinition;
auto make_canfd_dbc() -> DbcDefinition;

auto can20_frame() -> const FramePayload&;
inline constexpr auto can20_id = CanId{StandardId::create(0x100).value()};
inline constexpr auto can20_dlc = Dlc::create(8).value();

auto canfd_frame() -> const FramePayload&;
inline constexpr auto canfd_id = CanId{StandardId::create(0x200).value()};
inline constexpr auto canfd_dlc = Dlc::create(15).value();

auto can20_signals() -> const std::vector<SignalValue>&;
auto canfd_signals() -> const std::vector<SignalValue>&;

auto make_can20_properties() -> std::vector<LtlFormula>;
auto make_canfd_properties() -> std::vector<LtlFormula>;

} // namespace aletheia::bench
