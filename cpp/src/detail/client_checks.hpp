// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The payload-length check and the cancellation error that the definitions of
// AletheiaClient's members share.

#include <aletheia/error.hpp>
#include <aletheia/types.hpp>

#include <cstddef>
#include <span>
#include <string_view>

namespace aletheia::detail {

auto validate_payload(Dlc dlc, std::span<const std::byte> data) -> Result<void>;
auto make_cancellation_error(std::string_view method) -> AletheiaError;

} // namespace aletheia::detail
