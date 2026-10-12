// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The count of full-frame extractions a mock backend was asked for, which
// the enrichment tests compare against the extractions they expect.

#include "detail/mock_backend.hpp"

#include <algorithm>
#include <cstddef>

namespace aletheia::test {

// One sentinel per logical full-frame extraction: the call cardinality the
// extract-once shape pins.
inline auto count_extraction_sentinels(const MockBackend& mock) -> std::size_t {
    return static_cast<std::size_t>(
        std::ranges::count(mock.captured(), "<binary:extractAllSignals>"));
}

} // namespace aletheia::test
