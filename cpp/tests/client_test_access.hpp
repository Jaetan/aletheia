// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The tests' way into a client's diagnostics: no formula builds a diagnostic
// naming no signal, so a test that needs one replaces those set_properties
// built.

#include <aletheia/client.hpp>
#include <aletheia/response.hpp>

#include <utility>
#include <vector>

namespace aletheia::detail {

struct ClientTestAccess {
    static void set_diagnostics(AletheiaClient& client, std::vector<PropertyDiagnostic> diags) {
        client.diags_ = std::move(diags);
    }
};

} // namespace aletheia::detail
