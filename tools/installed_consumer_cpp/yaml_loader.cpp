// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The YAML loader, linked from the installed package, refuses a document that
// does not exist; the refusal coming back is the pass.
#include <aletheia/yaml.hpp>

int main() {
    auto const checks = aletheia::load_checks_from_yaml("/nonexistent/checks.yaml");
    return checks.has_value() ? 1 : 0;
}
