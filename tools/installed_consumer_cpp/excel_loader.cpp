// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The Excel loader, linked from the installed package, refuses a workbook that
// does not exist; the refusal coming back is the pass.
#include <aletheia/excel.hpp>

int main() {
    auto const checks = aletheia::load_checks_from_excel("/nonexistent/checks.xlsx");
    return checks.has_value() ? 1 : 0;
}
