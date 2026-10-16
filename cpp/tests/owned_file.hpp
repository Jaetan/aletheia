// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// One owner for a C stream a test opens, which closes it when it goes.

#include <cstdio>
#include <memory>

namespace aletheia::test {

struct CloseFile {
    void operator()(std::FILE* file) const { (void)std::fclose(file); }
};
using File = std::unique_ptr<std::FILE, CloseFile>;

} // namespace aletheia::test
