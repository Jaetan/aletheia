//go:build cgo

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

// cgoEnabled is whether this build can load the library at all. The binding
// reaches the kernel through cgo and dlopen, so without it a built
// libaletheia-ffi.so is a file the loader cannot use, and a test that drives
// the real interface has nothing to drive. The tests that read the source
// rather than run the interface do not consult this.
const cgoEnabled = true
