//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

// cgoEnabled is whether this build can load the library at all. The binding
// reaches the kernel through cgo and dlopen, so without it a built
// libaletheia-ffi.so is a file the loader cannot use. Only the cases that
// measure consult this.
const cgoEnabled = true
