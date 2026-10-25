//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"os"
	"path/filepath"
)

// findFFILibrary is the library a test opens: the one the environment names,
// then the places a build leaves it relative to where the tests run. Empty
// when none of them has it.
func findFFILibrary() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	candidates := []string{
		"../../build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"build/libaletheia-ffi.so",
	}
	// The working directory is read once: it is the one thing that can fail
	// here, and it fails for every candidate alike.
	cwd, err := os.Getwd()
	if err != nil {
		return ""
	}
	for _, c := range candidates {
		abs := filepath.Join(cwd, c)
		if _, err := os.Stat(abs); err == nil {
			return abs
		}
	}
	return ""
}
