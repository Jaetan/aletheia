// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"
)

// repoRoot is the repository the package's tests read their fixtures and
// documents from: the one ALETHEIA_REPO_ROOT names, the variable the C++ suite
// reads too, and otherwise the one this source file sits two directories
// below. A copy of the go/ module alone, which is what the mutation sweep
// tests each mutant in, finds the repository only through the variable.
func repoRoot(tb testing.TB) string {
	tb.Helper()
	if root := os.Getenv("ALETHEIA_REPO_ROOT"); root != "" {
		return root
	}
	_, here, _, ok := runtime.Caller(0)
	if !ok {
		tb.Fatal("runtime.Caller(0) failed")
	}
	return filepath.Join(filepath.Dir(here), "..", "..")
}

// RepoRoot is repoRoot for the external test package.
var RepoRoot = repoRoot
