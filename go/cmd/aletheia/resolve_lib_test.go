// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

// The CLI's search for the kernel library: resolveLib from each directory the
// CLI runs from, and newClient's error when nothing is in reach.

import (
	"os"
	"path/filepath"
	"testing"
)

// plant writes an empty file at path, making its directories, for a test that
// asks resolveLib to find it.
func plant(t *testing.T, path string) os.FileInfo {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("os.MkdirAll: %v", err)
	}
	if err := os.WriteFile(path, nil, 0o644); err != nil {
		t.Fatalf("os.WriteFile: %v", err)
	}
	fi, err := os.Stat(path)
	if err != nil {
		t.Fatalf("os.Stat: %v", err)
	}
	return fi
}

// deepEmptyDir makes an empty directory nested deep enough that every relative
// directory resolveLib searches from it lies inside the test's own temporary
// tree.
func deepEmptyDir(t *testing.T) string {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "a", "b", "c")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatalf("os.MkdirAll: %v", err)
	}
	return dir
}

// TestResolveLibFindsTheBuildTree: from each directory the CLI runs from, the
// repository root, go/ and go/cmd/aletheia, resolveLib finds the root's
// build/libaletheia-ffi.so in a planted tree, ALETHEIA_LIB empty and no system
// library in reach.
func TestResolveLibFindsTheBuildTree(t *testing.T) {
	root := t.TempDir()
	want := plant(t, filepath.Join(root, "build", "libaletheia-ffi.so"))
	sysRoot := t.TempDir()
	for _, dir := range []string{".", "go", filepath.Join("go", "cmd", "aletheia")} {
		t.Run(dir, func(t *testing.T) {
			wd := filepath.Join(root, dir)
			if err := os.MkdirAll(wd, 0o755); err != nil {
				t.Fatalf("os.MkdirAll: %v", err)
			}
			t.Chdir(wd)
			t.Setenv("ALETHEIA_LIB", "")
			got := resolveLib(sysRoot)
			if fi, err := os.Stat(got); err != nil || !os.SameFile(fi, want) {
				t.Errorf("from %s, resolveLib = %q; want the root's build/libaletheia-ffi.so", dir, got)
			}
		})
	}
}

// TestResolveLibFallsBackToTheSystemDirectory: with no build tree in reach,
// resolveLib finds usr/local/lib/libaletheia-ffi.so under the system root it is
// given.
func TestResolveLibFallsBackToTheSystemDirectory(t *testing.T) {
	sysRoot := t.TempDir()
	so := filepath.Join(sysRoot, "usr", "local", "lib", "libaletheia-ffi.so")
	plant(t, so)
	t.Chdir(deepEmptyDir(t))
	t.Setenv("ALETHEIA_LIB", "")
	if got := resolveLib(sysRoot); got != so {
		t.Errorf("resolveLib = %q; want %q", got, so)
	}
}

// TestResolveLibTakesTheEnvironmentFirst: a set ALETHEIA_LIB is the answer as
// given, unchecked, ahead of a build tree in reach.
func TestResolveLibTakesTheEnvironmentFirst(t *testing.T) {
	root := t.TempDir()
	plant(t, filepath.Join(root, "build", "libaletheia-ffi.so"))
	t.Chdir(root)
	const env = "/nonexistent/libaletheia-ffi.so"
	t.Setenv("ALETHEIA_LIB", env)
	if got := resolveLib(t.TempDir()); got != env {
		t.Errorf("resolveLib = %q; want %q", got, env)
	}
}

// TestResolveLibAnswersNothingOutOfReach: with no library in reach, resolveLib
// answers the empty path.
func TestResolveLibAnswersNothingOutOfReach(t *testing.T) {
	t.Chdir(deepEmptyDir(t))
	t.Setenv("ALETHEIA_LIB", "")
	if got := resolveLib(t.TempDir()); got != "" {
		t.Errorf("resolveLib = %q; want none", got)
	}
}

// TestNewClientNotFound: with no library in reach, newClient's error is the
// line the C++ CLI prints. The system directory is searched from the root, not
// from the working directory, so a library under the working directory's
// usr/local/lib is not taken. A machine with the library installed in
// /usr/local/lib answers from it, so the test skips on one.
func TestNewClientNotFound(t *testing.T) {
	if _, err := os.Stat("/usr/local/lib/libaletheia-ffi.so"); err == nil {
		t.Skip("libaletheia-ffi.so is installed in /usr/local/lib")
	}
	wd := deepEmptyDir(t)
	plant(t, filepath.Join(wd, "usr", "local", "lib", "libaletheia-ffi.so"))
	t.Chdir(wd)
	t.Setenv("ALETHEIA_LIB", "")
	const want = "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'"
	if _, err := newClient(); err == nil || err.Error() != want {
		t.Errorf("newClient error = %v; want %q", err, want)
	}
}
