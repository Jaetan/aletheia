//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// The structures the cgo preamble declares lay out as haskell-shim/include/aletheia.h
// fixes them. The expected sizes and offsets are read from the header's own
// static_assert lines, which the C compiler holds to the real layout, so a
// field moved on either side fails here rather than misreading across the ABI.
func TestFFIStructuresMatchKernelHeader(t *testing.T) {
	text, err := os.ReadFile(filepath.Join(repoRoot(t), "haskell-shim", "include", "aletheia.h"))
	if err != nil {
		t.Fatal(err)
	}
	wantSizes := map[string]uintptr{}
	for _, m := range regexp.MustCompile(`static_assert\(sizeof\(struct (\w+)\) == (\d+),`).FindAllStringSubmatch(string(text), -1) {
		wantSizes[m[1]] = parseOffset(t, m[2])
	}
	wantFields := map[string][]abiField{}
	for _, m := range regexp.MustCompile(`static_assert\(offsetof\(struct (\w+), (\w+)\) == (\d+),`).FindAllStringSubmatch(string(text), -1) {
		wantFields[m[1]] = append(wantFields[m[1]], abiField{m[2], parseOffset(t, m[3])})
	}

	version := regexp.MustCompile(`enum \{ ALETHEIA_ABI_VERSION = (\d+) \};`).FindStringSubmatch(string(text))
	if version == nil || parseOffset(t, version[1]) != abiVersion {
		t.Errorf("abiVersion = %d, header defines %v", abiVersion, version)
	}

	sizes, fields := abiLayout()
	if !reflect.DeepEqual(sizes, wantSizes) {
		t.Errorf("sizes = %v, header asserts %v", sizes, wantSizes)
	}
	if !reflect.DeepEqual(fields, wantFields) {
		t.Errorf("fields = %v, header asserts %v", fields, wantFields)
	}
}

// The backend admits a library at its own ABI version and names both
// versions when it refuses any other.
func TestABIVersionErrorAdmitsOnlyTheBindingsVersion(t *testing.T) {
	if err := abiVersionError(abiVersion); err != nil {
		t.Fatalf("the binding's own version was refused: %v", err)
	}
	for _, found := range []uint32{abiVersion - 1, abiVersion + 1} {
		err := abiVersionError(found)
		want := fmt.Sprintf("the library implements ABI version %d, and this binding needs %d", found, abiVersion)
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("abiVersionError(%d) = %v, want an error carrying %q", found, err, want)
		}
	}
}

func parseOffset(t *testing.T, digits string) uintptr {
	t.Helper()
	n, err := strconv.ParseUint(digits, 10, 64)
	if err != nil {
		t.Fatal(err)
	}
	return uintptr(n)
}
