// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Runtime GHC RTS parameters — Go parity (the Go leg of the K.1 runtime tier).
//
// Reads docs/RESOURCE_BUDGETS.yaml (the cross-binding SSOT, itself enforced
// against every binding by the `check-rts-runtime` run_ci gate) and asserts the
// Go mirror constants (rts.go) match — plus the pure argv builder rtsInitArgv.
// An internal `package aletheia` test (not aletheia_test) so it reads the
// UNEXPORTED mirror constants directly, matching how the Python / C++ / Rust
// mirrors are private to their binding. No cgo / no FFI needed.
package aletheia

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"gopkg.in/yaml.v3"
)

type rtsBudgetDoc struct {
	Runtime struct {
		HeapCap struct {
			Flag        string `yaml:"flag"`
			Bytes       int64  `yaml:"bytes"`
			OverrideEnv string `yaml:"override_env"`
		} `yaml:"heap_cap"`
		DefaultCores struct {
			Value int `yaml:"value"`
		} `yaml:"default_cores"`
		InitSymbol string `yaml:"init_symbol"`
	} `yaml:"runtime"`
}

func loadRTSBudget(t *testing.T) rtsBudgetDoc {
	t.Helper()
	_, here, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("runtime.Caller(0) failed")
	}
	yamlPath := filepath.Join(filepath.Dir(here), "..", "..", "docs", "RESOURCE_BUDGETS.yaml")
	data, err := os.ReadFile(yamlPath)
	if err != nil {
		t.Fatalf("read %s: %v", yamlPath, err)
	}
	var doc rtsBudgetDoc
	if err := yaml.Unmarshal(data, &doc); err != nil {
		t.Fatalf("unmarshal %s: %v", yamlPath, err)
	}
	return doc
}

func TestRTSParamsMirrorSSOT(t *testing.T) {
	doc := loadRTSBudget(t)
	if doc.Runtime.HeapCap.Flag != rtsHeapCapFlag {
		t.Errorf("heap cap: SSOT=%q Go=%q", doc.Runtime.HeapCap.Flag, rtsHeapCapFlag)
	}
	if doc.Runtime.DefaultCores.Value != rtsDefaultCores {
		t.Errorf("default cores: SSOT=%d Go=%d", doc.Runtime.DefaultCores.Value, rtsDefaultCores)
	}
	if doc.Runtime.InitSymbol != rtsInitSymbol {
		t.Errorf("init symbol: SSOT=%q Go=%q", doc.Runtime.InitSymbol, rtsInitSymbol)
	}
	if doc.Runtime.HeapCap.OverrideEnv != rtsOverrideEnv {
		t.Errorf("override env: SSOT=%q Go=%q", doc.Runtime.HeapCap.OverrideEnv, rtsOverrideEnv)
	}
}

func eqStrings(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func TestRTSInitArgvAlwaysCarriesCap(t *testing.T) {
	// Force a known override-env state so the builder is deterministic.
	t.Setenv(rtsOverrideEnv, "")

	// Default cores: cap present, no -N.
	if got := rtsInitArgv(1); !eqStrings(got, []string{"aletheia", "+RTS", rtsHeapCapFlag, "-RTS"}) {
		t.Errorf("cores=1: got %v", got)
	}
	// Multi-core: -N appended after the cap.
	if got := rtsInitArgv(4); !eqStrings(got, []string{"aletheia", "+RTS", rtsHeapCapFlag, "-N4", "-RTS"}) {
		t.Errorf("cores=4: got %v", got)
	}

	// Override flags land after the cap (so a caller -M occurs last, wins).
	t.Setenv(rtsOverrideEnv, "  -M12M   -hT ")
	if got := rtsInitArgv(1); !eqStrings(got, []string{"aletheia", "+RTS", rtsHeapCapFlag, "-M12M", "-hT", "-RTS"}) {
		t.Errorf("override: got %v", got)
	}
}
