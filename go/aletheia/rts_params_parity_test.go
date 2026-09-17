// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The runtime values this binding mirrors are the ones docs/RESOURCE_BUDGETS.yaml
// declares, and the argument vector is built from them in the order that
// document fixes. The test sits inside the package so that it reads the
// constants themselves, which are unexported here as they are in every other
// binding. Nothing here loads the library.
package aletheia

import (
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
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

// loadRTSBudget reads the document, found from this source file rather than
// from the working directory.
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

// Every value the binding mirrors is the document's.
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

// The vector carries the cap whatever the core count, names a core count only
// when one was asked for, and puts the environment's flags last, where a cap
// among them replaces the one before it.
func TestRTSInitArgv(t *testing.T) {
	cases := map[string]struct {
		cores    int
		override string
		want     []string
	}{
		"one core": {
			1, "", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-RTS"},
		},
		"four cores": {
			4, "", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-N4", "-RTS"},
		},
		"the environment adds flags": {
			1, "  -M12M   -hT ", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-M12M", "-hT", "-RTS"},
		},
		"and adds them beside a core count": {
			2, "-hT", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-N2", "-hT", "-RTS"},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			t.Setenv(rtsOverrideEnv, tc.override)
			if got := rtsInitArgv(tc.cores); !slices.Equal(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

// The document's own two spellings of the cap agree: the flag the runtime
// takes and the byte count the document states beside it. Nothing else reads
// that count, so without this they could drift apart and the document would
// say two things.
func TestRTSHeapCapFlagMatchesItsByteCount(t *testing.T) {
	doc := loadRTSBudget(t)
	flag := doc.Runtime.HeapCap.Flag
	if !strings.HasPrefix(flag, "-M") {
		t.Fatalf("the cap flag is %q, which is not a heap cap", flag)
	}
	body := flag[len("-M"):]
	units := map[byte]int64{'K': 1 << 10, 'M': 1 << 20, 'G': 1 << 30}
	scale := int64(1)
	if len(body) > 0 {
		if u, ok := units[body[len(body)-1]]; ok {
			scale = u
			body = body[:len(body)-1]
		}
	}
	n, err := strconv.ParseInt(body, 10, 64)
	if err != nil {
		t.Fatalf("the cap flag %q carries no number: %v", flag, err)
	}
	if got := n * scale; got != doc.Runtime.HeapCap.Bytes {
		t.Errorf("the flag %q is %d bytes and the document says %d", flag, got, doc.Runtime.HeapCap.Bytes)
	}
}
