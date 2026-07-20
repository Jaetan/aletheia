// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Cross-binding wire-code vocabulary parity — Go side.
//
// Reads docs/WIRE_CODES.yaml (the cross-binding SSOT, itself anchored to the
// Agda kernel by the `check-wire-codes` run_ci gate) and asserts the Go
// vocabulary surfaces are each an exact mirror of their YAML section —
// reciprocal set equality, so a missing member AND a stale member both fail:
//
//	issue_codes <-> the Issue* [aletheia.IssueCode] constants (result.go)
//	error_codes <-> the Code* error-code string constants (error.go)
//
// Go has no constant reflection, so the two slices below enumerate the
// constants explicitly. The slices cannot rot silently: removing a constant
// breaks compilation (the slice names it), a slice entry with no YAML row
// fails the Go→YAML direction, and a constant added together with its YAML
// row (the SSOT addition protocol) but not listed here fails the YAML→Go
// direction. IssueUnknown is deliberately absent: it is the binding-local
// default for a MISSING code (json.go parseIssueArray), not a kernel wire
// code — pinned by its own test below. The runtime decode path deliberately
// passes unknown non-empty codes through verbatim (forward compatibility)
// and is not touched by this test.
//
// Mirrors python/tests/test_wire_codes_parity.py,
// cpp/tests/test_wire_codes_parity.cpp, and rust/tests/wire_codes.rs, with
// the same YAML-loading mechanics as log_events_test.go.

package aletheia_test

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"gopkg.in/yaml.v3"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ----- YAML schema -----

type wireCodeRow struct {
	Name        string `yaml:"name"`
	Description string `yaml:"description"`
}

type wireCodeDoc struct {
	IssueCodes []wireCodeRow `yaml:"issue_codes"`
	ErrorCodes []wireCodeRow `yaml:"error_codes"`
}

func loadWireCodes(t *testing.T) wireCodeDoc {
	t.Helper()
	// Resolve docs/WIRE_CODES.yaml relative to this source file (go/aletheia/).
	_, here, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("runtime.Caller(0) failed")
	}
	yamlPath := filepath.Join(filepath.Dir(here), "..", "..", "docs", "WIRE_CODES.yaml")
	data, err := os.ReadFile(yamlPath)
	if err != nil {
		t.Fatalf("read %s: %v", yamlPath, err)
	}
	var doc wireCodeDoc
	if err := yaml.Unmarshal(data, &doc); err != nil {
		t.Fatalf("unmarshal %s: %v", yamlPath, err)
	}
	if len(doc.IssueCodes) == 0 || len(doc.ErrorCodes) == 0 {
		t.Fatalf("%s: empty issue_codes or error_codes section", yamlPath)
	}
	return doc
}

// yamlNameSet collects one section's names, failing on empties or duplicates.
func yamlNameSet(t *testing.T, section string, rows []wireCodeRow) map[string]struct{} {
	t.Helper()
	names := make(map[string]struct{}, len(rows))
	for i, row := range rows {
		if row.Name == "" {
			t.Fatalf("%s[%d]: empty name", section, i)
		}
		if _, dup := names[row.Name]; dup {
			t.Fatalf("%s[%d]: duplicate name %q", section, i, row.Name)
		}
		names[row.Name] = struct{}{}
	}
	return names
}

// ----- Go vocabulary surfaces -----

// Every Issue* constant — the closed Go issue-code vocabulary (result.go).
var goIssueCodes = []aletheia.IssueCode{
	aletheia.IssueDuplicateMessageID,
	aletheia.IssueDuplicateMessageName,
	aletheia.IssueDuplicateSignalName,
	aletheia.IssueFactorZero,
	aletheia.IssueMultiplexorNotFound,
	aletheia.IssueMultiplexorCycle,
	aletheia.IssueGlobalNameCollision,
	aletheia.IssueMinExceedsMax,
	aletheia.IssueSignalExceedsDLC,
	aletheia.IssueSignalOverlap,
	aletheia.IssueBitLengthZero,
	aletheia.IssueOffsetScaleRange,
	aletheia.IssueEmptyMessage,
	aletheia.IssueStartBitOutOfRange,
	aletheia.IssueBitLengthExcessive,
	aletheia.IssueMultiplexorNonUnitScaling,
	aletheia.IssueDuplicateAttributeName,
	aletheia.IssueUnknownCommentTarget,
	aletheia.IssueUnknownMessageSender,
	aletheia.IssueUnknownSignalReceiver,
	aletheia.IssueUnknownValueDescriptionTarget,
	aletheia.IssueTextRoundtripDivergence,
	aletheia.IssueMultiValueMuxSelector,
	aletheia.IssueMuxMasterIncoherent,
	aletheia.IssueUnknownAttributeName,
	aletheia.IssueAttributeValueTypeMismatch,
	aletheia.IssueAttributeEnumEmpty,
	aletheia.IssueAttributeEnumDefaultUnstable,
}

// Every Code* constant — the closed Go error-code vocabulary (error.go).
var goErrorCodes = []string{
	aletheia.CodeParseMissingField,
	aletheia.CodeParseInvalidByteOrder,
	aletheia.CodeParseInvalidPresence,
	aletheia.CodeParseMissingSigned,
	aletheia.CodeParseInvalidSigned,
	aletheia.CodeParseNotAnObject,
	aletheia.CodeParseExtCanIDOutOfRange,
	aletheia.CodeParseStdCanIDOutOfRange,
	aletheia.CodeParseDefaultCanIDOutOfRange,
	aletheia.CodeParseInvalidDLCBytes,
	aletheia.CodeParseRootNotObject,
	aletheia.CodeParseMissingSignalName,
	aletheia.CodeParseSignalBitLengthZero,
	aletheia.CodeParseSignalStartBitExceedsFrame,
	aletheia.CodeParseSignalBitLengthExceedsFrame,
	aletheia.CodeParseSignalBigEndianOverflow,
	aletheia.CodeParseInvalidKind,
	aletheia.CodeParseNonTerminatingRational,
	aletheia.CodeParseInvalidIdentifier,
	aletheia.CodeParseNonIntegerMultiplexValue,
	aletheia.CodeParseNonNaturalField,
	aletheia.CodeDBCTextParseFailure,
	aletheia.CodeDBCTextTrailingInput,
	aletheia.CodeDBCTextAttributeRefinementFailed,
	aletheia.CodeFrameSignalNotFound,
	aletheia.CodeFrameSignalIndexOOB,
	aletheia.CodeFrameInjectionFailed,
	aletheia.CodeFrameSignalsOverlap,
	aletheia.CodeFrameCanIDNotFound,
	aletheia.CodeFrameCanIDMismatch,
	aletheia.CodeFrameSignalValueOutOfBounds,
	aletheia.CodeInputBoundExceeded,
	aletheia.CodeRouteMissingField,
	aletheia.CodeRouteMissingArray,
	aletheia.CodeRouteUnknownCommand,
	aletheia.CodeRouteMissingCommandField,
	aletheia.CodeRouteDLCExceedsMax,
	aletheia.CodeRouteByteArrayParseFailed,
	aletheia.CodeRouteByteCountMismatch,
	aletheia.CodeRouteMissingDBCField,
	aletheia.CodeRouteMissingPropsField,
	aletheia.CodeHandlerNoDBC,
	aletheia.CodeHandlerAlreadyStreaming,
	aletheia.CodeHandlerNotStreaming,
	aletheia.CodeHandlerStreamNotStarted,
	aletheia.CodeHandlerStreamActive,
	aletheia.CodeHandlerPropertyParseFailed,
	aletheia.CodeHandlerInvalidDLCCode,
	aletheia.CodeHandlerValidationFailed,
	aletheia.CodeHandlerTextRoundtripFailed,
	aletheia.CodeHandlerNonMonotonicTimestamp,
	aletheia.CodeDispatchMissingTypeField,
	aletheia.CodeDispatchUnknownMessageType,
	aletheia.CodeDispatchInvalidJSON,
	aletheia.CodeDispatchRequestNotObject,
	aletheia.CodeExtractionMuxValueMismatch,
	aletheia.CodeExtractionMuxSignalNotFound,
	aletheia.CodeExtractionMuxChainCycle,
	aletheia.CodeExtractionMuxExtractionFailed,
	aletheia.CodeExtractionBitExtractionFailed,
}

// ----- 1. YAML schema sanity -----

func TestWireCodesYAMLSchema(t *testing.T) {
	doc := loadWireCodes(t)
	for section, rows := range map[string][]wireCodeRow{
		"issue_codes": doc.IssueCodes,
		"error_codes": doc.ErrorCodes,
	} {
		yamlNameSet(t, section, rows) // non-empty + unique names
		for i, row := range rows {
			if row.Description == "" {
				t.Errorf("%s[%d] (%s): missing description", section, i, row.Name)
			}
		}
	}
}

// ----- 2. reciprocal set equality, both vocabularies -----

func TestWireCodesIssueCodesMatchGoConstants(t *testing.T) {
	doc := loadWireCodes(t)
	yamlNames := yamlNameSet(t, "issue_codes", doc.IssueCodes)

	goNames := make(map[string]struct{}, len(goIssueCodes))
	for _, c := range goIssueCodes {
		if _, dup := goNames[string(c)]; dup {
			t.Fatalf("goIssueCodes lists %q twice", c)
		}
		goNames[string(c)] = struct{}{}
	}

	for name := range yamlNames {
		if _, ok := goNames[name]; !ok {
			t.Errorf("issue code %q is in docs/WIRE_CODES.yaml but Go has no "+
				"Issue* constant for it (or the constant is missing from "+
				"goIssueCodes above)", name)
		}
	}
	for name := range goNames {
		if _, ok := yamlNames[name]; !ok {
			t.Errorf("Issue* constant %q has no docs/WIRE_CODES.yaml row — "+
				"stale Go constant or missing SSOT row", name)
		}
	}
}

func TestWireCodesErrorCodesMatchGoConstants(t *testing.T) {
	doc := loadWireCodes(t)
	yamlNames := yamlNameSet(t, "error_codes", doc.ErrorCodes)

	goNames := make(map[string]struct{}, len(goErrorCodes))
	for _, c := range goErrorCodes {
		if _, dup := goNames[c]; dup {
			t.Fatalf("goErrorCodes lists %q twice", c)
		}
		goNames[c] = struct{}{}
	}

	for name := range yamlNames {
		if _, ok := goNames[name]; !ok {
			t.Errorf("error code %q is in docs/WIRE_CODES.yaml but Go has no "+
				"Code* constant for it (or the constant is missing from "+
				"goErrorCodes above)", name)
		}
	}
	for name := range goNames {
		if _, ok := yamlNames[name]; !ok {
			t.Errorf("Code* constant %q has no docs/WIRE_CODES.yaml row — "+
				"stale Go constant or missing SSOT row", name)
		}
	}
}

// ----- 3. sentinel canary -----

// IssueUnknown is the Go binding's default for a MISSING code on the wire,
// not a kernel wire code: the kernel never emits "unknown", so the SSOT must
// never list it (mirrors the C++/Rust Unknown sentinels, likewise excluded).
func TestWireCodesIssueUnknownIsNotAWireCode(t *testing.T) {
	doc := loadWireCodes(t)
	yamlNames := yamlNameSet(t, "issue_codes", doc.IssueCodes)
	if _, ok := yamlNames[string(aletheia.IssueUnknown)]; ok {
		t.Fatalf("docs/WIRE_CODES.yaml issue_codes contains %q — the "+
			"binding-local missing-code default must not become a canonical "+
			"wire code", aletheia.IssueUnknown)
	}
}
