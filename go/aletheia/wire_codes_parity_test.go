// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The two code vocabularies this binding carries are the ones
// docs/WIRE_CODES.yaml names, which the orchestrator's own gate anchors to the
// kernel. Each is compared both ways, so a code the document has and the
// binding lacks fails, and so does one the binding has and the document
// dropped.
//
// The constants are listed below by hand, Go offering no way to enumerate
// them: removing one breaks the build here, and a code added to the document
// alone fails the comparison. A code added to the package and to neither is
// what the probe over the source catches, which reads the declarations rather
// than a list.
//
// IssueUnknown is not among them. It is what this binding uses when a wire
// code is missing, not a code the kernel emits, and a test below holds the
// document to never naming it. A code the kernel adds and this binding does
// not know still crosses: the decoder carries it rather than refusing it.
//
// The Python, C++ and Rust suites hold their own vocabularies the same way.

package aletheia_test

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"gopkg.in/yaml.v3"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

type wireCodeRow struct {
	Name        string `yaml:"name"`
	Description string `yaml:"description"`
}

type wireCodeDoc struct {
	IssueCodes []wireCodeRow `yaml:"issue_codes"`
	ErrorCodes []wireCodeRow `yaml:"error_codes"`
}

// loadWireCodes reads the document, found from this source file rather than
// from the working directory.
func loadWireCodes(t *testing.T) wireCodeDoc {
	t.Helper()
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

// goIssueCodes is every issue code the binding declares.
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

// goErrorCodes is every error code the binding declares.
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
	aletheia.CodeExtractionValueExceedsWireRange,
}

// Every row of both sections names a code once and says what it is for.
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

// Each vocabulary and its section name the same codes, in both directions.
func TestWireCodes_MatchTheirSections(t *testing.T) {
	doc := loadWireCodes(t)
	issueNames := make([]string, 0, len(goIssueCodes))
	for _, c := range goIssueCodes {
		issueNames = append(issueNames, string(c))
	}
	cases := map[string]struct {
		rows      []wireCodeRow
		declared  []string
		constants string
	}{
		"issue codes": {doc.IssueCodes, issueNames, "Issue"},
		"error codes": {doc.ErrorCodes, goErrorCodes, "Code"},
	}
	for section, tc := range cases {
		t.Run(section, func(t *testing.T) {
			inDocument := yamlNameSet(t, section, tc.rows)
			declared := make(map[string]struct{}, len(tc.declared))
			for _, name := range tc.declared {
				if _, dup := declared[name]; dup {
					t.Fatalf("the list of %s constants names %q twice", tc.constants, name)
				}
				declared[name] = struct{}{}
			}
			for name := range inDocument {
				if _, ok := declared[name]; !ok {
					t.Errorf("%q is in the document and the binding declares no %s constant for it, "+
						"or the constant is not in the list above", name, tc.constants)
				}
			}
			for name := range declared {
				if _, ok := inDocument[name]; !ok {
					t.Errorf("the binding declares %q and the document has no row for it", name)
				}
			}
		})
	}
}

// The binding's own default for a missing code never becomes a code of the
// wire: the kernel does not emit it, and the C++ and Rust bindings keep their
// equivalents out of the document too.
func TestWireCodesIssueUnknownIsNotAWireCode(t *testing.T) {
	doc := loadWireCodes(t)
	yamlNames := yamlNameSet(t, "issue_codes", doc.IssueCodes)
	if _, ok := yamlNames[string(aletheia.IssueUnknown)]; ok {
		t.Fatalf("the document names %q, which is what this binding uses when the "+
			"wire carries no code", aletheia.IssueUnknown)
	}
}
