// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"os"
	"path/filepath"

	"gopkg.in/yaml.v3"
)

// LoadChecksFromYAML loads checks from a YAML file path or inline YAML string.
// If source names an existing file, it is read; otherwise it is treated as
// inline YAML content.
func LoadChecksFromYAML(source string) ([]CheckResult, error) {
	data, err := loadYAMLData(source)
	if err != nil {
		return nil, err
	}
	return parseYAMLChecks(data)
}

// LoadChecksFromYAMLFile loads checks from a YAML file.
//
// Returns *InputBoundExceededError if the file is larger than
// MaxDBCTextBytes (64 MiB).  YAML check definitions reference signal
// names from a parsed DBC, so the same input-length cap applies; cf.
// Python aletheia.yaml_loader._check_input_bound and AGENTS.md
// universal rule "Adversarial-input bounds at parser surfaces".
//
// R20 cluster N — also rejects symbolic links outright (cross-binding
// parity with C++ aletheia::detail::validate_loader_path and Python
// aletheia._loader_utils.reject_symlink_loader_path).  Callers passing
// legitimate symlinks must resolve them first.
func LoadChecksFromYAMLFile(path string) ([]CheckResult, error) {
	path = filepath.Clean(path)
	info, err := os.Lstat(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, validationError(fmt.Sprintf("YAML file not found: %s", path))
		}
		return nil, wrapValidationError("stat YAML file", err)
	}
	if info.Mode()&os.ModeSymlink != 0 {
		return nil, validationError(fmt.Sprintf(
			"YAML file is a symbolic link; refusing to load: %s.  Resolve the link and pass the real path.",
			path,
		))
	}
	if !info.Mode().IsRegular() {
		return nil, validationError(fmt.Sprintf("YAML path is not a regular file: %s", path))
	}
	if size := uint64(info.Size()); size > MaxDBCTextBytes {
		return nil, &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  size,
			Limit:     MaxDBCTextBytes,
		}
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, wrapValidationError("reading YAML file", err)
	}
	return parseYAMLChecks(data)
}

// loadYAMLData reads YAML data from either a file path or an inline string.
// If source refers to an existing file, it is read; otherwise it is treated
// as inline YAML content.
//
// Returns *InputBoundExceededError if either form exceeds MaxDBCTextBytes
// (64 MiB).  Mirrors Python aletheia.yaml_loader._check_input_bound per
// AGENTS.md universal rule "Adversarial-input bounds at parser surfaces".
//
// R20 cluster N — when the file branch is taken, also reject symbolic
// links (cross-binding parity with C++/Python).  Inline-content
// branch is unaffected.
func loadYAMLData(source string) ([]byte, error) {
	source = filepath.Clean(source)
	info, statErr := os.Lstat(source)
	if statErr == nil && info.Mode().IsRegular() {
		if size := uint64(info.Size()); size > MaxDBCTextBytes {
			return nil, &InputBoundExceededError{
				BoundKind: BoundKindInputLengthBytes,
				Observed:  size,
				Limit:     MaxDBCTextBytes,
			}
		}
		data, err := os.ReadFile(source)
		if err != nil {
			return nil, wrapValidationError("reading YAML file", err)
		}
		return data, nil
	}
	if statErr == nil && info.Mode()&os.ModeSymlink != 0 {
		// Stat-succeeds + symlink — refuse rather than silently follow.
		// Cross-binding parity with C++ aletheia::detail::validate_loader_path
		// and Python aletheia._loader_utils.reject_symlink_loader_path.
		return nil, validationError(fmt.Sprintf(
			"YAML file is a symbolic link; refusing to load: %s.  Resolve the link and pass the real path.",
			source,
		))
	}
	// Stat-fails or non-regular non-symlink — treat as inline YAML.
	// Not a file -- treat as inline YAML.
	if size := uint64(len(source)); size > MaxDBCTextBytes {
		return nil, &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  size,
			Limit:     MaxDBCTextBytes,
		}
	}
	return []byte(source), nil
}

// ---------------------------------------------------------------------------
// YAML intermediate structs
// ---------------------------------------------------------------------------

type yamlFile struct {
	Checks []yamlCheck `yaml:"checks"`
}

type yamlCheck struct {
	Name      string      `yaml:"name"`
	Signal    string      `yaml:"signal"`
	Condition string      `yaml:"condition"`
	Value     *float64    `yaml:"value"`
	Min       *float64    `yaml:"min"`
	Max       *float64    `yaml:"max"`
	WithinMs  *int64      `yaml:"within_ms"`
	Severity  string      `yaml:"severity"`
	When      *yamlClause `yaml:"when"`
	Then      *yamlClause `yaml:"then"`
}

type yamlClause struct {
	Signal    string   `yaml:"signal"`
	Condition string   `yaml:"condition"`
	Value     *float64 `yaml:"value"`
	Min       *float64 `yaml:"min"`
	Max       *float64 `yaml:"max"`
}

// ---------------------------------------------------------------------------
// Parse logic
// ---------------------------------------------------------------------------

// parseYAMLChecks decodes a YAML document into a list of CheckResults.
// The two-pass decode (untyped map → typed struct) is intentional: yaml.v3's
// typed-only path conflates "key missing" / "key present but empty list" /
// "key present with wrong type" into the same shape, which would surface as
// an opaque "no checks" downstream.  Cost is negligible on the loader path
// (microseconds per workbook); benefit is actionable diagnostics.
func parseYAMLChecks(data []byte) ([]CheckResult, error) {
	// First pass: structural check on the top-level "checks" key so we can
	// distinguish absent / wrong-type from a typed unmarshal failure.
	var raw map[string]any
	if err := yaml.Unmarshal(data, &raw); err != nil {
		return nil, wrapValidationError("invalid YAML", err)
	}

	checksRaw, ok := raw["checks"]
	if !ok {
		return nil, validationError("YAML document must contain a 'checks' list")
	}
	if _, isList := checksRaw.([]any); !isList {
		return nil, validationError("YAML 'checks' field must be a list")
	}

	// Second pass: typed unmarshal.
	var file yamlFile
	if err := yaml.Unmarshal(data, &file); err != nil {
		return nil, wrapValidationError("invalid YAML", err)
	}

	results := make([]CheckResult, 0, len(file.Checks))
	for _, entry := range file.Checks {
		r, err := parseYAMLCheck(entry)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}
	return results, nil
}

// parseYAMLCheck dispatches a single YAML check entry to the
// simple-form or when/then parser, then applies shared metadata
// (name, severity) before returning the CheckResult.
func parseYAMLCheck(entry yamlCheck) (CheckResult, error) {
	var result CheckResult
	var err error

	if entry.When != nil {
		result, err = parseYAMLWhenThen(entry)
	} else if entry.Signal != "" {
		result, err = parseYAMLSimple(entry)
	} else {
		name := checkName(entry.Name)
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': must have 'signal' or 'when'/'then'", name))
	}
	if err != nil {
		return CheckResult{}, err
	}

	result = applyMetadata(result, entry.Name, entry.Severity)
	return result, nil
}

// parseYAMLSimple handles the "simple" YAML shape (signal + condition
// + value/min/max/within_ms fields); see INTERFACES.md for the full
// condition vocabulary.
func parseYAMLSimple(entry yamlCheck) (CheckResult, error) {
	name := checkName(entry.Name)
	condition := entry.Condition

	if !IsSimpleCondition(condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown condition '%s'", name, condition))
	}

	if IsSimpleValueCondition(condition) {
		if entry.Value == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': condition '%s' requires 'value'", name, condition))
		}
		return DispatchSimple(entry.Signal, condition, PhysicalValue(*entry.Value))
	}

	if IsSimpleRangeCondition(condition) {
		if entry.Min == nil || entry.Max == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': condition '%s' requires 'min' and 'max'", name, condition))
		}
		return CheckSignal(entry.Signal).StaysBetween(PhysicalValue(*entry.Min), PhysicalValue(*entry.Max))
	}

	if IsSimpleSettlesCondition(condition) {
		if entry.Min == nil || entry.Max == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': condition 'settles_between' requires 'min' and 'max'", name))
		}
		if entry.WithinMs == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': condition 'settles_between' requires 'within_ms'", name))
		}
		return CheckSignal(entry.Signal).SettlesBetween(
			PhysicalValue(*entry.Min),
			PhysicalValue(*entry.Max),
		).Within(*entry.WithinMs)
	}

	if IsSimpleEqualsCondition(condition) {
		if entry.Value == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': condition 'equals' requires 'value'", name))
		}
		return CheckSignal(entry.Signal).Equals(PhysicalValue(*entry.Value)).Always()
	}

	return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown condition '%s'", name, condition))
}

// parseYAMLWhenThen handles the "when/then" YAML shape (trigger
// predicate + obligation with a bounded response window); delegates to
// the simple parsers for the two sub-conditions.
func parseYAMLWhenThen(entry yamlCheck) (CheckResult, error) {
	name := checkName(entry.Name)

	if entry.Then == nil {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': must have 'signal' or 'when'/'then'", name))
	}
	if entry.WithinMs == nil {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': when/then checks require 'within_ms'", name))
	}

	when := entry.When
	then := entry.Then

	// Validate when clause.
	if !IsWhenCondition(when.Condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown when condition '%s'", name, when.Condition))
	}
	if when.Value == nil {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': when condition '%s' requires 'value'", name, when.Condition))
	}

	whenResult, err := DispatchWhen(CheckWhen(when.Signal), when.Condition, PhysicalValue(*when.Value))
	if err != nil {
		return CheckResult{}, err
	}

	// Validate then clause.
	if !IsThenCondition(then.Condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown then condition '%s'", name, then.Condition))
	}

	thenBuilder := whenResult.Then(then.Signal)

	switch then.Condition {
	case "equals":
		if then.Value == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': then condition 'equals' requires 'value'", name))
		}
		return thenBuilder.Equals(PhysicalValue(*then.Value)).Within(*entry.WithinMs)
	case "exceeds":
		if then.Value == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': then condition 'exceeds' requires 'value'", name))
		}
		return thenBuilder.Exceeds(PhysicalValue(*then.Value)).Within(*entry.WithinMs)
	case "stays_between":
		if then.Min == nil || then.Max == nil {
			return CheckResult{}, validationError(fmt.Sprintf("check '%s': then condition 'stays_between' requires 'min' and 'max'", name))
		}
		return thenBuilder.StaysBetween(
			PhysicalValue(*then.Min),
			PhysicalValue(*then.Max),
		).Within(*entry.WithinMs)
	default:
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown then condition '%s'", name, then.Condition))
	}
}
