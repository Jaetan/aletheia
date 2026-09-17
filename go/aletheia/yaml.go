// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"os"
	"path/filepath"

	"gopkg.in/yaml.v3"
)

// LoadChecksFromYAML loads checks from a path or from YAML text. A source
// naming a file is read; anything else is the document itself.
func LoadChecksFromYAML(source string) ([]CheckResult, error) {
	data, err := loadYAMLData(source)
	if err != nil {
		return nil, err
	}
	return parseYAMLChecks(data)
}

// LoadChecksFromYAMLFile loads checks from a file, which must be a real file
// under the size cap. A path is never resolved for the caller: a symbolic link
// is refused, as the C++ and Python loaders refuse one, so that what is read is
// the path that was given.
func LoadChecksFromYAMLFile(path string) ([]CheckResult, error) {
	data, err := readYAMLFile(filepath.Clean(path), true)
	if err != nil {
		return nil, err
	}
	return parseYAMLChecks(data)
}

// symlinkRefusal is the refusal both entry points answer with, so that a
// caller sees one message whichever way it arrived.
func symlinkRefusal(path string) error {
	return validationError(fmt.Sprintf(
		"YAML file is a symbolic link; refusing to load: %s. Resolve the link and pass the real path.", path))
}

// readYAMLFile reads a path, holding it to being a real file no larger than
// the text cap and refusing a symbolic link. With mustExist false, a path that
// is not a file at all comes back as no data and no error, which is how the
// caller that also takes inline text knows to treat the string as the
// document.
func readYAMLFile(path string, mustExist bool) ([]byte, error) {
	info, err := os.Lstat(path)
	if err != nil {
		if !mustExist {
			return nil, nil
		}
		if os.IsNotExist(err) {
			return nil, validationError(fmt.Sprintf("YAML file not found: %s", path))
		}
		return nil, wrapValidationError("stat YAML file", err)
	}
	if info.Mode()&os.ModeSymlink != 0 {
		return nil, symlinkRefusal(path)
	}
	if !info.Mode().IsRegular() {
		if !mustExist {
			return nil, nil
		}
		return nil, validationError(fmt.Sprintf("YAML path is not a regular file: %s", path))
	}
	if size := uint64(info.Size()); size > MaxDBCTextBytes {
		return nil, newInputBoundExceededError(BoundKindInputLengthBytes, size, MaxDBCTextBytes, CodeInputBoundExceeded)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, wrapValidationError("reading YAML file", err)
	}
	return data, nil
}

// loadYAMLData is the document a source names: the contents of the file, when
// it is one, and otherwise the source itself. Both forms are held to the text
// cap, and a symbolic link is refused rather than followed.
func loadYAMLData(source string) ([]byte, error) {
	source = filepath.Clean(source)
	data, err := readYAMLFile(source, false)
	if err != nil {
		return nil, err
	}
	if data != nil {
		return data, nil
	}
	if size := uint64(len(source)); size > MaxDBCTextBytes {
		return nil, newInputBoundExceededError(BoundKindInputLengthBytes, size, MaxDBCTextBytes, CodeInputBoundExceeded)
	}
	return []byte(source), nil
}

type yamlFile struct {
	Checks []yamlCheck `yaml:"checks"`
}

// yamlScalar keeps a number as the text it was written as, so that the kernel
// parses it exactly: a field of floating type would have rounded a tenth
// before this code ever saw it. A nil one means the key was absent, the
// decoder calling this only for a value that is there.
type yamlScalar struct {
	text string
}

// UnmarshalYAML keeps the text as written, refusing a list or a mapping where
// a number belongs. Whether the text is a number the kernel decides later.
func (s *yamlScalar) UnmarshalYAML(node *yaml.Node) error {
	if node.Kind != yaml.ScalarNode {
		return validationError("expected a numeric scalar value")
	}
	s.text = node.Value
	return nil
}

type yamlCheck struct {
	Name      string      `yaml:"name"`
	Signal    string      `yaml:"signal"`
	Condition string      `yaml:"condition"`
	Value     *yamlScalar `yaml:"value"`
	Min       *yamlScalar `yaml:"min"`
	Max       *yamlScalar `yaml:"max"`
	WithinMs  *int64      `yaml:"within_ms"`
	Severity  string      `yaml:"severity"`
	When      *yamlClause `yaml:"when"`
	Then      *yamlClause `yaml:"then"`
}

type yamlClause struct {
	Signal    string      `yaml:"signal"`
	Condition string      `yaml:"condition"`
	Value     *yamlScalar `yaml:"value"`
	Min       *yamlScalar `yaml:"min"`
	Max       *yamlScalar `yaml:"max"`
}

// nodeRational is the exact value of a written number, parsed by the kernel.
// Loading a document with numbers therefore needs the runtime up, and a number
// the kernel refuses comes back with the kernel's own reason, as it does in the
// Rust binding.
func nodeRational(s *yamlScalar) (Rational, error) {
	return FromDecimal(s.text)
}

// parseYAMLChecks is the checks a document carries. It is decoded twice, once
// loosely and once into the types: the typed decode alone reads a missing key,
// a key with nothing under it and an empty list as the same empty answer, and
// reports a key of the wrong type as the decoder's own message rather than as
// what is wrong with the document.
func parseYAMLChecks(data []byte) ([]CheckResult, error) {
	// The loose pass, which tells an absent key from one of the wrong type.
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

	// The typed pass.
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

// parseYAMLCheck builds one check, by the shape it was written in, and puts
// the optional name and severity on it.
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

// yamlSimpleValues answers for the keys a check written as one signal and one
// condition is spelled with, refusing in this loader's own words.
type yamlSimpleValues struct {
	name  string
	entry yamlCheck
}

func (v yamlSimpleValues) requires(what string) error {
	return validationError(fmt.Sprintf("check '%s': condition '%s' requires %s", v.name, v.entry.Condition, what))
}

func (v yamlSimpleValues) Value() (Rational, error) {
	if v.entry.Value == nil {
		return Rational{}, v.requires("'value'")
	}
	return nodeRational(v.entry.Value)
}

func (v yamlSimpleValues) Range() (Rational, Rational, error) {
	if v.entry.Min == nil || v.entry.Max == nil {
		return Rational{}, Rational{}, v.requires("'min' and 'max'")
	}
	lo, err := nodeRational(v.entry.Min)
	if err != nil {
		return Rational{}, Rational{}, err
	}
	hi, err := nodeRational(v.entry.Max)
	if err != nil {
		return Rational{}, Rational{}, err
	}
	return lo, hi, nil
}

func (v yamlSimpleValues) Within() (int64, error) {
	if v.entry.WithinMs == nil {
		return 0, v.requires("'within_ms'")
	}
	return *v.entry.WithinMs, nil
}

// parseYAMLSimple builds a check written as one signal and one condition. The
// word is held to the vocabulary here, before the dispatcher holds it again,
// so that the refusal names the check.
func parseYAMLSimple(entry yamlCheck) (CheckResult, error) {
	name := checkName(entry.Name)
	if !IsSimpleCondition(entry.Condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown condition '%s'", name, entry.Condition))
	}
	return DispatchSimple(entry.Signal, entry.Condition, yamlSimpleValues{name: name, entry: entry})
}

// yamlThenValues answers for the keys an obligation is spelled with.
type yamlThenValues struct {
	name   string
	clause *yamlClause
}

func (v yamlThenValues) requires(what string) error {
	return validationError(fmt.Sprintf("check '%s': then condition '%s' requires %s", v.name, v.clause.Condition, what))
}

func (v yamlThenValues) Value() (Rational, error) {
	if v.clause.Value == nil {
		return Rational{}, v.requires("'value'")
	}
	return nodeRational(v.clause.Value)
}

func (v yamlThenValues) Range() (Rational, Rational, error) {
	if v.clause.Min == nil || v.clause.Max == nil {
		return Rational{}, Rational{}, v.requires("'min' and 'max'")
	}
	lo, err := nodeRational(v.clause.Min)
	if err != nil {
		return Rational{}, Rational{}, err
	}
	hi, err := nodeRational(v.clause.Max)
	if err != nil {
		return Rational{}, Rational{}, err
	}
	return lo, hi, nil
}

// parseYAMLWhenThen builds a check written as a trigger and an obligation,
// which must be met inside a stated time.
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

	// The trigger, whose three conditions all read one value.
	if !IsWhenCondition(when.Condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown when condition '%s'", name, when.Condition))
	}
	if when.Value == nil {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': when condition '%s' requires 'value'", name, when.Condition))
	}

	whenValue, err := nodeRational(when.Value)
	if err != nil {
		return CheckResult{}, err
	}
	whenResult, err := DispatchWhen(CheckWhen(when.Signal), when.Condition, whenValue)
	if err != nil {
		return CheckResult{}, err
	}

	// The obligation, its word held here for the same reason as above.
	if !IsThenCondition(then.Condition) {
		return CheckResult{}, validationError(fmt.Sprintf("check '%s': unknown then condition '%s'", name, then.Condition))
	}
	return DispatchThen(whenResult.Then(then.Signal), then.Condition,
		yamlThenValues{name: name, clause: then}, *entry.WithinMs)
}
