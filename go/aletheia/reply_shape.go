// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"fmt"
	"strings"
	"unicode/utf16"
)

// The refusal every reply reader returns for a place holding what the kernel
// never writes there reads "reply <path>: expected <what>, got <what came>",
// the same text in the four bindings. The path is the reply proof's: the keys from the reply's root joined by
// "/", an array's entries keeping the array's path, the whole reply's path
// empty ("reply: expected object, got array"). What is expected and what came
// are JSON kinds, "string", "boolean", "number", "array", "object" or "null",
// and a key the reply lacks came as "nothing". A rational place expects "a
// rational": a number, or the {numerator, denominator} object the kernel
// writes a fraction as. A place holding one of a set of words expects them
// quoted, one holding a code expects "an issue code" or "an error code", and
// a string outside them came quoted. A whole-number place expects
// a "number" written as digits, all the kernel writes there.
//
// A reader narrows each place itself and builds its refusal here: came names
// what a key held, cameAs what a value is, cameWord what a word place held.

// replyPath is a place in a reply: its keys from the root joined by "/",
// empty for the whole reply.
type replyPath string

// at names the place of key in the object at p.
func (p replyPath) at(key string) replyPath {
	if p == "" {
		return replyPath(key)
	}
	return p + "/" + replyPath(key)
}

// What a place holds: a JSON kind, a rational, a code, or its words quoted.
const (
	expectString    = "string"
	expectBoolean   = "boolean"
	expectNumber    = "number"
	expectArray     = "array"
	expectObject    = "object"
	expectRational  = "a rational"
	expectIssueCode = "an issue code"
	expectErrorCode = "an error code"
)

// cameNothing is what came at a key the reply lacks.
const cameNothing = "nothing"

// jsonKind names the JSON kind of a value parseResponse decoded, which reads
// every number as a json.Number.
func jsonKind(v any) string {
	switch v.(type) {
	case nil:
		return "null"
	case bool:
		return "boolean"
	case json.Number:
		return "number"
	case string:
		return "string"
	case []any:
		return "array"
	case map[string]any:
		return "object"
	default:
		// No decoded JSON value is of another type; a reader handed one
		// names it rather than a kind it is not.
		return fmt.Sprintf("%T", v)
	}
}

// cameAs names what came at a place: the JSON kind of its value.
func cameAs(v any) string { return jsonKind(v) }

// came names what key held in obj: its value's JSON kind, or nothing.
func came(obj map[string]any, key string) string {
	v, ok := obj[key]
	if !ok {
		return cameNothing
	}
	return jsonKind(v)
}

// cameWord names what a word place held: its string quoted, another value's
// kind, or nothing.
func cameWord(obj map[string]any, key string) string {
	if s, ok := obj[key].(string); ok {
		return quoteJSON(s)
	}
	return came(obj, key)
}

// words names a word place's words quoted: "a", "a" or "b", "a", "b" or "c".
func words(expected ...string) string {
	quoted := make([]string, len(expected))
	for i, w := range expected {
		quoted[i] = quoteJSON(w)
	}
	if len(quoted) == 1 {
		return quoted[0]
	}
	return strings.Join(quoted[:len(quoted)-1], ", ") + " or " + quoted[len(quoted)-1]
}

// quoteJSON writes s as a JSON string with every character past ASCII
// escaped, the quoting the other bindings print a word in, so a string
// outside a place's words reads alike in all four.
func quoteJSON(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch {
		case r == '"':
			b.WriteString(`\"`)
		case r == '\\':
			b.WriteString(`\\`)
		case r == '\n':
			b.WriteString(`\n`)
		case r == '\r':
			b.WriteString(`\r`)
		case r == '\t':
			b.WriteString(`\t`)
		case r == '\b':
			b.WriteString(`\b`)
		case r == '\f':
			b.WriteString(`\f`)
		case r > 0xffff:
			hi, lo := utf16.EncodeRune(r)
			fmt.Fprintf(&b, `\u%04x\u%04x`, hi, lo)
		case r < 0x20 || r >= 0x7f:
			fmt.Fprintf(&b, `\u%04x`, r)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

// replyRefusal is the refusal of a reply place.
func replyRefusal(path replyPath, expected, arrival string) error {
	where := "reply"
	if path != "" {
		where = "reply " + string(path)
	}
	return protocolError(fmt.Sprintf("%s: expected %s, got %s", where, expected, arrival))
}

// wholeNumber reads the digits of a reply's number, an optional minus sign
// then decimal digits, as a sign and a magnitude; false for a number written
// otherwise (a fraction, an exponent) or past 2^128-1.
func wholeNumber(v any) (SignMagnitude, bool) {
	n, ok := v.(json.Number)
	if !ok {
		return SignMagnitude{}, false
	}
	digits, negative := strings.CutPrefix(n.String(), "-")
	magnitude, ok := parseUint128(digits)
	return SignMagnitude{Negative: negative && magnitude != Uint128{}, Magnitude: magnitude}, ok
}

// readSignMagnitude reads the whole number at path, signed.
func readSignMagnitude(v any, path replyPath) (SignMagnitude, error) {
	s, ok := wholeNumber(v)
	if !ok {
		return SignMagnitude{}, replyRefusal(path, expectNumber, cameAs(v))
	}
	return s, nil
}

// readUint128 reads the whole number at a place the kernel proves natural.
func readUint128(v any, path replyPath) (Uint128, error) {
	s, ok := wholeNumber(v)
	if !ok || s.Negative {
		return Uint128{}, replyRefusal(path, expectNumber, cameAs(v))
	}
	return s.Magnitude, nil
}

// readUint64 reads the whole number at a natural place whose proven range a
// uint64 holds; the caller converts it to the place's own type, which holds
// that range too.
func readUint64(v any, path replyPath) (uint64, error) {
	u, err := readUint128(v, path)
	if err != nil {
		return 0, err
	}
	n, ok := u.Uint64()
	if !ok {
		return 0, replyRefusal(path, expectNumber, cameAs(v))
	}
	return n, nil
}

// readInt64 reads the whole number at a place whose proven range an int64
// holds, an attribute's integer value or bound.
func readInt64(v any, path replyPath) (int64, error) {
	s, err := readSignMagnitude(v, path)
	if err != nil {
		return 0, err
	}
	n, ok := s.Int64()
	if !ok {
		return 0, replyRefusal(path, expectNumber, cameAs(v))
	}
	return n, nil
}

// readRational reads the rational at path, a number or its {numerator,
// denominator} object, anything else refused as a rational expected. The
// object's sign is the quotient's, so a negative denominator, which the
// kernel never writes, flips it as the other bindings' readers do; a zero
// denominator, which it never writes either, is read as written.
func readRational(v any, path replyPath) (Rational, error) {
	if whole, ok := wholeNumber(v); ok {
		return Rational{Negative: whole.Negative, Numerator: whole.Magnitude, Denominator: Uint128{Lo: 1}}, nil
	}
	if obj, ok := v.(map[string]any); ok {
		numerator, numOK := wholeNumber(obj["numerator"])
		denominator, denOK := wholeNumber(obj["denominator"])
		if numOK && denOK {
			return Rational{
				Negative:    numerator.Negative != denominator.Negative && numerator.Magnitude != Uint128{},
				Numerator:   numerator.Magnitude,
				Denominator: denominator.Magnitude,
			}, nil
		}
	}
	return Rational{}, replyRefusal(path, expectRational, cameAs(v))
}

// readString reads the string at path.
func readString(v any, path replyPath) (string, error) {
	if s, ok := v.(string); ok {
		return s, nil
	}
	return "", replyRefusal(path, expectString, cameAs(v))
}

// readBool reads the boolean at path.
func readBool(v any, path replyPath) (bool, error) {
	if b, ok := v.(bool); ok {
		return b, nil
	}
	return false, replyRefusal(path, expectBoolean, cameAs(v))
}

// readArray reads the array at path.
func readArray(v any, path replyPath) ([]any, error) {
	if a, ok := v.([]any); ok {
		return a, nil
	}
	return nil, replyRefusal(path, expectArray, cameAs(v))
}

// readObject reads the object at path.
func readObject(v any, path replyPath) (map[string]any, error) {
	if o, ok := v.(map[string]any); ok {
		return o, nil
	}
	return nil, replyRefusal(path, expectObject, cameAs(v))
}

// field reads key of the object at path with read, which names its own
// expectation for a value of the wrong kind; an absent key is refused as
// nothing came, expected being what read expects.
func field[T any](obj map[string]any, path replyPath, key, expected string, read func(any, replyPath) (T, error)) (T, error) {
	v, ok := obj[key]
	if !ok {
		var zero T
		return zero, replyRefusal(path.at(key), expected, cameNothing)
	}
	return read(v, path.at(key))
}

// The fields of each kind, each refusing an absent key as nothing came.

func fieldString(obj map[string]any, path replyPath, key string) (string, error) {
	return field(obj, path, key, expectString, readString)
}

func fieldBool(obj map[string]any, path replyPath, key string) (bool, error) {
	return field(obj, path, key, expectBoolean, readBool)
}

func fieldArray(obj map[string]any, path replyPath, key string) ([]any, error) {
	return field(obj, path, key, expectArray, readArray)
}

func fieldObject(obj map[string]any, path replyPath, key string) (map[string]any, error) {
	return field(obj, path, key, expectObject, readObject)
}

func fieldRational(obj map[string]any, path replyPath, key string) (Rational, error) {
	return field(obj, path, key, expectRational, readRational)
}

func fieldUint64(obj map[string]any, path replyPath, key string) (uint64, error) {
	return field(obj, path, key, expectNumber, readUint64)
}

func fieldUint128(obj map[string]any, path replyPath, key string) (Uint128, error) {
	return field(obj, path, key, expectNumber, readUint128)
}

func fieldInt64(obj map[string]any, path replyPath, key string) (int64, error) {
	return field(obj, path, key, expectNumber, readInt64)
}

func fieldSignMagnitude(obj map[string]any, path replyPath, key string) (SignMagnitude, error) {
	return field(obj, path, key, expectNumber, readSignMagnitude)
}

// fieldObjectOf reads the object at key with read, at the key's place.
func fieldObjectOf[T any](obj map[string]any, path replyPath, key string, read func(map[string]any, replyPath) (T, error)) (T, error) {
	o, err := fieldObject(obj, path, key)
	if err != nil {
		var zero T
		return zero, err
	}
	return read(o, path.at(key))
}

// fieldObjects reads the array at key, each entry an object read with read at
// the array's place; nil for an empty array.
func fieldObjects[T any](obj map[string]any, path replyPath, key string, read func(map[string]any, replyPath) (T, error)) ([]T, error) {
	entries, err := fieldArray(obj, path, key)
	if err != nil {
		return nil, err
	}
	place := path.at(key)
	var out []T
	for _, entry := range entries {
		o, err := readObject(entry, place)
		if err != nil {
			return nil, err
		}
		v, err := read(o, place)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}

// fieldStrings reads the array at key, each entry a string, as the string
// type of its place.
func fieldStrings[T ~string](obj map[string]any, path replyPath, key string) ([]T, error) {
	entries, err := fieldArray(obj, path, key)
	if err != nil {
		return nil, err
	}
	place := path.at(key)
	out := make([]T, 0, len(entries))
	for _, entry := range entries {
		s, err := readString(entry, place)
		if err != nil {
			return nil, err
		}
		out = append(out, T(s))
	}
	return out, nil
}

// fieldWord reads the word at key, one of expected, refusing any other with
// the words quoted.
func fieldWord(obj map[string]any, path replyPath, key string, expected ...string) (string, error) {
	if s, ok := obj[key].(string); ok {
		for _, w := range expected {
			if s == w {
				return w, nil
			}
		}
	}
	return "", replyRefusal(path.at(key), words(expected...), cameWord(obj, key))
}

// fieldMember reads the word at key, a member of members, refusing any other
// as expected, a string outside them quoted as fieldWord quotes it.
func fieldMember[T ~string](obj map[string]any, path replyPath, key, expected string, members map[T]struct{}) (T, error) {
	if s, ok := obj[key].(string); ok {
		if _, member := members[T(s)]; member {
			return T(s), nil
		}
	}
	return "", replyRefusal(path.at(key), expected, cameWord(obj, key))
}

// fieldStatus reads the status at key, one of expected, refusing any other
// with the words quoted as fieldWord does. It is the one reader of a status's
// word, which tools/check_limits_parity.py holds.
func fieldStatus(obj map[string]any, path replyPath, key string, expected ...replyStatus) (replyStatus, error) {
	if s, ok := obj[key].(string); ok {
		for _, w := range expected {
			if s == w.word {
				return w, nil
			}
		}
	}
	spellings := make([]string, len(expected))
	for i, w := range expected {
		spellings[i] = w.word
	}
	var none replyStatus
	return none, replyRefusal(path.at(key), words(spellings...), cameWord(obj, key))
}
