// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"reflect"
	"strings"
	"testing"
)

// thenBuilder returns a fresh ThenSignalBuilder for DispatchThen tests.
func thenBuilder() ThenSignalBuilder {
	return CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed")
}

func TestDispatchThenEquals(t *testing.T) {
	got, err := DispatchThen(thenBuilder(), "equals", IntRational(1), Rational{}, Rational{}, 100)
	if err != nil {
		t.Fatalf("DispatchThen(equals) errored: %v", err)
	}
	want, err := thenBuilder().Equals(IntRational(1)).Within(100)
	if err != nil {
		t.Fatalf("direct builder chain errored: %v", err)
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("DispatchThen(equals) = %+v, want %+v", got, want)
	}
}

func TestDispatchThenExceeds(t *testing.T) {
	got, err := DispatchThen(thenBuilder(), "exceeds", IntRational(30), Rational{}, Rational{}, 200)
	if err != nil {
		t.Fatalf("DispatchThen(exceeds) errored: %v", err)
	}
	want, err := thenBuilder().Exceeds(IntRational(30)).Within(200)
	if err != nil {
		t.Fatalf("direct builder chain errored: %v", err)
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("DispatchThen(exceeds) = %+v, want %+v", got, want)
	}
}

func TestDispatchThenStaysBetween(t *testing.T) {
	got, err := DispatchThen(thenBuilder(), "stays_between", Rational{}, IntRational(10), IntRational(90), 300)
	if err != nil {
		t.Fatalf("DispatchThen(stays_between) errored: %v", err)
	}
	want, err := thenBuilder().StaysBetween(IntRational(10), IntRational(90)).Within(300)
	if err != nil {
		t.Fatalf("direct builder chain errored: %v", err)
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("DispatchThen(stays_between) = %+v, want %+v", got, want)
	}
}

func TestDispatchThenUnknownCondition(t *testing.T) {
	_, err := DispatchThen(thenBuilder(), "flickers", IntRational(1), Rational{}, Rational{}, 100)
	if err == nil {
		t.Fatal("DispatchThen with an unknown condition must error")
	}
	if !strings.Contains(err.Error(), "unknown then condition") {
		t.Errorf("error %q does not name the unknown-then-condition cause", err)
	}
}
