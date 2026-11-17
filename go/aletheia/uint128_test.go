// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"math"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// A signed value reads as an int64 up to each edge of that range and is
// refused one past it: 2^63-1 and -2^63 are read, 2^63 and -(2^63+1) are
// not, and neither is a magnitude past 2^64-1 on either side.
func TestSignMagnitude_Int64ReadsToEachEdge(t *testing.T) {
	cases := map[string]struct {
		s    aletheia.SignMagnitude
		want int64
		ok   bool
	}{
		"zero":      {aletheia.SignMagnitude{}, 0, true},
		"minus one": {aletheia.SignMagnitude{Negative: true, Magnitude: aletheia.Uint128{Lo: 1}}, -1, true},
		"2^63-1":    {aletheia.SignMagnitude{Magnitude: aletheia.Uint128{Lo: math.MaxInt64}}, math.MaxInt64, true},
		"2^63":      {aletheia.SignMagnitude{Magnitude: aletheia.Uint128{Lo: 1 << 63}}, 0, false},
		"-2^63":     {aletheia.SignMagnitude{Negative: true, Magnitude: aletheia.Uint128{Lo: 1 << 63}}, math.MinInt64, true},
		"-(2^63+1)": {aletheia.SignMagnitude{Negative: true, Magnitude: aletheia.Uint128{Lo: 1<<63 + 1}}, 0, false},
		"2^64":      {aletheia.SignMagnitude{Magnitude: aletheia.Uint128{Hi: 1}}, 0, false},
		"-2^64":     {aletheia.SignMagnitude{Negative: true, Magnitude: aletheia.Uint128{Hi: 1}}, 0, false},
	}
	for name, tc := range cases {
		if got, ok := tc.s.Int64(); got != tc.want || ok != tc.ok {
			t.Errorf("%s: Int64() = %d, %v; want %d, %v", name, got, ok, tc.want, tc.ok)
		}
	}
}
