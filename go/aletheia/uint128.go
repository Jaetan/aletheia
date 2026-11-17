// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"math"
	"math/big"
	"math/bits"
	"strconv"
)

// Uint128 is an unsigned 128-bit integer, the width the kernel's magnitudes
// reach: a rational's numerator and denominator, a multiplex value, a bound
// refusal's observed size and limit. It is a value compared with ==. The
// kernel decides every number, so the binding neither parses one from text
// a caller wrote nor orders two; it reads the kernel's replies and prints.
type Uint128 struct {
	Hi uint64
	Lo uint64
}

// Uint64 is the value as a uint64, and false when it is past 2^64-1.
func (u Uint128) Uint64() (uint64, bool) {
	if u.Hi != 0 {
		return 0, false
	}
	return u.Lo, true
}

// tenPow19 is the largest power of ten a word holds, the base String prints in.
const tenPow19 = 10_000_000_000_000_000_000

// String is the value's decimal digits.
func (u Uint128) String() string {
	if u.Hi == 0 {
		return strconv.FormatUint(u.Lo, 10)
	}
	// The value is q*10^19 + r: the high word divides first and its remainder
	// carries into the low word's division, which bits.Div64 takes whole.
	qHi, rem := u.Hi/tenPow19, u.Hi%tenPow19
	qLo, rem := bits.Div64(rem, u.Lo, tenPow19)
	low := strconv.FormatUint(rem, 10)
	return Uint128{Hi: qHi, Lo: qLo}.String() + zeros[:19-len(low)] + low
}

const zeros = "0000000000000000000"

// parseUint128 reads the decimal digits of a reply's number, false for text
// holding anything but digits and for a value past 2^128-1.
func parseUint128(s string) (Uint128, bool) {
	if s == "" {
		return Uint128{}, false
	}
	var u Uint128
	for i := range len(s) {
		c := s[i]
		if c < '0' || c > '9' {
			return Uint128{}, false
		}
		// u*10 + digit, refused once a carry leaves the high word.
		over, hi := bits.Mul64(u.Hi, 10)
		loCarry, lo := bits.Mul64(u.Lo, 10)
		hi, carry := bits.Add64(hi, loCarry, 0)
		if over != 0 || carry != 0 {
			return Uint128{}, false
		}
		lo, carry = bits.Add64(lo, uint64(c-'0'), 0)
		hi, carry = bits.Add64(hi, 0, carry)
		if carry != 0 {
			return Uint128{}, false
		}
		u = Uint128{Hi: hi, Lo: lo}
	}
	return u, true
}

// bigInt is the value as a math/big integer.
func (u Uint128) bigInt() *big.Int {
	v := new(big.Int).SetUint64(u.Hi)
	return v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(u.Lo))
}

// SignMagnitude is a signed integer as a sign and a 128-bit magnitude, the
// form the kernel writes a value-description key in: its magnitude reaches
// 2^128-1 either side of zero, which no Go integer type holds.
type SignMagnitude struct {
	Negative  bool
	Magnitude Uint128
}

// Int64 is the value as an int64, and false when it lies outside that range.
func (s SignMagnitude) Int64() (int64, bool) {
	m, ok := s.Magnitude.Uint64()
	switch {
	case !ok, !s.Negative && m > math.MaxInt64, s.Negative && m > 1<<63:
		return 0, false
	case s.Negative:
		// The negation is taken in the unsigned word, so -2^63, whose
		// magnitude no int64 holds, comes out exact.
		return int64(-m), true
	default:
		return int64(m), true
	}
}

// String is the value in decimal, led by a minus sign when it is below zero.
// A zero magnitude prints without a sign whatever Negative says.
func (s SignMagnitude) String() string {
	if s.Negative && s.Magnitude != (Uint128{}) {
		return "-" + s.Magnitude.String()
	}
	return s.Magnitude.String()
}
