//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

/*
#include "aletheia_abi.h"
*/
import "C"

// wireUint128 lays a magnitude out as the two words the entries read.
func wireUint128(u Uint128) C.struct_aletheia_uint128 {
	return C.struct_aletheia_uint128{lo: C.uint64_t(u.Lo), hi: C.uint64_t(u.Hi)}
}

// uint128Of reads the two words an entry wrote.
func uint128Of(w C.struct_aletheia_uint128) Uint128 {
	return Uint128{Hi: uint64(w.hi), Lo: uint64(w.lo)}
}

// wireRational lays a rational out as the structure the entries read, its
// sign a byte the library reads as negative when it is not 0.
func wireRational(r Rational) C.struct_aletheia_rational {
	var negative C.uint8_t
	if r.Negative {
		negative = 1
	}
	return C.struct_aletheia_rational{
		numerator:   wireUint128(r.Numerator),
		denominator: wireUint128(r.Denominator),
		negative:    negative,
	}
}

// rationalOf reads the rational an entry wrote, which the library writes with
// a positive denominator and a zero unsigned.
func rationalOf(w C.struct_aletheia_rational) Rational {
	return Rational{
		Negative:    w.negative != 0,
		Numerator:   uint128Of(w.numerator),
		Denominator: uint128Of(w.denominator),
	}
}
