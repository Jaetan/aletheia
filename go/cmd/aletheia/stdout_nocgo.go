//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

// systemMessage is err's own text: without cgo there is no C library to ask,
// and nothing runs before the Go runtime to hold a closed descriptor 1, which
// the runtime opens on /dev/null; see the cgo half of this pair.
func systemMessage(err error) string {
	return err.Error()
}
