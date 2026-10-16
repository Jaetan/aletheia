//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

/*
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

// Runs when the program is loaded, before the Go runtime, which opens
// /dev/null read-write on a closed descriptor 1, where a report would then be
// written to nothing. stdout reopened read-only on /dev/null takes descriptor 1
// first, and every write to it fails with EBADF, as on the closed descriptor.
__attribute__((constructor)) static void aletheia_hold_stdout(void) {
	struct stat status;
	if (fstat(STDOUT_FILENO, &status) == 0 || errno != EBADF)
		return;
	if (freopen("/dev/null", "r", stdout) == NULL)
		return;
}
*/
import "C"

import (
	"errors"
	"syscall"
)

// systemMessage is the C library's text for the errno err carries, the text
// the C++ and Python CLIs print, or err's own text where it carries none.
func systemMessage(err error) string {
	var errno syscall.Errno
	if errors.As(err, &errno) {
		return C.GoString(C.strerror(C.int(errno)))
	}
	return err.Error()
}
