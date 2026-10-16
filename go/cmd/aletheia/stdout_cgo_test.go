//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"errors"
	"os"
	"syscall"
	"testing"
)

// TestSystemMessageIsTheCLibraryText: a failed write is named by the C
// library's text for its errno, the words the C++ and Python CLIs print, and
// not by Go's spelling of the error with the file's name before it; an error
// carrying no errno keeps its own text.
func TestSystemMessageIsTheCLibraryText(t *testing.T) {
	for _, c := range []struct {
		errno syscall.Errno
		want  string
	}{
		{syscall.ENOSPC, "No space left on device"},
		{syscall.EPIPE, "Broken pipe"},
		{syscall.EBADF, "Bad file descriptor"},
		{syscall.EFBIG, "File too large"},
	} {
		err := &os.PathError{Op: "write", Path: "/dev/stdout", Err: c.errno}
		if got := systemMessage(err); got != c.want {
			t.Errorf("systemMessage(%v) = %q, want %q", err, got, c.want)
		}
	}
	if got := systemMessage(errors.New("no errno here")); got != "no errno here" {
		t.Errorf("systemMessage of an error with no errno = %q, want its own text", got)
	}
}
