// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// What a loader checks before it opens what it was given: that the path is a
// file and not a link to one, that the file is within the text bound, that an
// archive does not expand past it, and that a file about to be written has a
// directory to be written into.
//
// The C++ binding checks the same four in cpp/src/detail/loader_utils.cpp and
// the Python binding the first and the third, in aletheia._loader_utils and
// aletheia.excel_loader. AGENTS.md states the rule they share, under
// adversarial-input bounds at parser surfaces.
package excel

import (
	"archive/zip"
	"errors"
	"fmt"
	"math"
	"os"
	"path/filepath"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

// validateLoaderPath requires the path to name an existing regular file that is
// not a symbolic link. The link check reads the path itself rather than what it
// points at, a caller with a link to follow resolving it first. A path can
// still change between this check and the open that follows, which is a race
// the C++ side records too: closing it needs a descriptor the spreadsheet
// library does not take.
//
// kind names the loader in the refusal, so a reader knows which one refused.
// It is lowercase as a Go error is; the other bindings capitalise theirs, the
// parity being over what is refused rather than over the words.
func validateLoaderPath(path, kind string) error {
	info, err := os.Lstat(path)
	if err != nil {
		if errors.Is(err, os.ErrNotExist) {
			return aletheia.NewValidationError(fmt.Sprintf("%s file not found: %s", kind, path))
		}
		return aletheia.WrapValidationError(fmt.Sprintf("stat %s file", kind), err)
	}
	if info.Mode()&os.ModeSymlink != 0 {
		return aletheia.NewValidationError(fmt.Sprintf(
			"%s file is a symbolic link; refusing to load: %s.  Resolve the link and pass the real path.",
			kind, path,
		))
	}
	if !info.Mode().IsRegular() {
		return aletheia.NewValidationError(fmt.Sprintf(
			"%s path is not a regular file: %s", kind, path,
		))
	}
	return nil
}

// boundExceeded is the refusal all three bounds answer with, typed so that a
// caller reads the limit and what was seen rather than parsing a sentence.
func boundExceeded(observed uint64) error {
	return &aletheia.InputBoundExceededError{
		BoundKind: aletheia.BoundKindInputLengthBytes,
		Observed:  observed,
		Limit:     aletheia.MaxDBCTextBytes,
	}
}

// checkFileSizeBound refuses a file larger than the text bound, as the Python
// binding's check_dbc_text_size_bound and the C++ check_file_size_bound do.
func checkFileSizeBound(path string) error {
	info, err := os.Stat(path)
	if err != nil {
		return aletheia.WrapValidationError("stat file", err)
	}
	if size := uint64(info.Size()); size > aletheia.MaxDBCTextBytes {
		return boundExceeded(size)
	}
	return nil
}

// checkXlsxUncompressedBound refuses an archive whose entries claim, together,
// more than the text bound once expanded. That is what a small archive of
// several gigabytes of repeated bytes does to the spreadsheet library's memory,
// and the sizes are read from the archive's own index rather than by expanding
// anything. The C++ and Python bindings check the same; here the standard
// library hands over each entry's expanded size, so there is no index to walk
// by hand.
func checkXlsxUncompressedBound(path string) error {
	r, err := zip.OpenReader(path)
	if err != nil {
		return aletheia.NewValidationError(fmt.Sprintf("not a valid .xlsx (ZIP) archive: %s", path))
	}
	defer r.Close()

	var total uint64
	for _, f := range r.File {
		// Written as a subtraction from the bound because the addition it
		// stands for can overflow on an entry claiming a forged size. What is
		// reported is the size the entries claim, held at the largest number
		// that can be reported when even that sum wraps.
		if f.UncompressedSize64 > aletheia.MaxDBCTextBytes-total {
			claimed := total + f.UncompressedSize64
			if claimed < total {
				claimed = math.MaxUint64
			}
			return boundExceeded(claimed)
		}
		total += f.UncompressedSize64
	}
	return nil
}

// validateOutputParentDir requires the directory a file is about to be written
// into to exist. A path naming no directory is the working one, which does. The
// C++ binding checks the same.
//
// A failure to look at the directory is not the directory being absent, and is
// not reported as one: a component too long to be a name, a directory that
// cannot be searched, or a descriptor limit reached under load would send a
// reader to create something that is already there. This is the distinction
// validateLoaderPath draws above, keyed the same way.
func validateOutputParentDir(path string) error {
	parent := filepath.Dir(path)
	if parent == "" || parent == "." {
		return nil
	}
	info, err := os.Stat(parent)
	if err != nil {
		if errors.Is(err, os.ErrNotExist) {
			return aletheia.NewValidationError(fmt.Sprintf("parent directory does not exist: %s", parent))
		}
		return aletheia.WrapValidationError("stat parent directory", err)
	}
	if !info.IsDir() {
		return aletheia.NewValidationError(fmt.Sprintf("parent path is not a directory: %s", parent))
	}
	return nil
}
