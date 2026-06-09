// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Loader-entry hardening helpers (R20 cluster N — cross-binding parity).
//
// Mirrors the C++ aletheia::detail::validate_loader_path /
// check_file_size_bound / check_xlsx_uncompressed_bound /
// validate_output_parent_dir set in cpp/src/detail/loader_utils.{hpp,cpp},
// and the Python aletheia._loader_utils.reject_symlink_loader_path +
// excel_loader._check_xlsx_uncompressed_bound pair.  See
// AGENTS.md universal rule "Adversarial-input bounds at parser surfaces"
// and feedback_cross_language_parity.md.
package excel

import (
	"archive/zip"
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// validateLoaderPath checks that path exists, is a regular file, and
// is NOT a symbolic link.  Symlink rejection is strict — filepath.EvalSymlinks
// would FOLLOW the link, defeating the check; callers passing legitimate
// symlinks must resolve them up front.  TOCTOU residual: a small race
// exists between Lstat and the eventual excelize.OpenFile / os.Open;
// strict closure requires fd-based plumbing which excelize does not
// expose.  Documented residual risk per the C++ side's matching note.
//
// kind ("excel" / "yaml") is interpolated into error messages so
// operators see which loader rejected the path.  Lowercase per Go's
// standard error-message convention (the C++ / Python sides use
// "Excel" / "YAML"; cross-binding parity is on behaviour + structure,
// not exact error text).
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

// checkFileSizeBound rejects files whose raw byte count exceeds
// MaxDBCTextBytes.  Mirrors Python check_dbc_text_size_bound and
// C++ aletheia::detail::check_file_size_bound — the typed
// *InputBoundExceededError keeps cross-binding error-shape parity.
func checkFileSizeBound(path string) error {
	info, err := os.Stat(path)
	if err != nil {
		return aletheia.WrapValidationError("stat file", err)
	}
	if size := uint64(info.Size()); size > aletheia.MaxDBCTextBytes {
		return &aletheia.InputBoundExceededError{
			BoundKind: aletheia.BoundKindInputLengthBytes,
			Observed:  size,
			Limit:     aletheia.MaxDBCTextBytes,
		}
	}
	return nil
}

// checkXlsxUncompressedBound walks the .xlsx archive's central
// directory and rejects when the sum of uncompressed entry sizes
// exceeds MaxDBCTextBytes — defence against ZIP bombs where a small
// archive (e.g. ~50 KiB) decompresses to multiple GiB of XML and
// exhausts heap inside excelize.
//
// Mirrors C++ aletheia::detail::check_xlsx_uncompressed_bound and
// Python excel_loader._check_xlsx_uncompressed_bound.  Go has it
// easier: archive/zip is stdlib and exposes UncompressedSize64
// directly without manual EOCD walking.
func checkXlsxUncompressedBound(path string) error {
	r, err := zip.OpenReader(path)
	if err != nil {
		return aletheia.NewValidationError(fmt.Sprintf("not a valid .xlsx (ZIP) archive: %s", path))
	}
	defer r.Close()

	var total uint64
	for _, f := range r.File {
		// Saturating add — refuse to silently wrap on a forged entry.
		if f.UncompressedSize64 > aletheia.MaxDBCTextBytes-total {
			return &aletheia.InputBoundExceededError{
				BoundKind: aletheia.BoundKindInputLengthBytes,
				Observed:  aletheia.MaxDBCTextBytes + 1, // any value above the bound — exact total has overflowed
				Limit:     aletheia.MaxDBCTextBytes,
			}
		}
		total += f.UncompressedSize64
		if total > aletheia.MaxDBCTextBytes {
			return &aletheia.InputBoundExceededError{
				BoundKind: aletheia.BoundKindInputLengthBytes,
				Observed:  total,
				Limit:     aletheia.MaxDBCTextBytes,
			}
		}
	}
	return nil
}

// validateOutputParentDir checks that path's parent directory exists.
// Empty parent (cwd-relative) is allowed.  Mirrors C++
// aletheia::detail::validate_output_parent_dir.
func validateOutputParentDir(path string) error {
	parent := filepath.Dir(path)
	if parent == "" || parent == "." {
		return nil
	}
	info, err := os.Stat(parent)
	if err != nil {
		return aletheia.NewValidationError(fmt.Sprintf("parent directory does not exist: %s", parent))
	}
	if !info.IsDir() {
		return aletheia.NewValidationError(fmt.Sprintf("parent path is not a directory: %s", parent))
	}
	return nil
}
