# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_clang_tidy_coverage.py — every cpp/src/**/*.cpp is in the compile DB.

The C++ clang-tidy gate runs ``run-clang-tidy -p build cpp/src/``, which lints
exactly the translation units present in ``compile_commands.json``.  Driving the
lint from the compile database makes the build system the single source of truth
for coverage — so a whole *directory* can no longer be silently dropped the way
a hand-maintained ``src/*.cpp`` glob dropped ``src/detail/``.

But the DB-driven scan has a dual blind spot: a source file that exists on disk
yet is **not** wired into any CMake target never appears in the DB, so
``run-clang-tidy`` silently skips it (and it is silently unbuilt).  This guard
closes that gap — it fails when a ``cpp/src/**/*.cpp`` file is absent from the
compile DB, turning "forgot to add it to CMakeLists.txt" into a CI failure
rather than a quiet hole.

Together the recursive regex (no forgotten directories) and this guard (no
forgotten files) make the C++ lint coverage self-maintaining.

Exit codes:
  0 — every cpp/src/**/*.cpp appears in the compile DB.
  1 — one or more source files are missing from the DB.
  2 — compile_commands.json not found (run ``cmake -B build`` first).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from tools._common import emit, git_toplevel


def uncovered_sources(src_files: set[str], db_files: set[str]) -> list[str]:
    """Return the sorted src files (repo-relative) absent from the compile DB.

    Pure set difference ``src_files - db_files``: only membership of each source
    file in the DB matters.  Extra DB entries (tests, third-party ``_deps``,
    benchmarks) are intentionally ignored — this guard checks *coverage of
    sources*, not the converse.
    """
    return sorted(src_files - db_files)


def _db_relpaths(db: list[dict[str, object]], repo: Path) -> set[str]:
    """Normalize each compile-DB entry's ``file`` to a repo-relative POSIX path."""
    out: set[str] = set()
    for entry in db:
        raw = entry.get("file")
        if not isinstance(raw, str):
            continue
        path = Path(raw)
        if not path.is_absolute():
            directory = entry.get("directory")
            path = Path(directory if isinstance(directory, str) else "") / path
        try:
            out.add(path.resolve().relative_to(repo).as_posix())
        except ValueError:
            continue  # entry outside the repo (shouldn't happen) — ignore
    return out


def main(repo: Path | None = None) -> int:
    """Fail (exit 1) if any cpp/src/**/*.cpp is missing from the build's compile DB.

    ``repo`` defaults to the enclosing git work tree; tests inject a temp tree.
    """
    repo = (repo if repo is not None else git_toplevel()).resolve()
    db_path = repo / "cpp" / "build" / "compile_commands.json"
    if not db_path.is_file():
        emit(f"check-clang-tidy-coverage: {db_path} not found; run 'cmake -B build' first")
        return 2

    db = json.loads(db_path.read_text(encoding="utf-8"))
    db_files = _db_relpaths(db, repo)
    src_files = {
        p.resolve().relative_to(repo).as_posix() for p in (repo / "cpp" / "src").rglob("*.cpp")
    }

    missing = uncovered_sources(src_files, db_files)
    if missing:
        emit("check-clang-tidy-coverage: cpp/src sources missing from compile_commands.json")
        emit("(not wired into a CMake target → silently unbuilt and unlinted):")
        for f in missing:
            emit(f"  {f}")
        return 1

    emit(f"check-clang-tidy-coverage: ok ({len(src_files)} cpp/src sources all in the compile DB)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
