# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Delete the Actions cache entries no run can restore or would be given.

The platform keeps a repository's cache under a size ceiling and, at the
ceiling, evicts whatever was read longest ago.  Two kinds of entry fill it
without ever being read again, and this tool deletes those and nothing else:

* An entry saved by a pull request's run lives on that request's merge ref,
  which only that request's own runs can restore.  Once the request is closed,
  merged or not, nothing can read it.  A request reopened later restores from
  the default branch's entries, as a fresh request does.
* An entry saved on the default branch under a key that ends in the commit it
  was saved at is reached by later runs through a prefix match, which yields the
  newest entry under the prefix.  Every older entry under that prefix is passed
  over; a few of the newest are kept so that deleting a bad newest entry by hand
  leaves a run something to fall back on, and the rest go.  A key with no commit
  suffix is a toolchain cache, keyed by content, and is kept whatever its age.

An entry whose request state cannot be read is kept.  Nothing is deleted
unless ``--apply`` is given: the default is to print what would go.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime
from typing import NamedTuple

DEFAULT_REF = "refs/heads/main"
KEEP_NEWEST = 2
LIST_LIMIT = 1000
_PULL_REF = re.compile(r"^refs/pull/(\d+)/merge$")
_COMMIT_SUFFIX = re.compile(r"-[0-9a-f]{40}$")


class Entry(NamedTuple):
    """One cache entry as ``gh cache list`` reports it."""

    id: int
    key: str
    ref: str
    size: int
    created: str

    @property
    def created_at(self) -> datetime:
        """When the entry was saved, for ordering entries under one prefix."""
        return datetime.fromisoformat(self.created)


class Plan(NamedTuple):
    """The entries to delete, each with the reason, and the entries left alone."""

    delete: list[tuple[Entry, str]]
    keep: list[Entry]


def pull_number(ref: str) -> int | None:
    """Return the pull request a merge ref belongs to, or ``None`` for any other ref."""
    match = _PULL_REF.match(ref)
    return int(match.group(1)) if match else None


def key_prefix(key: str) -> str | None:
    """Return the key with its trailing commit removed, or ``None`` when it carries none."""
    if not _COMMIT_SUFFIX.search(key):
        return None
    return _COMMIT_SUFFIX.sub("", key)


def plan(
    entries: list[Entry],
    *,
    open_pulls: set[int],
    unknown_pulls: set[int],
    default_ref: str = DEFAULT_REF,
    keep_newest: int = KEEP_NEWEST,
) -> Plan:
    """Decide each entry's fate under the two rules above.

    ``open_pulls`` are the requests still open, ``unknown_pulls`` the ones whose
    state could not be read; an entry of either is kept.
    """
    delete: list[tuple[Entry, str]] = []
    keep: list[Entry] = []
    by_prefix: dict[str, list[Entry]] = {}
    for entry in entries:
        number = pull_number(entry.ref)
        if number is not None:
            if number in open_pulls or number in unknown_pulls:
                keep.append(entry)
            else:
                delete.append((entry, f"pull request {number} is closed"))
            continue
        prefix = key_prefix(entry.key) if entry.ref == default_ref else None
        if prefix is None:
            keep.append(entry)
            continue
        by_prefix.setdefault(prefix, []).append(entry)
    for prefix, group in by_prefix.items():
        group.sort(key=lambda entry: entry.created_at, reverse=True)
        keep.extend(group[:keep_newest])
        delete.extend((entry, f"superseded under {prefix}") for entry in group[keep_newest:])
    return Plan(delete, keep)


def gh(args: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the GitHub CLI, which reads the token and the repository from its environment."""
    executable = shutil.which("gh")
    if executable is None:
        msg = "gh is not on PATH"
        raise RuntimeError(msg)
    return subprocess.run([executable, *args], capture_output=True, text=True, check=False)


def list_entries(ref: str | None) -> list[Entry]:
    """Every entry the repository holds, or every entry on one ref."""
    args = [
        "cache",
        "list",
        "--limit",
        str(LIST_LIMIT),
        "--json",
        "id,key,ref,sizeInBytes,createdAt",
    ]
    if ref is not None:
        args += ["--ref", ref]
    proc = gh(args)
    if proc.returncode != 0:
        msg = f"gh cache list failed (exit {proc.returncode}): {proc.stderr.strip()}"
        raise RuntimeError(msg)
    rows = json.loads(proc.stdout)
    return [
        Entry(
            int(row["id"]),
            str(row["key"]),
            str(row["ref"]),
            int(row["sizeInBytes"]),
            str(row["createdAt"]),
        )
        for row in rows
    ]


def pull_states(numbers: set[int]) -> tuple[set[int], set[int]]:
    """Split the requests into the open ones and the ones whose state did not read."""
    open_pulls: set[int] = set()
    unknown: set[int] = set()
    for number in sorted(numbers):
        proc = gh(["pr", "view", str(number), "--json", "state", "--jq", ".state"])
        state = proc.stdout.strip()
        if proc.returncode != 0 or not state:
            unknown.add(number)
        elif state == "OPEN":
            open_pulls.add(number)
    return open_pulls, unknown


def delete_entries(planned: list[tuple[Entry, str]]) -> int:
    """Delete each planned entry, returning how many deletions failed."""
    failed = 0
    for entry, _reason in planned:
        proc = gh(["cache", "delete", str(entry.id)])
        if proc.returncode != 0:
            failed += 1
            _ = sys.stderr.write(
                f"delete failed for {entry.id} ({entry.key}): {proc.stderr.strip()}\n"
            )
    return failed


def _mib(size: int) -> str:
    return f"{size / 2**20:8.1f} MiB"


def report(entries: list[Entry], planned: Plan, *, apply: bool) -> None:
    """One line per deletion, then the totals."""
    verb = "delete" if apply else "would delete"
    for entry, reason in planned.delete:
        _ = sys.stdout.write(f"{verb} {_mib(entry.size)}  {entry.ref}  {entry.key}  ({reason})\n")
    held = sum(entry.size for entry in entries)
    freed = sum(entry.size for entry, _reason in planned.delete)
    before = f"{len(entries)} entries holding {_mib(held).strip()}"
    going = f"{verb} {len(planned.delete)} holding {_mib(freed).strip()}"
    after = f"leaving {len(planned.keep)} holding {_mib(held - freed).strip()}"
    _ = sys.stdout.write(f"{before}; {going}, {after}\n")


def main(argv: list[str] | None = None) -> int:
    """Plan the prune from the live listing, print it, and apply it when asked."""
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    _ = parser.add_argument(
        "--apply", action="store_true", help="delete; without it, only print what would go"
    )
    _ = parser.add_argument(
        "--ref",
        help="prune every entry on this ref: the event naming it says its run is over",
    )
    _ = parser.add_argument(
        "--default-ref",
        default=DEFAULT_REF,
        help=f"the default branch's ref (default {DEFAULT_REF})",
    )
    _ = parser.add_argument(
        "--keep-newest",
        type=int,
        default=KEEP_NEWEST,
        help=f"entries kept under each commit-suffixed prefix on main (default {KEEP_NEWEST})",
    )
    args = parser.parse_args(argv)
    apply = bool(args.apply)
    ref = str(args.ref) if args.ref else None

    try:
        entries = list_entries(ref)
    except (RuntimeError, ValueError) as exc:
        _ = sys.stderr.write(f"{exc}\n")
        return 2
    if ref is not None:
        planned = Plan([(entry, f"the run on {ref} is over") for entry in entries], [])
    else:
        numbers = {number for entry in entries if (number := pull_number(entry.ref)) is not None}
        open_pulls, unknown = pull_states(numbers)
        for number in sorted(unknown):
            _ = sys.stderr.write(f"pull request {number}: state unread, its entries are kept\n")
        planned = plan(
            entries,
            open_pulls=open_pulls,
            unknown_pulls=unknown,
            default_ref=str(args.default_ref),
            keep_newest=int(args.keep_newest),
        )
    report(entries, planned, apply=apply)
    if not apply:
        return 0
    return 1 if delete_entries(planned.delete) else 0


if __name__ == "__main__":
    sys.exit(main())
