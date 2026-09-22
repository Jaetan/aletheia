# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The cache prune deletes what no run can restore or would be given, and nothing else.

``tools/prune_actions_cache.py`` decides each entry's fate from its ref and its
key.  The rules are few and each has a side a wrong reading would cross: a
closed request's entries go and an open one's stay, an unreadable state keeps,
the newest entries under a commit-suffixed prefix on the default branch stay
and the rest go, a key without a commit suffix stays whatever its age, and no
other ref is touched.  Each side is pinned here, and so is the default of
deleting nothing.
"""

from __future__ import annotations

import json
import subprocess
from typing import TYPE_CHECKING, NamedTuple

from tools import prune_actions_cache as prune
from tools.prune_actions_cache import Entry

if TYPE_CHECKING:
    import pytest

_SHA_A = "a" * 40
_SHA_B = "b" * 40
_SHA_C = "c" * 40
_PREFIX = "ccache-mutation-cpp-plain-1-clang23-v1"
_MAIN = prune.DEFAULT_REF


def _entry(
    ident: int,
    key: str,
    ref: str = _MAIN,
    *,
    size: int = 1,
    created: str = "2026-09-22T00:00:00Z",
) -> Entry:
    return Entry(ident, key, ref, size, created)


def _fates(planned: prune.Plan) -> tuple[set[int], set[int]]:
    return {entry.id for entry, _reason in planned.delete}, {entry.id for entry in planned.keep}


def test_a_closed_pull_requests_entries_go_and_an_open_ones_stay() -> None:
    """The ref names the request that saved the entry; its state says whether it still reads it."""
    entries = [
        _entry(1, "any-key", "refs/pull/10/merge"),
        _entry(2, "any-key", "refs/pull/11/merge"),
    ]
    deleted, kept = _fates(prune.plan(entries, open_pulls={11}, unknown_pulls=set()))
    assert deleted == {1}
    assert kept == {2}


def test_an_entry_of_a_request_whose_state_did_not_read_is_kept() -> None:
    """An unread state is not a closed one."""
    entries = [_entry(1, "any-key", "refs/pull/10/merge")]
    deleted, kept = _fates(prune.plan(entries, open_pulls=set(), unknown_pulls={10}))
    assert deleted == set()
    assert kept == {1}


def test_the_newest_entries_under_a_prefix_on_the_default_branch_stay_and_the_rest_go() -> None:
    """A prefix match yields the newest entry, so older ones are never chosen; a few stay."""
    entries = [
        _entry(1, f"{_PREFIX}-{_SHA_A}", created="2026-09-20T00:00:00Z"),
        _entry(2, f"{_PREFIX}-{_SHA_B}", created="2026-09-21T00:00:00Z"),
        _entry(3, f"{_PREFIX}-{_SHA_C}", created="2026-09-22T00:00:00Z"),
    ]
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=2)
    )
    assert deleted == {1}
    assert kept == {2, 3}
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=1)
    )
    assert deleted == {1, 2}
    assert kept == {3}


def test_the_order_is_by_creation_time_and_not_by_listing_order() -> None:
    """The listing's order is the platform's; the rule reads the timestamp."""
    entries = [
        _entry(1, f"{_PREFIX}-{_SHA_A}", created="2026-09-22T00:00:00Z"),
        _entry(2, f"{_PREFIX}-{_SHA_B}", created="2026-09-20T00:00:00Z"),
    ]
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=1)
    )
    assert deleted == {2}
    assert kept == {1}


def test_a_key_without_a_commit_suffix_is_kept_whatever_its_age() -> None:
    """A toolchain cache is keyed by content and read for as long as the content stands."""
    entries = [
        _entry(1, "clang23-llvm23dev-libstdcxx15-noble-v1", created="2026-01-01T00:00:00Z"),
        _entry(2, "mull23-noble-" + "f" * 64, created="2026-01-01T00:00:00Z"),
        _entry(3, "cabal-Linux-ghc9.8.4-agda2.8.0-v2", created="2026-01-01T00:00:00Z"),
    ]
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=1)
    )
    assert deleted == set()
    assert kept == {1, 2, 3}


def test_a_commit_suffixed_key_on_another_branch_is_not_a_candidate() -> None:
    """The prefix rule is the default branch's; a branch of its own is left alone."""
    entries = [
        _entry(1, f"{_PREFIX}-{_SHA_A}", "refs/heads/topic", created="2026-09-20T00:00:00Z"),
        _entry(2, f"{_PREFIX}-{_SHA_B}", "refs/heads/topic", created="2026-09-21T00:00:00Z"),
    ]
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=1)
    )
    assert deleted == set()
    assert kept == {1, 2}


def test_prefixes_are_counted_apart() -> None:
    """Two lanes' keys share everything but the lane, and each keeps its own newest."""
    other = _PREFIX.replace("plain-1", "plain-2")
    entries = [
        _entry(1, f"{_PREFIX}-{_SHA_A}", created="2026-09-20T00:00:00Z"),
        _entry(2, f"{other}-{_SHA_A}", created="2026-09-20T00:00:00Z"),
        _entry(3, f"{_PREFIX}-{_SHA_B}", created="2026-09-21T00:00:00Z"),
    ]
    deleted, kept = _fates(
        prune.plan(entries, open_pulls=set(), unknown_pulls=set(), keep_newest=1)
    )
    assert deleted == {1}
    assert kept == {2, 3}


def test_pull_number_and_key_prefix_read_only_their_own_shapes() -> None:
    """A ref that is no merge ref has no number; a key with no commit suffix has no prefix."""
    assert prune.pull_number("refs/pull/287/merge") == 287
    assert prune.pull_number("refs/heads/main") is None
    assert prune.pull_number("refs/pull/287/head") is None
    assert prune.key_prefix(f"{_PREFIX}-{_SHA_A}") == _PREFIX
    assert prune.key_prefix(f"{_PREFIX}-{'a' * 39}") is None
    assert prune.key_prefix("mull23-noble-" + "f" * 64) is None


class _Calls(NamedTuple):
    """Every call the CLI stand-in took, and the ids it was told to delete."""

    made: list[list[str]]
    deleted: list[str]


def _install_gh(
    monkeypatch: pytest.MonkeyPatch,
    listing: list[dict[str, object]],
    states: dict[str, str],
) -> _Calls:
    """Stand in for the CLI: answer a listing and request states, record every delete."""
    calls = _Calls([], [])

    def fake(args: list[str]) -> subprocess.CompletedProcess[str]:
        calls.made.append(args)
        if args[:2] == ["cache", "list"]:
            return subprocess.CompletedProcess(args, 0, json.dumps(listing), "")
        if args[:2] == ["pr", "view"]:
            state = states.get(args[2])
            if state is None:
                return subprocess.CompletedProcess(args, 1, "", "no pull request found")
            return subprocess.CompletedProcess(args, 0, state + "\n", "")
        if args[:2] == ["cache", "delete"]:
            calls.deleted.append(args[2])
            return subprocess.CompletedProcess(args, 0, "", "")
        msg = f"unexpected gh call: {args}"
        raise AssertionError(msg)

    monkeypatch.setattr(prune, "gh", fake)
    return calls


def _row(
    ident: int, key: str, ref: str, created: str = "2026-09-22T00:00:00Z"
) -> dict[str, object]:
    return {"id": ident, "key": key, "ref": ref, "sizeInBytes": 1, "createdAt": created}


def test_without_apply_nothing_is_deleted(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """The default is the plan, printed; the deletions wait for the flag."""
    calls = _install_gh(monkeypatch, [_row(1, "k", "refs/pull/10/merge")], {"10": "MERGED"})
    assert prune.main([]) == 0
    assert calls.deleted == []
    out = capsys.readouterr().out
    assert "would delete" in out
    assert "refs/pull/10/merge" in out


def test_with_apply_the_planned_entries_are_deleted_and_the_kept_ones_are_not(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Merged and closed requests both go; the open one and the unread one stay."""
    calls = _install_gh(
        monkeypatch,
        [
            _row(1, "k", "refs/pull/10/merge"),
            _row(2, "k", "refs/pull/11/merge"),
            _row(3, "k", "refs/pull/12/merge"),
            _row(4, "k", "refs/pull/13/merge"),
        ],
        {"10": "MERGED", "11": "CLOSED", "12": "OPEN"},
    )
    assert prune.main(["--apply"]) == 0
    assert calls.deleted == ["1", "2"]


def test_a_ref_given_on_the_command_line_is_pruned_whole_without_a_state_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The event that named the ref is the evidence its run is over."""
    rows = [_row(1, "k", "refs/pull/10/merge"), _row(2, "k2", "refs/pull/10/merge")]
    calls = _install_gh(monkeypatch, rows, {})
    assert prune.main(["--apply", "--ref", "refs/pull/10/merge"]) == 0
    assert calls.deleted == ["1", "2"]
    listing = next(call for call in calls.made if call[:2] == ["cache", "list"])
    assert listing[-2:] == ["--ref", "refs/pull/10/merge"]
    assert not any(call[:2] == ["pr", "view"] for call in calls.made)


def test_a_failed_deletion_is_the_exit_status(monkeypatch: pytest.MonkeyPatch) -> None:
    """A prune that could not delete what it planned says so to the caller."""
    _ = _install_gh(monkeypatch, [_row(1, "k", "refs/pull/10/merge")], {"10": "MERGED"})
    answering = prune.gh

    def failing(args: list[str]) -> subprocess.CompletedProcess[str]:
        if args[:2] == ["cache", "delete"]:
            return subprocess.CompletedProcess(args, 1, "", "denied")
        return answering(args)

    monkeypatch.setattr(prune, "gh", failing)
    assert prune.main(["--apply"]) == 1


def test_a_listing_that_fails_is_a_usage_exit_and_deletes_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """No listing, no plan."""
    calls = _install_gh(monkeypatch, [], {})
    answering = prune.gh

    def broken(args: list[str]) -> subprocess.CompletedProcess[str]:
        if args[:2] == ["cache", "list"]:
            return subprocess.CompletedProcess(args, 1, "", "HTTP 403")
        return answering(args)

    monkeypatch.setattr(prune, "gh", broken)
    assert prune.main(["--apply"]) == 2
    assert calls.deleted == []
