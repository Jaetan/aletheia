# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The determinism gate's wide net: a time or thread word its catalogue does not count.

Each binding's net is put to a word its catalogue does not count, which must be a
site, and to the same word in prose, which must not; C++ puts it to a counted
site too, which the catalogue's rows hold instead.  A row dismisses its word in
its one file or, with no file, in every file of its binding; a row no site needs
fails the tree's run, as a ratchet's stale row does.  The plants here are
fragments, never scripts: the gate reads a test's string that parses and calls or
imports something as the source of a child process.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _processes import CommandWord

from tools._common import RelPath
from tools._determinism_dismissals import Dismissal
from tools._determinism_syntax import GO, PYTHON, RUST, NetWord, SourceText
from tools.check_test_determinism import (
    CLEAN,
    OUT_OF_STEP,
    UNREADABLE,
    NetSite,
    as_dismissal,
    judged,
    main,
    net_report,
    python_child_sources,
    scan_of,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

_REASON = Prose("a reason")


def _words(repo: Path, rel: RelPath, source: SourceText) -> set[NetWord]:
    """Name the net's words in one file's source, read as the path it stands for."""
    return {site.word for site in scan_of(repo, rel, source).sites}


@pytest.mark.parametrize(
    ("rel", "code", "prose", "word"),
    [
        (RelPath(rel), SourceText(code), SourceText(prose), NetWord(word))
        for rel, code, prose, word in (
            ("go/aletheia/x_test.go", "var mu sync.Mutex\n", "// sync.Mutex\n", "sync.Mutex"),
            ("python/tests/test_x.py", "q = queue.Queue\n", "# queue.Queue\n", "queue.Queue"),
            ("cpp/tests/x.cpp", "std::latch done{1};\n", "// std::latch\n", "latch"),
            ("rust/tests/x.rs", "let c = std::sync::mpsc::channel;\n", "// mpsc\n", "mpsc"),
            (
                "go/aletheia/x_test.go",
                "func f() { syscall.ForkExec(p, a, nil) }\n",
                "// syscall.ForkExec\n",
                "syscall.ForkExec",
            ),
            ("python/tests/fuzz/fuzz_x.py", "run = os.system\n", "# os.system\n", "os.system"),
            ("cpp/tests/x.cpp", "void f() { vfork(); }\n", "// vfork()\n", "vfork("),
            ("cpp/tests/x.cpp", "void f() { time(&t); }\n", "// time()\n", "time("),
            ("rust/tests/x.rs", "let f = libc::fork;\n", "// libc::fork\n", "libc::fork"),
        )
    ],
    ids=["go", "python", "cpp", "rust", "go-fork", "python-system", "vfork", "time", "libc"],
)
def test_a_word_the_catalogue_does_not_count_is_a_net_site_and_its_prose_is_not(
    tmp_path: Path, rel: RelPath, code: SourceText, prose: SourceText, word: NetWord
) -> None:
    """Each binding's net finds its word in code and never in a comment."""
    assert _words(tmp_path, rel, code) == {word}
    assert not _words(tmp_path, rel, prose)
    assert not _words(tmp_path, RelPath("docs/x.md"), code)


@pytest.mark.parametrize(
    ("rel", "code", "words"),
    [
        (
            RelPath("python/tests/fuzz/fuzz_x.py"),
            SourceText("a = os.posix_spawn\nb = os.posix_spawnp\nc = os.spawnv\nd = os.popen\n"),
            {NetWord(w) for w in ("os.posix_spawn", "os.posix_spawnp", "os.spawnv", "os.popen")},
        ),
        (
            RelPath("rust/tests/x.rs"),
            SourceText("let a = (libc::vfork, libc::posix_spawnp, libc::system, libc::popen);\n"),
            {
                NetWord(w)
                for w in ("libc::vfork", "libc::posix_spawnp", "libc::system", "libc::popen")
            },
        ),
        (
            RelPath("go/aletheia/x_test.go"),
            SourceText("func f() { syscall.StartProcess(p, a, nil) }\n"),
            {NetWord("syscall.StartProcess")},
        ),
    ],
    ids=["python-starts", "rust-starts", "go-start"],
)
def test_every_process_start_spelling_is_a_net_site(
    tmp_path: Path, rel: RelPath, code: SourceText, words: set[NetWord]
) -> None:
    """Each binding's net reads each way its tests could spell a process start."""
    assert _words(tmp_path, rel, code) == words


def test_a_date_or_a_memory_cap_is_a_value_and_a_clock_reader_is_a_site(tmp_path: Path) -> None:
    """A date, a duration or the address-space cap names no clock; a clock reader named does."""
    rel = RelPath("python/tests/test_x.py")
    values = "start = datetime.date\nspan = datetime.timedelta\ncap = resource.RLIMIT_AS\n"
    assert not _words(tmp_path, rel, SourceText(values))
    readers = (
        "clock = datetime.datetime.now\nday = date.today\nstamp = datetime.utcnow\n"
        + "limit = resource.setrlimit\ncpu = resource.RLIMIT_CPU\n"
    )
    assert _words(tmp_path, rel, SourceText(readers)) == {
        NetWord(word)
        for word in (
            "datetime.datetime.now",
            "date.today",
            "datetime.utcnow",
            "resource.setrlimit",
            "resource.RLIMIT_CPU",
        )
    }


def test_a_counted_site_is_the_catalogue_s_and_a_spaced_word_is_one_word(tmp_path: Path) -> None:
    """A net word inside a catalogue site is no net site; whitespace inside a word is dropped."""
    rel = RelPath("cpp/tests/x.cpp")
    scan = scan_of(tmp_path, rel, SourceText("void f() { std::this_thread::sleep_for(d); }\n"))
    assert scan.rows
    assert not scan.sites
    go = RelPath("go/aletheia/x_test.go")
    assert _words(tmp_path, go, SourceText("func f() {\n\tselect {\n\t}\n}\n")) == {
        NetWord("select{")
    }


def test_a_word_beside_a_counted_site_is_still_a_net_site(tmp_path: Path) -> None:
    """Only a word overlapping a site is the catalogue's; one ending or starting at it is not."""
    rel = RelPath("cpp/tests/x.cpp")
    scan = scan_of(tmp_path, rel, SourceText("void f() { cv.wait(sleep_for(poll(d))); }\n"))
    assert scan.rows
    assert {site.word for site in scan.sites} == {NetWord("wait("), NetWord("poll(")}


def test_a_file_s_net_sites_come_in_word_order(tmp_path: Path) -> None:
    """The report's order is the words' order, never the order a set happened to keep."""
    words = ("semaphore", "promise", "latch", "future", "condition_variable", "barrier")
    source = "".join(f"std::{word} v{n};\n" for n, word in enumerate(words))
    sites = scan_of(tmp_path, RelPath("cpp/tests/x.cpp"), SourceText(source)).sites
    assert [site.word for site in sites] == sorted(NetWord(word) for word in words)


def test_a_row_dismisses_its_word_in_its_file_or_with_no_file_in_every_file() -> None:
    """A row naming a file covers it alone, one naming none every file, and a file's row first."""
    here, there = RelPath("go/aletheia/a_test.go"), RelPath("go/aletheia/b_test.go")
    word = NetWord("sync.Mutex")
    sites = [NetSite(here, GO, word), NetSite(there, GO, word)]
    assert judged(sites, {Dismissal(GO, word, here): _REASON}) == ([sites[1]], [])
    assert judged(sites, {Dismissal(GO, word, None): _REASON}) == ([], [])
    elsewhere = Dismissal(RUST, word, None)
    assert judged(sites, {elsewhere: _REASON}) == (sites, [elsewhere])
    both = {Dismissal(GO, word, here): _REASON, Dismissal(GO, word, None): _REASON}
    assert judged(sites[:1], both) == ([], [Dismissal(GO, word, None)])
    assert judged(sites, both) == ([], [])
    later, earlier = Dismissal(RUST, NetWord("mpsc"), None), Dismissal(GO, word, None)
    assert judged([], {later: _REASON, earlier: _REASON}) == ([], [earlier, later])


# Every word the runtime guard holds: the subprocess entries, and the forks.
_GUARDED_STARTS = [
    NetWord(word)
    for word in (
        "Popen subprocess.Popen subprocess.call subprocess.check_call subprocess.check_output"
        + " subprocess.getoutput subprocess.getstatusoutput subprocess.run os.fork os.forkpty"
        + " os.system os.popen os.posix_spawn os.posix_spawnp os.spawnv os.spawnlpe"
        + " asyncio.create_subprocess_exec asyncio.create_subprocess_shell"
        + " loop.subprocess_exec loop.subprocess_shell"
    ).split()
]


@pytest.mark.parametrize("start", _GUARDED_STARTS)
def test_a_process_start_in_a_suite_test_is_the_runtime_guard_s(start: NetWord) -> None:
    """Under python/tests/ the guard holds a process start; a fuzz harness and the root do not."""
    suite = NetSite(RelPath("python/tests/test_x.py"), PYTHON, start)
    fuzz = NetSite(RelPath("python/tests/fuzz/fuzz_x.py"), PYTHON, start)
    root = NetSite(RelPath("conftest.py"), PYTHON, start)
    assert judged([suite, fuzz, root], {}) == ([fuzz, root], [])


@pytest.mark.parametrize(
    "word",
    [NetWord(word) for word in ("subprocess.PIPE", "os.forkserver", "os.spawn", "asyncio.run")],
)
def test_a_word_that_starts_no_process_is_not_the_guard_s(word: NetWord) -> None:
    """A word beside the starts, or a start's prefix, is a row's to dismiss, not the guard's."""
    site = NetSite(RelPath("python/tests/test_x.py"), PYTHON, word)
    assert judged([site], {}) == ([site], [])


def test_the_report_refuses_an_undismissed_word_and_over_the_tree_an_unused_row(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A word no row dismisses fails always; a row no site uses fails the tree's run alone."""
    printed: list[Prose] = []

    def _emit(line: Prose) -> None:
        printed.append(line)

    monkeypatch.setattr("tools.check_test_determinism.emit", _emit)
    site = NetSite(RelPath("go/aletheia/a_test.go"), GO, NetWord("sync.Mutex"))
    unused = {Dismissal(GO, NetWord("sync.Once"), None): _REASON}
    assert net_report([site], {}, whole=False) == OUT_OF_STEP
    assert as_dismissal(site) in printed
    assert net_report([], unused, whole=True) == OUT_OF_STEP
    assert any("go 'sync.Once'" in line for line in printed)
    assert net_report([], unused, whole=False) == CLEAN
    twice = [site, site._replace(file=RelPath("go/aletheia/b_test.go"))]
    assert net_report(twice, {Dismissal(GO, site.word, None): _REASON}, whole=True) == CLEAN
    assert printed[-1].startswith("net sites the catalogue does not count: 2 of 1 words")


def test_the_row_to_paste_names_the_binding_the_word_and_the_file() -> None:
    """The printed row is the table's own spelling of a dismissal in the site's file."""
    site = NetSite(RelPath("rust/tests/x.rs"), RUST, NetWord("mpsc"))
    assert as_dismissal(site) == (
        "    Dismissal(RUST, NetWord('mpsc'), RelPath('rust/tests/x.rs')):"
        + ' Prose("<why it reads no physical time and starts nothing, or why the claim'
        + ' needs the process it starts>"),'
    )


def _plant(root: Path, files: Mapping[RelPath, SourceText]) -> list[RelPath]:
    """Write each file under ``root`` and name them all, as git would list them."""
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / rel).write_text(text, encoding="utf-8")
    return list(files)


def test_main_holds_the_tree_and_a_file_under_edit_to_the_dismissals(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The tree's run refuses an undismissed word and an unused row; one file only its words."""
    tracked = _plant(
        tmp_path,
        {
            RelPath(rel): SourceText(text)
            for rel, text in (
                ("docs/TEST_DETERMINISM.yaml", "sites: []\n"),
                (
                    "rust/.cargo/config.toml",
                    '[env]\nRUST_TEST_THREADS = { value = "1", force = true }\n',
                ),
                ("go/aletheia/a_test.go", "var mu sync.Mutex\n"),
            )
        },
    )

    def _top() -> Path:
        return tmp_path

    def _tracked(_repo: Path) -> list[RelPath]:
        return tracked

    monkeypatch.setattr("tools.check_test_determinism.git_toplevel", _top)
    monkeypatch.setattr("tools.check_test_determinism.git_ls_files", _tracked)

    def _run(dismissals: Mapping[Dismissal, Prose], *arguments: CommandWord) -> ExitStatus:
        monkeypatch.setattr("tools.check_test_determinism.DISMISSED", dismissals)
        monkeypatch.setattr(sys, "argv", [CommandWord("check_test_determinism"), *arguments])
        return main()

    row = Dismissal(GO, NetWord("sync.Mutex"), None)
    spare = {row: _REASON, Dismissal(GO, NetWord("sync.Once"), None): _REASON}
    assert _run({}) == OUT_OF_STEP
    assert _run({row: _REASON}) == CLEAN
    assert _run(spare) == OUT_OF_STEP
    edited = tmp_path / "edited.go"
    _ = edited.write_text("var mu sync.Mutex\n", encoding="utf-8")
    under_edit = tuple(map(CommandWord, ("--file", str(edited), "--as", "go/aletheia/a_test.go")))
    assert _run(spare, *under_edit) == CLEAN
    assert _run({}, *under_edit) == OUT_OF_STEP
    _ = (tmp_path / tracked[-1]).write_bytes(b"package x\n\xff\xfe\n")
    assert _run({row: _REASON}) == UNREADABLE


def test_no_plant_here_is_a_script() -> None:
    """The gate would read a plant that parses and calls or imports as a child's source."""
    own = Path(__file__).read_text(encoding="utf-8")
    assert not python_child_sources(SourceText(own))
