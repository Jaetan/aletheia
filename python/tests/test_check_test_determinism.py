# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The test-determinism scan finds every time and thread primitive, and only in code.

Each binding's catalogue is put to a line that uses the primitive, which the scan
must count, and to the same words in a comment or a string, which it must not:
a scan that read prose would record sites no test holds, and one that missed a
spelling would let a timed wait or a thread back in unrecorded. Rust's tests sit
in ``#[cfg(test)]`` modules inside library sources, so only those blocks are
read there. The report fails in both directions, as a ratchet must.
"""

from __future__ import annotations

import textwrap

from tools._common import RelPath, git_toplevel
from tools._ratchet import CanonicalText, RatchetRows, RowKey
from tools.check_test_determinism import (
    BINDINGS,
    CLEAN,
    OUT_OF_STEP,
    Binding,
    BlankedCode,
    SourceText,
    is_test,
    report,
    rows_of,
    rust_test_modules,
    sites_in,
    which_are_tests,
)

GO, PYTHON, CPP, RUST = BINDINGS


def _labels(binding: Binding, rel: RelPath, source: SourceText) -> set[CanonicalText]:
    """Name the primitives the scan finds in one file's source."""
    return set(sites_in(binding.blank(rel, source), binding.primitives))


def test_go_time_and_goroutines_are_sites_and_their_prose_is_not() -> None:
    """A Go test's timer, deadline, go statement and scheduler yield each count."""
    rel = RelPath("go/aletheia/x_test.go")
    source = SourceText(
        textwrap.dedent(
            """\
            func T() {
                time.Sleep(d)
                ctx, _ := context.WithTimeout(p, d)
                go func() {}()
                go run(x)
                runtime.Gosched()
            }
            """
        )
    )
    assert _labels(GO, rel, source) == {
        "time: a clock or timer from package time",
        "time: a context with a deadline",
        "thread: a go statement",
        "thread: a yield to the scheduler",
    }
    prose = SourceText(
        textwrap.dedent(
            """\
            // time.Sleep(d) and go func() in a comment
            s := "time.After(d) go run(x)"
            """
        )
    )
    assert _labels(GO, rel, prose) == set()


def test_python_time_threads_and_tasks_are_sites_and_their_prose_is_not() -> None:
    """A Python test's sleep, clock, timeout, thread, executor and task each count."""
    rel = RelPath("python/tests/test_x.py")
    source = SourceText(
        textwrap.dedent(
            """\
            time.sleep(1)
            t = time.monotonic()
            await asyncio.sleep(0.5)
            async with asyncio.timeout(2):
                pass
            p.wait(timeout=3)
            threading.Thread(target=f)
            ThreadPoolExecutor()
            await asyncio.to_thread(f)
            asyncio.create_task(c())
            done.wait(5)
            proc.wait(BOUND_SECONDS)
            future.result(15)
            loop.call_later(1, f)
            _thread.start_new_thread(f, ())
            """
        )
    )
    assert _labels(PYTHON, rel, source) == {
        "time: a clock or sleep from module time",
        "time: an asyncio sleep of a duration",
        "time: an asyncio timeout",
        "time: a timeout argument",
        "time: a positional timeout",
        "time: a loop callback after a delay",
        "thread: a thread or timer from module threading",
        "thread: a thread from module _thread",
        "thread: an executor",
        "thread: a coroutine run on a thread",
        "thread: a concurrent asyncio task",
    }
    prose = SourceText(
        textwrap.dedent(
            """\
            # time.sleep(1) threading.Thread done.wait(5)
            msg = "asyncio.create_task(c()) timeout=3 loop.call_later(1, f)"
            """
        )
    )
    assert _labels(PYTHON, rel, prose) == set()
    for alone in ("proc.wait(BOUND_SECONDS)\n", "future.result(15)\n"):
        assert _labels(PYTHON, rel, SourceText(alone)) == {"time: a positional timeout"}


def test_a_python_yield_to_the_loop_is_not_physical_time() -> None:
    """A zero sleep, timeout or wait is a poll, not a clock read; a string join is no wait."""
    source = SourceText(
        textwrap.dedent(
            """\
            await asyncio.sleep(0)
            async with asyncio.timeout(0):
                pass
            f(timeout=None)
            ready.wait(0)
            proc.wait()
            ", ".join(names)
            """
        )
    )
    assert _labels(PYTHON, RelPath("python/tests/test_x.py"), source) == set()


def test_cpp_sleeps_clocks_and_threads_are_sites_and_their_prose_is_not() -> None:
    """A C++ test's sleep, timed wait, clock read and thread each count."""
    rel = RelPath("cpp/tests/x.cpp")
    source = SourceText(
        textwrap.dedent(
            """\
            void f() {
              std::this_thread::sleep_for(d);
              cv.wait_for(lock, d);
              auto t = std::chrono::steady_clock::now();
              std::thread w([] {});
              std::jthread j([] {});
              auto fut = std::async(g);
            }
            """
        )
    )
    assert _labels(CPP, rel, source) == {
        "time: a sleep",
        "time: a wait of a duration",
        "time: a clock read",
        "thread: a std::thread or std::jthread",
        "thread: std::async",
    }
    prose = SourceText(
        textwrap.dedent(
            """\
            // std::thread and sleep_for(d)
            auto s = "std::async(g) steady_clock::now()";
            """
        )
    )
    assert _labels(CPP, rel, prose) == set()
    lock_wait = SourceText("void g() { m.try_lock_until(t); }\n")
    assert _labels(CPP, rel, lock_wait) == {"time: a wait of a duration"}


def test_rust_sites_count_only_inside_test_modules_of_a_library_source() -> None:
    """A spawn in library code is not a test's; one in a ``#[cfg(test)]`` module is."""
    source = SourceText(
        textwrap.dedent(
            """\
            fn worker() { std::thread::spawn(|| {}); }
            #[cfg(test)]
            mod tests {
                #[test]
                fn t() {
                    std::thread::sleep(d);
                    let _ = std::time::Instant::now();
                    std::thread::park_timeout(d);
                    std::thread::yield_now();
                    let s = "{ thread::spawn }";
                }
            }
            fn after() { std::thread::spawn(|| {}); }
            """
        )
    )
    assert _labels(RUST, RelPath("rust/src/lib.rs"), source) == {
        "time: a sleep",
        "time: a clock read",
        "time: a wait of a duration",
        "thread: a yield to the scheduler",
    }
    integration = SourceText("fn t() { std::thread::spawn(|| {}); }\n")
    assert _labels(RUST, RelPath("rust/tests/t.rs"), integration) == {
        "thread: a spawned or scoped thread"
    }


def test_a_test_module_ends_at_its_own_closing_brace() -> None:
    """Braces nested inside the module do not end it early, and code after it is dropped."""
    code = BlankedCode("#[cfg(test)]\nmod t {\n    fn a() { if x { b(); } }\n}\nfn c() {}\n")
    kept = rust_test_modules(code)
    assert "b();" in str(kept)
    assert "fn c" not in str(kept)
    assert len(kept) == len(code)


def test_the_report_refuses_an_unrecorded_site_and_a_stale_row() -> None:
    """A site the record does not allow fails, and so does a row past what the file holds."""
    key = RowKey(RelPath("go/aletheia/x_test.go"), CanonicalText("thread: a go statement"))
    one: RatchetRows = {key: 1}
    two: RatchetRows = {key: 2}
    none: RatchetRows = {}
    assert report(one, one) == CLEAN
    assert report(one, none) == OUT_OF_STEP
    assert report(none, one) == OUT_OF_STEP
    assert report(two, one) == OUT_OF_STEP


def test_one_file_is_held_to_its_own_rows_and_never_called_stale() -> None:
    """The write-time check refuses a site the file's rows do not allow, and only that.

    A file under edit holding fewer sites than its row is the change the record
    follows, and another file's unrecorded site is the tree's run to report.
    """
    rel = RelPath("python/tests/test_x.py")
    other = RowKey(RelPath("python/tests/test_y.py"), CanonicalText("thread: an executor"))
    sleep = RowKey(rel, CanonicalText("time: a clock or sleep from module time"))
    recorded: RatchetRows = {sleep: 2}
    edited = rows_of(rel, SourceText("time.sleep(1)\ntime.sleep(2)\ntime.sleep(3)\n"))
    assert edited == {sleep: 3}
    assert report(edited, recorded, file=rel) == OUT_OF_STEP
    assert report(rows_of(rel, SourceText("x = 1\n")), recorded, file=rel) == CLEAN
    assert report({other: 1}, recorded, file=rel) == CLEAN
    assert not rows_of(RelPath("python/aletheia/types.py"), SourceText("time.sleep(1)\n"))


def test_is_test_asks_every_binding() -> None:
    """A path is a test when any binding counts it one, and no other path is."""
    assert is_test(RelPath("go/aletheia/client_test.go"))
    assert is_test(RelPath("cpp/tests/unit_tests_cancel.cpp"))
    assert is_test(RelPath("rust/src/backend.rs"))
    assert not is_test(RelPath("go/aletheia/client.go"))
    assert not is_test(RelPath("tools/check_test_determinism.py"))


def test_the_hook_is_told_which_paths_are_tests() -> None:
    """A test file, or a directory holding a tracked one, is named; the root and others are not."""
    asked = [
        RelPath("go/aletheia"),
        RelPath("docs"),
        RelPath("go/aletheia/client.go"),
        RelPath("python/tests/test_types_serialization.py"),
        RelPath("."),
    ]
    assert which_are_tests(git_toplevel(), asked) == [
        RelPath("go/aletheia"),
        RelPath("python/tests/test_types_serialization.py"),
    ]


def test_every_test_tree_of_every_binding_is_read() -> None:
    """Each binding recognises its own test files and no other's."""
    assert GO.is_test(RelPath("go/cmd/aletheia/main_test.go"))
    assert not GO.is_test(RelPath("go/aletheia/client.go"))
    assert PYTHON.is_test(RelPath("python/tests/test_x.py"))
    assert PYTHON.is_test(RelPath("conftest.py"))
    assert not PYTHON.is_test(RelPath("python/aletheia/types.py"))
    assert CPP.is_test(RelPath("cpp/tests/unit_tests_cancel.cpp"))
    assert not CPP.is_test(RelPath("cpp/src/client.cpp"))
    assert RUST.is_test(RelPath("rust/tests/async_client.rs"))
    assert RUST.is_test(RelPath("rust/excel/tests/load.rs"))
    assert RUST.is_test(RelPath("rust/src/backend.rs"))
    assert not RUST.is_test(RelPath("rust/examples/demo.rs"))
