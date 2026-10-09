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
from typing import TYPE_CHECKING

import pytest

from tools import _determinism_guard
from tools._common import RelPath, git_toplevel
from tools._ratchet import CanonicalText, RatchetRows, RowKey
from tools.check_test_determinism import (
    ASYNC_CLIENT_ON_A_THREAD,
    BINDINGS,
    CLEAN,
    OUT_OF_STEP,
    REPLAYING_PROFILE,
    UNSEEDED_PROPERTY,
    Binding,
    BlankedCode,
    SiteCount,
    SourceText,
    async_clients_on_a_thread,
    blank_python,
    is_test,
    report,
    rows_of,
    rust_test_modules,
    rust_tests_run_alone,
    sites_in,
    spell_python_aliases,
    unseeded_properties,
    which_are_tests,
)

if TYPE_CHECKING:
    from pathlib import Path

GO, PYTHON, CPP, RUST = BINDINGS


def _labels(binding: Binding, rel: RelPath, source: SourceText) -> set[CanonicalText]:
    """Name the primitives the scan finds in one file's source."""
    return set(sites_in(binding.code(rel, source), binding.primitives))


def _counts(binding: Binding, rel: RelPath, source: SourceText) -> dict[CanonicalText, SiteCount]:
    """Count the sites of each primitive the scan finds in one file's source."""
    return dict(sites_in(binding.code(rel, source), binding.primitives))


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


def test_a_parallel_test_and_a_group_s_goroutine_are_go_thread_sites() -> None:
    """A test run beside its siblings, and a goroutine a wait or error group starts, each count."""
    rel = RelPath("go/aletheia/x_test.go")
    source = SourceText(
        textwrap.dedent(
            """\
            func TestX(t *testing.T) {
                t.Parallel()
                b.RunParallel(body)
                wg.Go(func() {})
                g.Go(work)
            }
            """
        )
    )
    assert _counts(GO, rel, source) == {
        "thread: a parallel test": 2,
        "thread: a goroutine started through a group": 2,
    }
    prose = SourceText('// t.Parallel() and wg.Go(f)\ns := "t.Parallel()"\n')
    assert _labels(GO, rel, prose) == set()


def test_a_go_package_imported_under_another_name_is_read_as_the_package() -> None:
    """A renamed or a dot import of a watched package hides no site; a blank one binds none."""
    rel = RelPath("go/aletheia/x_test.go")
    renamed = SourceText(
        textwrap.dedent(
            """\
            import (
                clock "time"
                c "context"
            )
            func T() { clock.Sleep(d); c.WithTimeout(p, d) }
            """
        )
    )
    assert _counts(GO, rel, renamed) == {
        "time: a clock or timer from package time": 1,
        "time: a context with a deadline": 1,
    }
    dotted = SourceText('import . "time"\nfunc T() { Sleep(d); x.Now(); Now() }\n')
    assert _counts(GO, rel, dotted) == {"time: a clock or timer from package time": 2}
    unbound = SourceText(
        textwrap.dedent(
            """\
            import _ "time"
            // clock "time"
            func T() { clock.Sleep(d) }
            """
        )
    )
    assert _labels(GO, rel, unbound) == set()


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
            msg = f"time.sleep(1) {x}"
            msg = t"time.sleep(1) {x}"
            """
        )
    )
    assert _labels(PYTHON, rel, prose) == set()
    for alone in ("proc.wait(BOUND_SECONDS)\n", "future.result(15)\n"):
        assert _labels(PYTHON, rel, SourceText(alone)) == {"time: a positional timeout"}


def test_a_python_primitive_imported_by_name_is_read_qualified() -> None:
    """A from-import, a module alias and a star import each hide no site."""
    rel = RelPath("python/tests/test_x.py")
    source = SourceText(
        textwrap.dedent(
            """\
            import time as clock
            import asyncio as aio
            from threading import Thread as Worker
            from datetime import date, datetime as dt
            from concurrent import futures
            from os import fork
            from time import *
            clock.sleep(1)
            perf_counter()
            await aio.sleep(2)
            Worker(target=f)
            date.today()
            dt.now()
            futures.ThreadPoolExecutor()
            fork()
            """
        )
    )
    assert _counts(PYTHON, rel, source) == {
        "time: a clock or sleep from module time": 2,
        "time: an asyncio sleep of a duration": 1,
        "thread: a thread or timer from module threading": 1,
        "time: a wall-clock date": 2,
        "thread: an executor": 1,
        "thread: a process pool or fork": 1,
    }
    unbound = SourceText(
        textwrap.dedent(
            """\
            # from time import sleep
            from pathlib import Path
            sleep = Path("x")
            obj.sleep(1)
            await aio.sleep(0)
            """
        )
    )
    assert _labels(PYTHON, rel, unbound) == set()


def test_python_clock_reads_signal_timers_and_yields_are_sites() -> None:
    """A process or thread clock, a signal or watchdog timer and a scheduler yield each count."""
    source = SourceText(
        textwrap.dedent(
            """\
            time.process_time()
            time.thread_time_ns()
            time.clock_gettime(c)
            signal.alarm(1)
            signal.setitimer(w, 1)
            faulthandler.dump_traceback_later(5)
            os.sched_yield()
            datetime.date.today()
            """
        )
    )
    assert _counts(PYTHON, RelPath("python/tests/test_x.py"), source) == {
        "time: a clock or sleep from module time": 3,
        "time: a signal timer": 3,
        "thread: a yield to the scheduler": 1,
        "time: a wall-clock date": 1,
    }


@pytest.mark.parametrize(
    "source",
    [
        SourceText('import time\nnote = "a\u2028b"\ntime.sleep(1)\n# threading.Thread()\n'),
        SourceText('import time as t\nnote = "a\u2028b"\nt.sleep(1)\n# threading.Thread()\n'),
    ],
    ids=["qualified", "alias"],
)
def test_a_line_separator_inside_a_string_ends_no_line(source: SourceText) -> None:
    """A U+2028 in a string literal ends no line, so the code and comment after it are read."""
    assert _counts(PYTHON, RelPath("python/tests/test_x.py"), source) == {
        "time: a clock or sleep from module time": 1
    }


@pytest.mark.parametrize(
    "script",
    [
        SourceText("import time as t\\rx = 1\\nt.sleep(1)\\n"),
        SourceText("import time as t\\r\\nx = 1\\rt.sleep(1)\\n"),
    ],
    ids=["cr", "crlf"],
)
def test_a_carriage_return_in_a_child_script_ends_a_row(script: SourceText) -> None:
    """A carriage return or CRLF in a child script ends a row, so the alias read after it counts."""
    source = SourceText(f'import subprocess\nsubprocess.run(["python", "-c", "{script}"])\n')
    assert _counts(PYTHON, RelPath("python/tests/test_x.py"), source) == {
        "time: a clock or sleep from module time": 1
    }


@pytest.mark.parametrize(
    "script",
    [
        SourceText("import os\\r# time.sleep(1)\\nos.getcwd()\\n"),
        SourceText("import os\\r\\n# time.sleep(1)\\r\\nos.getcwd()\\r\\n"),
    ],
    ids=["cr", "crlf"],
)
def test_a_comment_after_a_carriage_return_in_a_child_script_is_no_site(
    script: SourceText,
) -> None:
    """A comment after a carriage return or CRLF in a child script is blanked like any other."""
    source = SourceText(f'import subprocess\nsubprocess.run(["python", "-c", "{script}"])\n')
    assert (
        _counts(PYTHON, RelPath("python/tests/test_x.py"), source)
        == dict[CanonicalText, SiteCount]()
    )


def test_an_indented_child_script_whose_rows_end_at_a_carriage_return_is_read_dedented() -> None:
    """An indented child script whose rows end at a carriage return is dedented and counts."""
    script = SourceText("\\r    import time\\r    time.sleep(1)\\r")
    source = SourceText(f'import subprocess\nsubprocess.run(["python", "-c", "{script}"])\n')
    assert _counts(PYTHON, RelPath("python/tests/test_x.py"), source) == {
        "time: a clock or sleep from module time": 1
    }


@pytest.mark.parametrize(
    ("source", "blanked"),
    [
        (SourceText("x = '''a\nb'''\nimport os\n"), BlankedCode("x =     \n    \nimport os\n")),
        (SourceText("x = '''a\rb'''\nimport os\n"), BlankedCode("x =     \r    \nimport os\n")),
        (
            SourceText("x = '''a\r\nb'''\r\nimport os\r\n"),
            BlankedCode("x =     \r\n    \r\nimport os\r\n"),
        ),
        (SourceText("x = 'Xy'\nimport os\n"), BlankedCode("x =     \nimport os\n")),
    ],
    ids=["lf", "cr", "crlf", "letters"],
)
def test_a_blanked_string_keeps_the_row_ends_inside_it(
    source: SourceText, blanked: BlankedCode
) -> None:
    """Blanking a string spanning rows keeps each line feed, carriage return or CRLF ending one."""
    assert blank_python(source) == blanked


@pytest.mark.parametrize("end", [SourceText("\r"), SourceText("\r\n")], ids=["cr", "crlf"])
def test_an_alias_read_on_a_row_a_carriage_return_opens_is_spelled_out(end: SourceText) -> None:
    """The parser ends a row at a carriage return or CRLF, and the alias read on it is spelled."""
    source = SourceText(f"import time as t{end}t.sleep(1){end}")
    assert spell_python_aliases(source, blank_python(source)) == BlankedCode(
        f"import time as t{end}time.sleep(1){end}"
    )


def test_a_child_script_in_a_python_string_is_read_as_source() -> None:
    """A script a test hands a child interpreter counts; prose and a docstring do not.

    An f-string or a t-string is read with what it interpolates standing as a
    name, and a line passed alone is read dedented.  The gate's own test is
    exempt, its strings being the fixtures it feeds the gate.
    """
    source = SourceText(
        textwrap.dedent(
            '''\
            """Names time.sleep(1) in prose."""
            holder = f"""
                import fcntl, time
                fd = open({path!r})
                time.sleep(60)
            """
            script = render(t"import time\\ntime.sleep(1)\\n{x}")
            lines = ["import sys", "    time.sleep(0.01)"]
            note = "wait for time.sleep(1) then go"
            '''
        )
    )
    sleep = CanonicalText("time: a clock or sleep from module time")
    assert _counts(PYTHON, RelPath("python/tests/test_x.py"), source) == {sleep: 3}
    assert not rows_of(RelPath("python/tests/test_check_test_determinism.py"), source)


def test_an_async_client_on_its_default_runner_is_a_thread_site() -> None:
    """An async client built in a test without ``run_in_thread`` leans on executor threads.

    Found by what the file imports, an alias or the module included; one handed
    a runner, the sync client and a mention in a string are none.
    """
    source = SourceText(
        textwrap.dedent(
            """\
            import aletheia.asyncio as aio
            from aletheia import AletheiaClient
            from aletheia.asyncio import AletheiaClient as AsyncClient
            AsyncClient()
            AsyncClient(sync_client=AletheiaClient())
            aio.AletheiaClient()
            aletheia.asyncio.AletheiaClient()
            AsyncClient(run_in_thread=executor)
            AletheiaClient()
            note = "AsyncClient()"
            """
        )
    )
    assert async_clients_on_a_thread(source) == 4
    rel = RelPath("python/tests/test_x.py")
    assert rows_of(rel, source) == {RowKey(rel, ASYNC_CLIENT_ON_A_THREAD): 4}
    assert not rows_of(RelPath("python/aletheia/x.py"), source)


def test_an_unseeded_go_property_check_is_a_random_site() -> None:
    """A testing/quick check handed no Rand, or no configuration, draws from the clock."""
    rel = RelPath("go/aletheia/x_test.go")
    source = SourceText(
        textwrap.dedent(
            """\
            func T(t *testing.T) {
                quick.Check(p, &quick.Config{MaxCount: 200})
                quick.Check(p, &quick.Config{MaxCount: 200, Rand: propertyRand(t)})
                quick.Check(func(x int) bool { return f(x) }, nil)
                quick.CheckEqual(f, g, nil)
                quick.Check(p, cfg)
            }
            // quick.Config{MaxCount: 1} in a comment
            """
        )
    )
    assert _counts(GO, rel, source) == {UNSEEDED_PROPERTY: 3}


def test_an_unseeded_hypothesis_test_and_a_replaying_profile_are_random_sites() -> None:
    """A hypothesis test with no seed, and a profile with an example database, each count.

    Found by what the file imports, an alias or the module included; a seeded
    test, a plain test, a profile with no database and a mention in a string
    are none.
    """
    source = SourceText(
        textwrap.dedent(
            """\
            import hypothesis as h
            from hypothesis import given, seed as fix, settings
            from hypothesis import settings as s

            @given(x=st.integers())
            def test_a(x): ...

            @fix(1)
            @given(x=st.integers())
            def test_b(x): ...

            @h.given(st.integers())
            def test_c(x): ...

            @h.seed(2)
            @h.given(st.integers())
            async def test_d(x): ...

            @pytest.mark.slow
            @given(st.integers())
            def test_f(x): ...

            def test_e(): ...

            def test_g(): ...

            @given(st.integers())
            async def test_h(x): ...

            settings.register_profile("a", max_examples=1)
            s.register_profile("b", database=None)
            h.settings.register_profile("c", database=None, deadline=None)
            h.settings.register_profile("d", database=other)
            note = "@given(x) settings.register_profile()"
            """
        )
    )
    assert unseeded_properties(source) == 4
    rel = RelPath("python/tests/test_x.py")
    assert rows_of(rel, source) == {
        RowKey(rel, UNSEEDED_PROPERTY): 4,
        RowKey(rel, REPLAYING_PROFILE): 2,
    }
    assert not rows_of(RelPath("python/aletheia/x.py"), source)


def test_a_rust_async_client_on_its_worker_thread_is_a_thread_site() -> None:
    """A Rust test building the async client by a constructor that starts its worker counts.

    A renamed import of the client is read through; one a turn executor hosts,
    and the builder's own definition, are none.
    """
    rel = RelPath("rust/tests/t.rs")
    source = SourceText(
        textwrap.dedent(
            """\
            use aletheia::AsyncClient as Async;
            fn t() {
                let a = AsyncClient::new();
                let b = Async::new();
                let c = ClientBuilder::default().build_async();
                let d = builder.build_async_with_backend(Box::new(mock));
                let e = ClientBuilder::build_async(builder);
                let f = turns.adopt(Client::new()?);
            }
            pub async fn build_async(self) {}
            """
        )
    )
    assert _counts(RUST, rel, source) == {ASYNC_CLIENT_ON_A_THREAD: 5}


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


def test_cpp_c_library_time_benchmarks_and_yields_are_sites() -> None:
    """A POSIX sleep, clock or timer, a Catch2 benchmark and a yield count; a member does not."""
    rel = RelPath("cpp/tests/x.cpp")
    source = SourceText(
        textwrap.dedent(
            """\
            void f() {
              usleep(1);
              ::sleep(1);
              clock_gettime(CLOCK_MONOTONIC, &ts);
              std::time(nullptr);
              time(nullptr);
              alarm(1);
              BENCHMARK("x") { return 1; };
              std::this_thread::yield();
              sched_yield();
              stand_in.sleep(1);
              clock->time();
            }
            """
        )
    )
    assert _counts(CPP, rel, source) == {
        "time: a sleep": 2,
        "time: a clock read": 3,
        "time: a timer": 1,
        "time: a Catch2 benchmark": 1,
        "thread: a yield to the scheduler": 2,
    }


def test_a_cpp_alias_or_using_declaration_is_read_qualified() -> None:
    """A clock alias, a namespace alias and a used ``std`` name hide no site; an include is none."""
    rel = RelPath("cpp/tests/x.cpp")
    source = SourceText(
        textwrap.dedent(
            """\
            #include <thread>
            using clock = std::chrono::steady_clock;
            typedef std::chrono::system_clock wall;
            namespace s = std;
            using std::thread;
            void f() {
              auto a = clock::now();
              auto b = wall::now();
              auto c = s::async(g);
              thread w([] {});
              std::this_thread::get_id();
            }
            """
        )
    )
    assert _counts(CPP, rel, source) == {
        "time: a clock read": 2,
        "thread: std::async": 1,
        "thread: a std::thread or std::jthread": 2,
    }
    directive = SourceText("using namespace std;\nvoid f() { jthread j([] {}); async(g); }\n")
    assert _counts(CPP, rel, directive) == {
        "thread: a std::thread or std::jthread": 1,
        "thread: std::async": 1,
    }
    member = SourceText("#include <thread>\nvoid f() { worker.thread(); }\n")
    assert _labels(CPP, rel, member) == set()


def test_a_rust_use_is_read_as_the_path_it_names() -> None:
    """A used, renamed, nested or glob-imported thread or clock name hides no site."""
    rel = RelPath("rust/tests/t.rs")
    source = SourceText(
        textwrap.dedent(
            """\
            use std::{thread::{self, sleep}, time::Instant as Clock};
            use std::thread::spawn as start;
            fn t() {
                sleep(d);
                start(|| {});
                let _ = Clock::now();
                thread::yield_now();
                gate.sleep(d);
            }
            """
        )
    )
    assert _counts(RUST, rel, source) == {
        "time: a sleep": 1,
        "thread: a spawned or scoped thread": 1,
        "time: a clock read": 1,
        "thread: a yield to the scheduler": 1,
    }
    glob = SourceText("use std::thread::*;\nfn t() { scope(|s| {}); park_timeout(d); }\n")
    assert _counts(RUST, rel, glob) == {
        "thread: a spawned or scoped thread": 1,
        "time: a wait of a duration": 1,
    }
    unwatched = SourceText("use std::sync::Mutex;\nfn t() { let m = Mutex::new(0); sleep(d); }\n")
    assert _labels(RUST, rel, unwatched) == set()


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


def test_every_rust_test_binary_is_held_to_one_test_at_a_time(tmp_path: Path) -> None:
    """Cargo's configuration must force one test thread; unforced, other or absent fails."""
    assert rust_tests_run_alone(git_toplevel())
    config = tmp_path / "rust" / ".cargo" / "config.toml"
    assert not rust_tests_run_alone(tmp_path)
    config.parent.mkdir(parents=True)
    for setting, holds in (
        ('{ value = "1", force = true }', True),
        ('"1"', False),
        ('{ value = "4", force = true }', False),
        ('{ value = "1", force = false }', False),
    ):
        _ = config.write_text(f"[env]\nRUST_TEST_THREADS = {setting}\n", encoding="utf-8")
        assert rust_tests_run_alone(tmp_path) is holds, setting
    _ = config.write_text("[env\n", encoding="utf-8")
    assert not rust_tests_run_alone(tmp_path)


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


# The runtime guard, tools/_determinism_guard.py, holds what a test reaches, the
# code under test included.  Each plant below is a test run in a session inside
# this one, under the guard: what it does must fail it, or must not.


def _run_guarded(pytester: pytest.Pytester, test: SourceText) -> pytest.RunResult:
    """Run one test file under the guard, in a session inside this test's process."""
    _ = pytester.makeconftest('pytest_plugins = ["tools._determinism_guard"]')
    _ = pytester.makepyfile(test_plant=textwrap.dedent(test))
    return pytester.runpytest_inprocess("-p", "no:cacheprovider")


@pytest.mark.parametrize(
    ("call", "refusal"),
    [
        ("import threading; threading.Thread(target=print).start()", "a thread started"),
        ("import _thread; _thread.start_new_thread(print, ())", "a thread started on print"),
        ("import _thread; _thread.start_joinable_thread(print)", "a thread started on print"),
        ("import time; time.sleep(0)", "time.sleep(0)"),
        ("import threading; threading.Event().wait(0.01)", "a wait of 0.01 s on a condition"),
        ("import threading; threading.Event().wait(0)", "a wait of 0 s on a condition"),
        ("import queue; queue.Queue().get(timeout=0.01)", "s on a condition"),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).wait(timeout=1)",
            "a process waited on for 1 s",
        ),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).wait(timeout=0)",
            "a process waited on for 0 s",
        ),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).communicate(timeout=1)",
            "a process waited on for 1 s",
        ),
        ("import select; select.select([], [], [], 0)", "a select of 0 s"),
        ("import signal; signal.alarm(1)", "an alarm set 1 s ahead"),
        ("import signal; signal.setitimer(signal.ITIMER_REAL, 1)", "a timer set 1 s ahead"),
        ("import asyncio; asyncio.run(asyncio.sleep(1))", "a callback scheduled 1.0 s ahead"),
    ],
)
def test_the_guard_fails_a_test_that_waits_or_starts_a_thread(
    pytester: pytest.Pytester, call: SourceText, refusal: SourceText
) -> None:
    """A thread, a sleep, a timed wait or a timer fails the test that reaches it, named."""
    result = _run_guarded(pytester, SourceText(f"def test_plant():\n    {call}\n"))
    result.assert_outcomes(failed=1)
    assert refusal in result.stdout.str()


@pytest.mark.parametrize(
    "call",
    [
        "import asyncio; asyncio.run(asyncio.sleep(0))",
        "import signal; signal.alarm(0)",
        "import signal; signal.setitimer(signal.ITIMER_REAL, 0)",
        "import threading; e = threading.Event(); e.set(); e.wait()",
        "import asyncio; loop = asyncio.new_event_loop(); loop.call_later(0, print); loop.close()",
    ],
)
def test_the_guard_lets_a_test_yield_cancel_a_timer_or_wait_on_what_is_done(
    pytester: pytest.Pytester, call: SourceText
) -> None:
    """A zero sleep on a loop yields, a zero timer cancels one, and a set event waits on nothing."""
    result = _run_guarded(pytester, SourceText(f"def test_plant():\n    {call}\n"))
    result.assert_outcomes(passed=1)


def test_the_guard_fails_a_test_whose_code_caught_the_refusal(pytester: pytest.Pytester) -> None:
    """A refusal the code under test swallowed still fails the test, at its teardown."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import time
            def test_plant():
                try:
                    time.sleep(0)
                except BaseException:
                    pass
            """
        ),
    )
    result.assert_outcomes(passed=1, errors=1)
    assert "time.sleep(0)" in result.stdout.str()


def test_every_test_reads_one_clock_that_moves_only_when_told(pytester: pytest.Pytester) -> None:
    """The clocks and calendars all read the guard's clock, from the same instant in every test."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import datetime, time
            import pytest
            from tools._determinism_guard import Seconds

            START = 1_767_225_600

            def test_the_clocks_agree_and_stand_still():
                assert time.time() == time.monotonic() == time.perf_counter() == START
                assert time.time_ns() == time.monotonic_ns() == START * 1_000_000_000
                assert time.perf_counter_ns() == time.process_time_ns() == START * 1_000_000_000
                assert time.thread_time_ns() == START * 1_000_000_000
                assert time.gmtime()[:6] == (2026, 1, 1, 0, 0, 0)
                assert datetime.datetime.now(datetime.UTC) == datetime.datetime(
                    2026, 1, 1, tzinfo=datetime.UTC
                )
                assert datetime.date.today() == datetime.date.fromtimestamp(START)
                assert isinstance(datetime.datetime.now(), datetime.datetime)
                assert datetime.datetime.today() == datetime.datetime.fromtimestamp(START)
                assert datetime.datetime.utcnow() == datetime.datetime(2026, 1, 1)
                assert time.process_time() == time.thread_time() == START
                assert time.clock_gettime(time.CLOCK_MONOTONIC) == START
                assert time.clock_gettime_ns(time.CLOCK_MONOTONIC) == START * 1_000_000_000
                assert time.localtime() == time.localtime(START)
                assert time.ctime() == time.ctime(START)
                assert time.asctime() == time.asctime(time.localtime(START))
                assert time.strftime("%Y-%m-%d") == time.strftime("%Y-%m-%d", time.localtime(START))
                assert time.gmtime(0)[:6] == (1970, 1, 1, 0, 0, 0)
                assert time.mktime(time.localtime(0)) == 0
                assert time.ctime(0) == time.asctime(time.localtime(0))
                assert time.strftime("%Y", time.gmtime(0)) == "1970"
                assert time.time() == START

            def test_the_clock_moves_by_what_the_test_advances(clock):
                clock.advance(Seconds(2.5))
                assert time.monotonic() == START + 2.5

            def test_the_clock_never_moves_back(clock):
                with pytest.raises(ValueError, match="moves forward"):
                    clock.advance(Seconds(-1))
                assert time.time() == START

            def test_the_next_test_starts_from_the_same_instant():
                assert time.time() == START
            """
        ),
    )
    result.assert_outcomes(passed=4)


def test_a_session_inside_a_test_leaves_the_guard_on(pytester: pytest.Pytester) -> None:
    """The guard stays until the last session that installed it ends, not the first."""
    _run_guarded(pytester, SourceText("def test_plant():\n    pass\n")).assert_outcomes(passed=1)
    assert _determinism_guard.installed()
