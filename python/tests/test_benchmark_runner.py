# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``benchmarks/run_all.sh``: what the benchmark runner refuses, skips, reports and leaves behind.

The runner is a shell script, so each claim is shown by running it, into a
results directory, a C++ tree, a Go binary path and a cargo target of the
test's own, which is what its overrides exist for. The compiled lanes are
driven through PATH: a ``cmake``, ``go`` or ``cargo`` that refuses to build,
one that writes a harness naming where it was built, or a PATH that holds
neither go nor cargo. The Python lane cannot be driven that way, since the
runner activates the venv before it and the venv's interpreter runs whatever
PATH held, so an arm that reaches a lane runs the real Python benchmark at one
frame against the built kernel, and skips when the kernel has not been built,
as the CLI tests do.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import TYPE_CHECKING, Final, NamedTuple, NewType

import pytest
from _bench_schema import BindingId, ModeName
from _cli_check_helpers import CliRun, run_captured, skip_without_ffi
from _processes import CommandWord

from tools._common import find_executable

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Sequence

# The flags a mode reads, and the words of one command line.
type Flags = frozenset[CommandWord]
type Words = list[CommandWord]
# A PATH value: the directories a shell searches for a command, joined.
SearchPath = NewType("SearchPath", str)

_REPO: Final = Path(__file__).resolve().parents[2]
_RUNNER: Final = _REPO / "benchmarks" / "run_all.sh"
_RUNS_THE_SHELL: Final = (
    "the runner is a shell script: what it refuses, skips, reports and leaves behind "
    "is what the shell does"
)
_GIT_ANSWERS: Final = "whether a path is ignored is git's own answer"

THROUGHPUT: Final = ModeName("throughput")
LATENCY: Final = ModeName("latency")
SCALING: Final = ModeName("scaling")

# The lanes the runner builds: as its messages name them, and as their result files do.
_COMPILED: Final = {
    Prose("C++"): BindingId("cpp"),
    Prose("Go"): BindingId("go"),
    Prose("Rust"): BindingId("rust"),
}

# What each mode reads, as the runner's own table says; every other flag is refused.
_READS: Final[dict[ModeName, Flags]] = {
    THROUGHPUT: frozenset({CommandWord("--frames"), CommandWord("--runs")}),
    LATENCY: frozenset({CommandWord("--frames"), CommandWord("--warmup")}),
    SCALING: frozenset({CommandWord("--runs"), CommandWord("--quick")}),
}
_FLAGS: Final[Flags] = frozenset(flag for reads in _READS.values() for flag in reads)
# A value for each flag that takes one.
_A_VALUE: Final = {
    CommandWord("--frames"): CommandWord("100"),
    CommandWord("--runs"): CommandWord("3"),
    CommandWord("--warmup"): CommandWord("7"),
}
# Each mode given exactly what it reads.
_ACCEPTED: Final[dict[ModeName, Words]] = {
    THROUGHPUT: [CommandWord(w) for w in ("--frames", "10000", "--runs", "10")],
    LATENCY: [CommandWord(w) for w in ("--frames", "10000", "--warmup", "500")],
    SCALING: [CommandWord(w) for w in ("--runs", "10", "--quick")],
}
_ONE_FRAME: Final[Words] = [
    CommandWord(w) for w in ("--frames", "1", "--runs", "1", "--bench", THROUGHPUT)
]
_BAD_COUNTS: Final = (CommandWord("0"), CommandWord("-1"), CommandWord("abc"), CommandWord("1.5"))
# The tools the runner and the venv's interpreter reach through PATH when no lane builds.
_TOOLS_THE_RUNNER_NEEDS: Final = (
    "bash",
    "sh",
    "sed",
    "awk",
    "mktemp",
    "mv",
    "rm",
    "mkdir",
    "dirname",
    "basename",
    "cat",
    "uname",
)


class Scratch(NamedTuple):
    """Where one run writes: results, a C++ tree, a Go binary, a cargo target and its tools."""

    results: Path
    cpp_tree: Path
    go_binary: Path
    cargo_target: Path
    bin: Path


def _scratch(tmp_path: Path) -> Scratch:
    scratch = Scratch(
        tmp_path / "results",
        tmp_path / "cpp",
        tmp_path / "go-benchmark",
        tmp_path / "cargo",
        tmp_path / "bin",
    )
    for directory in (scratch.results, scratch.cpp_tree, scratch.bin):
        directory.mkdir()
    return scratch


def _run(
    scratch: Scratch,
    words: Sequence[CommandWord],
    *,
    path: SearchPath | None = None,
    results: Path | None = None,
) -> CliRun:
    """Run the runner with ``words``, every place it writes pointed into ``scratch``."""
    env = os.environ | {
        "ALETHEIA_BENCH_RESULTS_DIR": str(results or scratch.results),
        "ALETHEIA_BENCH_CPP_BUILD_DIR": str(scratch.cpp_tree),
        "ALETHEIA_BENCH_GO_BIN": str(scratch.go_binary),
        "CARGO_TARGET_DIR": str(scratch.cargo_target),
    }
    if path is not None:
        env["PATH"] = path
    done = run_captured([find_executable("bash"), str(_RUNNER), *words], env, cwd=_REPO)
    return CliRun(ExitStatus(done.returncode), Prose(done.stdout), Prose(done.stderr))


def _sentinel(scratch: Scratch, mode: ModeName) -> Path:
    """Plant a result file the mode's clear would remove."""
    sentinel = scratch.results / f"sentinel_{mode}.json"
    _ = sentinel.write_text("{}\n", encoding="utf-8")
    return sentinel


def _configured(scratch: Scratch, build_type: Prose) -> None:
    """Give the C++ tree the cache line the runner reads before building there."""
    _ = (scratch.cpp_tree / "CMakeCache.txt").write_text(
        f"CMAKE_BUILD_TYPE:STRING={build_type}\n", encoding="utf-8"
    )


def _stub(directory: Path, name: CommandWord, body: Prose) -> None:
    """Write a shell script named ``name`` into ``directory``."""
    tool = directory / name
    _ = tool.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
    tool.chmod(0o755)


def _stubs_first(scratch: Scratch) -> SearchPath:
    """PATH with the scratch tools ahead of the real ones."""
    return SearchPath(f"{scratch.bin}{os.pathsep}{os.environ['PATH']}")


def _builds_refused(scratch: Scratch) -> SearchPath:
    """Stub cmake, go and cargo that refuse to build; return the PATH that reaches them first."""
    for tool in ("cmake", "go", "cargo"):
        _stub(scratch.bin, CommandWord(tool), Prose('echo "stub: build refused" >&2\nexit 1'))
    return _stubs_first(scratch)


def _without_go_or_cargo(scratch: Scratch) -> SearchPath:
    """Make a PATH of the tools the runner needs and nothing else, so go and cargo are absent."""
    for tool in _TOOLS_THE_RUNNER_NEEDS:
        (scratch.bin / tool).symlink_to(find_executable(tool))
    return SearchPath(str(scratch.bin))


def _hint(stderr: Prose) -> Prose:
    """Read the command the Debug refusal prints under ``Reconfigure with``, unindented."""
    lines = stderr.splitlines()
    after = [lines[i + 1] for i, line in enumerate(lines[:-1]) if "Reconfigure with" in line]
    assert len(after) == 1, stderr
    return Prose(after[0].strip())


@pytest.mark.process(_RUNS_THE_SHELL)
@pytest.mark.parametrize("flag", [CommandWord("--frames"), CommandWord("--runs")])
@pytest.mark.parametrize("value", [*_BAD_COUNTS, CommandWord("")])
def test_a_count_that_is_not_a_positive_integer_is_refused_before_anything_is_touched(
    tmp_path: Path, flag: CommandWord, value: CommandWord
) -> None:
    """``--frames`` and ``--runs`` take a positive integer; the refusal clears no result."""
    scratch = _scratch(tmp_path)
    sentinel = _sentinel(scratch, THROUGHPUT)
    done = _run(scratch, [flag, value, CommandWord("--bench"), CommandWord(THROUGHPUT)])
    assert done.returncode != 0
    assert f"ERROR: {flag} must be a positive integer, got '{value}'" in done.stderr
    assert sentinel.exists(), "the refusal cleared the mode's results"


@pytest.mark.process(_RUNS_THE_SHELL)
@pytest.mark.parametrize("value", [*_BAD_COUNTS[1:], CommandWord("")])
def test_a_warmup_that_is_not_a_whole_number_is_refused_before_anything_is_touched(
    tmp_path: Path, value: CommandWord
) -> None:
    """``--warmup`` takes a non-negative integer; the refusal clears no result."""
    scratch = _scratch(tmp_path)
    sentinel = _sentinel(scratch, THROUGHPUT)
    words = [CommandWord("--warmup"), value, CommandWord("--bench"), CommandWord(THROUGHPUT)]
    done = _run(scratch, words)
    assert done.returncode != 0
    assert f"ERROR: --warmup must be a non-negative integer, got '{value}'" in done.stderr
    assert sentinel.exists(), "the refusal cleared the mode's results"


@pytest.mark.process(_RUNS_THE_SHELL)
def test_a_warmup_of_zero_and_a_valid_count_pair_reach_the_mode_check(tmp_path: Path) -> None:
    """Zero warms nothing and is a choice; a valid pair is refused by nothing before the mode."""
    scratch = _scratch(tmp_path)
    cold = _run(scratch, [CommandWord(w) for w in ("--warmup", "0", "--bench", "bogus")])
    assert "--warmup must be" not in cold.stderr
    assert "ERROR: unknown --bench 'bogus'" in cold.stderr
    pair = _run(
        scratch, [CommandWord(w) for w in ("--frames", "10000", "--runs", "5", "--bench", "bogus")]
    )
    assert "positive integer" not in pair.stderr
    assert "ERROR: unknown --bench 'bogus'" in pair.stderr


@pytest.mark.process(_RUNS_THE_SHELL)
@pytest.mark.parametrize(
    ("mode", "flag"),
    [(mode, flag) for mode, reads in _READS.items() for flag in sorted(_FLAGS - reads)],
)
def test_a_flag_the_mode_does_not_read_is_refused_before_the_results_are_cleared(
    tmp_path: Path, mode: ModeName, flag: CommandWord
) -> None:
    """A flag outside the mode's set is refused, naming the set, never accepted and dropped."""
    scratch = _scratch(tmp_path)
    sentinel = _sentinel(scratch, mode)
    value = [_A_VALUE[flag]] if flag in _A_VALUE else []
    done = _run(scratch, [CommandWord("--bench"), CommandWord(mode), flag, *value])
    assert done.returncode != 0
    refusal = re.search(
        rf"ERROR: {flag} is not read by the {mode} mode, which reads (.*)$",
        done.stderr,
        re.MULTILINE,
    )
    assert refusal is not None, done.stderr
    assert set(refusal.group(1).split(", ")) == {word.removeprefix("--") for word in _READS[mode]}
    assert sentinel.exists(), "the refusal cleared the mode's results"


@pytest.mark.process(_RUNS_THE_SHELL)
@pytest.mark.parametrize("mode", list(_ACCEPTED))
def test_every_flag_the_mode_reads_reaches_the_results_directory(
    tmp_path: Path, mode: ModeName
) -> None:
    """Given only what it reads, a mode gets as far as making its results directory.

    An unwritable results directory stops the run right after the argument
    checks and before any lane, so the whole of the checking is reached
    without a measurement.
    """
    scratch = _scratch(tmp_path)
    done = _run(
        scratch,
        [CommandWord("--bench"), CommandWord(mode), *_ACCEPTED[mode]],
        results=Path("/proc/no-such-directory/results"),
    )
    assert done.returncode != 0
    assert "is not read by" not in done.stderr, done.stderr
    assert "mkdir" in done.stderr, done.stderr


@pytest.mark.process(_RUNS_THE_SHELL)
def test_a_broken_build_with_the_toolchain_present_fails_the_run(tmp_path: Path) -> None:
    """A configured tree or a present toolchain whose build fails is a FAIL, not a SKIP."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    _configured(scratch, Prose("Release"))
    done = _run(scratch, _ONE_FRAME, path=_builds_refused(scratch))
    assert done.returncode != 0
    for lane, binding in _COMPILED.items():
        assert f">>> FAIL: {lane} benchmark failed to build" in done.stderr, done.stderr
        assert f"SKIP: {lane}" not in done.stderr
        assert not (scratch.results / f"{binding}_{THROUGHPUT}.json").exists(), lane
    assert "WARNING: Failed benchmarks: C++ Go Rust" in done.stderr


@pytest.mark.process(_RUNS_THE_SHELL)
def test_the_latency_banner_names_the_warmup_given_and_no_run_count(tmp_path: Path) -> None:
    """The banner names what the run was given, and the lanes are given it: the Python lane runs."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    _configured(scratch, Prose("Release"))
    words = [CommandWord(w) for w in ("--bench", LATENCY, "--frames", "1", "--warmup", "7")]
    done = _run(scratch, words, path=_builds_refused(scratch))
    assert re.search(r"^Warmup: +7$", done.stdout, re.MULTILINE), done.stdout
    assert re.search(r"^Ops: +1$", done.stdout, re.MULTILINE), done.stdout
    assert not re.search(r"^Runs:", done.stdout, re.MULTILINE), done.stdout
    # The flags reached the Python lane, which ran them: only the three stubbed lanes failed.
    assert (scratch.results / f"python_{LATENCY}.json").exists(), done.stderr
    assert "WARNING: Failed benchmarks: C++ Go Rust" in done.stderr


@pytest.mark.process(_RUNS_THE_SHELL)
def test_a_missing_toolchain_skips_its_lane_and_the_run_passes(tmp_path: Path) -> None:
    """With no go and no cargo on PATH their lanes are SKIPs, and the lanes that can run do."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    done = _run(scratch, _ONE_FRAME, path=_without_go_or_cargo(scratch))
    assert done.returncode == 0, done.stderr
    for lane in ("Go", "Rust"):
        assert f">>> SKIP: {lane} benchmark not built" in done.stderr, done.stderr
    assert "FAIL:" not in done.stderr
    assert (scratch.results / f"python_{THROUGHPUT}.json").exists()


@pytest.mark.process(_RUNS_THE_SHELL)
def test_a_temp_file_failure_fails_the_lane_and_leaves_nothing_behind(tmp_path: Path) -> None:
    """A lane whose second scratch file cannot be made is a FAIL, and its first file is removed."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    path = _without_go_or_cargo(scratch)
    shim = tmp_path / "shim"
    shim.mkdir()
    _stub(
        shim,
        CommandWord("mktemp"),
        Prose(
            'case "$*" in *.err.*) echo "shim: mktemp refused" >&2; exit 1 ;; esac\n'
            + f'exec {find_executable("mktemp")} "$@"'
        ),
    )
    done = _run(scratch, _ONE_FRAME, path=SearchPath(f"{shim}{os.pathsep}{path}"))
    assert done.returncode != 0
    assert f"FAIL: Python could not create a temp file in {scratch.results}" in done.stderr
    assert "Saved:" not in done.stdout
    assert not list(scratch.results.iterdir()), "a scratch file was left behind"


@pytest.mark.process(_RUNS_THE_SHELL)
def test_each_compiled_harness_runs_where_it_was_told_to_build(tmp_path: Path) -> None:
    """Each lane runs the harness built where the runner named, and replays what it said."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    _configured(scratch, Prose("Release"))
    harness = scratch.bin / "harness"
    # harness <lane> <path>: write at the path a harness that says where it runs from and fails.
    _stub(
        scratch.bin,
        CommandWord("harness"),
        Prose(
            'mkdir -p "$(dirname "$2")" || exit 1\n'
            + """printf '#!/bin/sh\\necho "%s harness at $0" >&2\\nexit 1\\n' "$1" > "$2" """
            + '&& chmod +x "$2"'
        ),
    )
    # cmake --build <tree> --target benchmark
    _stub(scratch.bin, CommandWord("cmake"), Prose(f'exec "{harness}" C++ "$2/benchmark"'))
    # go build -o <path> ./benchmarks/
    _stub(scratch.bin, CommandWord("go"), Prose(f'exec "{harness}" Go "$3"'))
    # cargo build --release --example benchmark, from rust/
    _stub(
        scratch.bin,
        CommandWord("cargo"),
        Prose(f'exec "{harness}" Rust "${{CARGO_TARGET_DIR:-target}}/release/examples/benchmark"'),
    )
    done = _run(scratch, _ONE_FRAME, path=_stubs_first(scratch))
    for lane, built_at in (
        ("C++", scratch.cpp_tree / "benchmark"),
        ("Go", scratch.go_binary),
        ("Rust", scratch.cargo_target / "release" / "examples" / "benchmark"),
    ):
        assert f"| {lane} harness at {built_at}" in done.stderr, done.stderr


@pytest.mark.process(_RUNS_THE_SHELL)
def test_the_debug_refusal_prints_one_reconfigure_that_keeps_the_tree(tmp_path: Path) -> None:
    """A Debug C++ tree is refused before the clear, with one plain configure as the way out."""
    skip_without_ffi()
    scratch = _scratch(tmp_path)
    _configured(scratch, Prose("Debug"))
    sentinel = _sentinel(scratch, THROUGHPUT)
    done = _run(scratch, [])
    assert done.returncode != 0
    assert f"ERROR: {scratch.cpp_tree} is configured with CMAKE_BUILD_TYPE=Debug." in done.stderr
    assert sentinel.exists(), "the refusal cleared the mode's results"
    assert _hint(done.stderr) == f"cmake -S cpp -B {scratch.cpp_tree} -DCMAKE_BUILD_TYPE=Release"


def _ignored(path: Prose) -> bool:
    """Whether the ignore rules match ``path``: 0 says yes, 1 says no, anything else is an error.

    Asked of the rules alone, since the index answers for a tracked file, a
    committed baseline included, whatever the rules say.
    """
    done = run_captured(
        [find_executable("git"), "check-ignore", "-q", "--no-index", path],
        dict(os.environ),
        cwd=_REPO,
    )
    assert done.returncode in (0, 1), done.stderr
    return done.returncode == 0


@pytest.mark.process(_GIT_ANSWERS)
def test_the_runners_scratch_files_and_a_lanes_result_are_ignored_and_a_baseline_is_not() -> None:
    """The runner's scratch shapes and a result are ignored and untracked, a baseline neither."""
    shapes = re.findall(
        r'mktemp "\$RESULTS_DIR/(\.[a-z]+\.)\$\{lang\}\.XXXXXX"',
        _RUNNER.read_text(encoding="utf-8"),
    )
    assert shapes, "the runner's mktemp templates were not found"
    for name in (*(f"{shape}Go.abc123" for shape in shapes), f"go_{THROUGHPUT}.json"):
        assert _ignored(Prose(f"benchmarks/results/{name}")), name
    assert not _ignored(Prose(f"benchmarks/results/go_{THROUGHPUT}_baseline.json"))
    # And the index agrees with the rules: nothing but the rules file and baselines is tracked.
    tracked = run_captured(
        [find_executable("git"), "ls-files", "benchmarks/results"], dict(os.environ), cwd=_REPO
    )
    assert tracked.returncode == 0, tracked.stderr
    assert {
        Path(line).name
        for line in tracked.stdout.splitlines()
        if not line.endswith("_baseline.json")
    } == {".gitignore"}, tracked.stdout
