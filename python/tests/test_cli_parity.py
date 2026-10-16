# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cross-CLI integration harness — drives all three CLIs as real subprocesses.

``docs/CLI_SCENARIOS.yaml`` is the behavior contract: every scenario there is
executed against the Python CLI (``python -m aletheia``), the Go CLI
(``go/cmd/aletheia``, built once per session into a pytest temp dir), and the
C++ CLI (``cpp/build/aletheia-cli``). Exit codes, stdout/stderr substrings,
and ``--json`` output pins must match the contract on every CLI — a scenario
passing on one CLI and failing on another is a parity bug in that CLI.

Every invocation runs with ``ALETHEIA_LIB`` pointing at the repo's built
``build/libaletheia-ffi.so`` so all three CLIs exercise the same verified
core. Missing prerequisites skip loudly:

* no ``build/libaletheia-ffi.so``  -> every test running a CLI skips ("cabal run shake -- build"),
  the contract's own checks still running
* no ``go`` toolchain on PATH      -> the Go CLI lane skips
* no ``cpp/build/aletheia-cli``    -> the C++ CLI lane skips
  ("run cmake --build cpp/build first")

A subcommand-coverage tripwire asserts every ``meta.subcommands`` entry has at
least one scenario and appears in each CLI's ``--help`` output, so a new
subcommand cannot ship uncovered and a CLI cannot silently drop one. No run may
change its fixture, and a workbook a scenario says a run writes is held to the
sheets and header rows the Python Excel loader reads, so the three CLIs write
one template.
"""

from __future__ import annotations

import errno
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, NotRequired, TypedDict, cast

import pytest
import yaml
from _cli_check_helpers import StdoutFd, run_captured
from _excel_helpers import sheet_headers
from _yaml_shape import as_str_object_dict

from aletheia.common_types import Prose
from aletheia.excel_loader import CHECKS_HEADERS, DBC_HEADERS, WHEN_THEN_HEADERS
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from aletheia.types import JSONValue

_REPO_ROOT = Path(__file__).resolve().parents[2]
_SCENARIOS_PATH = _REPO_ROOT / "docs" / "CLI_SCENARIOS.yaml"
_FIXTURES_DIR = Path(__file__).resolve().parent / "fixtures"
_FFI_LIB = _REPO_ROOT / "build" / "libaletheia-ffi.so"
_CPP_CLI = _REPO_ROOT / "cpp" / "build" / "aletheia-cli"
_GO_MODULE_DIR = _REPO_ROOT / "go"

# The Python CLI resolves the ``aletheia`` package from this cwd exactly like
# the repo's other gates (which all run from ``python/``); the Go/C++ binaries
# ignore cwd (absolute binary + fixture + ALETHEIA_LIB paths).
_SUBPROCESS_CWD = _REPO_ROOT / "python"

# A CLI lane's contract key, which also keys a scenario's overrides.
type CliName = Literal["python", "go", "cpp"]
_CLI_NAMES: tuple[CliName, ...] = ("python", "go", "cpp")

# Why every lane starts a process, the Go one also building its binary first.
_RUNS_AS_A_PROGRAM = (
    "each binding's command line answers the parity contract as a program,"
    + " run the same way for every binding"
)

# Why the stdout self-check starts a process.
_HANDS_A_PROGRAM_ITS_STDOUT = "the claim is the standard output the harness hands a program"

# The exit codes the contract at the head of CLI_SCENARIOS.yaml defines.
type ExitCode = Literal[0, 1, 2]
_EXIT_CODES: tuple[ExitCode, ...] = (0, 1, 2)

# What a scenario's ``stdout`` can set up in place of the capture, each a
# standard output that refuses a write (see _run_cli), and what the write
# fails with.
type StdoutValue = Literal["full", "closed", "broken-pipe", "over-limit"]
_STDOUT_VALUES: tuple[StdoutValue, ...] = ("full", "closed", "broken-pipe", "over-limit")
_WRITE_REFUSAL = {
    "full": errno.ENOSPC,
    "closed": errno.EBADF,
    "broken-pipe": errno.EPIPE,
    "over-limit": errno.EFBIG,
}

# The device refusing every write, and the shell lines that run a program with
# descriptor 1 closed and with a file-size limit of one block (512 bytes under
# dash, 1024 under bash), the program replacing the shell.
_FULL_DEVICE = Path("/dev/full")
_CLOSED_STDOUT = ["/bin/sh", "-c", 'exec "$0" "$@" >&-']
_ONE_BLOCK_LIMIT = ["/bin/sh", "-c", 'ulimit -f 1 && exec "$0" "$@"']

# The pins that read a run's stdout back, which a run whose stdout goes to the
# device cannot carry.
type ReadBackPin = Literal["stdout_contains", "json"]
_READ_BACK_PINS: tuple[ReadBackPin, ...] = ("stdout_contains", "json")

# The pins naming substrings a stream must carry.
type StreamPin = Literal["stdout_contains", "stderr_contains"]
_STREAM_PINS: tuple[StreamPin, ...] = ("stdout_contains", "stderr_contains")

# A scenario's id, a subcommand, an argument as the contract writes it (its
# placeholders unreplaced), a fixture's path under python/tests/fixtures/, a
# substring a stream must carry, and a JSON pin's path.
ScenarioId = NewType("ScenarioId", str)
Subcommand = NewType("Subcommand", str)
CliArg = NewType("CliArg", str)
FixtureName = NewType("FixtureName", str)
Needle = NewType("Needle", str)
JsonPinPath = NewType("JsonPinPath", str)

# One scenario entry spelled as CLI_SCENARIOS.yaml spells one, for the self-checks.
YamlEntry = NewType("YamlEntry", str)

# The workbook the Python Excel loader reads: its sheets, in order, each with
# its header row.
_TEMPLATE_SHEETS: dict[str, list[str]] = {
    "DBC": DBC_HEADERS,
    "Checks": CHECKS_HEADERS,
    "When-Then": WHEN_THEN_HEADERS,
}


class CliUnderTest(NamedTuple):
    """A CLI lane: its contract key (for overrides) and launcher argv."""

    name: CliName
    argv: list[str]


class Expect(TypedDict):
    """What a run must show, the schema's ``expect``."""

    exit: ExitCode
    stdout_contains: NotRequired[list[Needle]]
    stderr_contains: NotRequired[list[Needle]]
    json: NotRequired[dict[JsonPinPath, JSONValue]]
    writes_template: NotRequired[CliArg]


class Override(TypedDict):
    """One CLI's ratified divergence: an ``args`` or ``expect`` replacing the scenario's."""

    args: NotRequired[list[CliArg]]
    expect: NotRequired[Expect]


class Scenario(TypedDict):
    """One entry of the schema's ``scenarios``."""

    id: ScenarioId
    subcommand: Subcommand
    args: list[CliArg]
    fixture: NotRequired[FixtureName]
    fixture_exists: NotRequired[bool]
    stdout: NotRequired[StdoutValue]
    expect: Expect
    overrides: NotRequired[dict[CliName, Override]]


# The keys each mapping may hold, read from ``__annotations__``: under postponed
# annotations ``__required_keys__`` holds every key, the optional ones included.
_SCENARIO_KEYS = frozenset(Scenario.__annotations__)
_EXPECT_KEYS = frozenset(Expect.__annotations__)
_OVERRIDE_KEYS = frozenset(Override.__annotations__)


# ---------------------------------------------------------------------------
# Contract loading (module scope: scenarios parametrize test collection)
# ---------------------------------------------------------------------------


def _str_list(value: object, context: Prose) -> list[str]:
    """Narrow a YAML value to a list of strings."""
    assert isinstance(value, list), f"{context}: expected list, got {type(value).__name__}"
    out: list[str] = []
    for i, entry in enumerate(cast("list[object]", value)):
        assert isinstance(entry, str), f"{context}[{i}]: expected string, got {entry!r}"
        out.append(entry)
    return out


def _text(value: object, context: Prose) -> str:
    """Narrow a YAML value to a non-empty string."""
    assert isinstance(value, str), f"{context}: expected string, got {value!r}"
    assert value, f"{context}: must be non-empty"
    return value


def _exit_code(value: object, context: Prose) -> ExitCode:
    """Narrow a YAML value to one of the contract's exit codes, a boolean refused."""
    codes: list[ExitCode] = [
        code
        for code in _EXIT_CODES
        if isinstance(value, int) and not isinstance(value, bool) and value == code
    ]
    assert codes, f"{context}: expected one of {list(_EXIT_CODES)}, got {value!r}"
    return codes[0]


def _cli_name(value: object, context: Prose) -> CliName:
    """Narrow a value to a CLI lane's name."""
    names: list[CliName] = [name for name in _CLI_NAMES if value == name]
    assert names, f"{context}: expected one of {list(_CLI_NAMES)}, got {value!r}"
    return names[0]


def _parse_expect(raw: object, context: Prose) -> Expect:
    """Check an ``expect`` mapping against the schema and return it typed."""
    entry = as_str_object_dict(raw, context)
    unknown = sorted(entry.keys() - _EXPECT_KEYS)
    assert not unknown, f"{context}: keys outside the schema: {unknown}"
    expect: Expect = {"exit": _exit_code(entry.get("exit"), Prose(f"{context}.exit"))}
    for stream in _STREAM_PINS:
        if stream in entry:
            needles = _str_list(entry[stream], Prose(f"{context}.{stream}"))
            assert all(needles), f"{context}.{stream}: an empty substring pins nothing"
            expect[stream] = [Needle(needle) for needle in needles]
    if "json" in entry:
        pins = entry["json"]
        assert is_str_dict(pins), f"{context}.json: expected mapping with string keys"
        expect["json"] = {JsonPinPath(path): value for path, value in pins.items()}
    if "writes_template" in entry:
        expect["writes_template"] = CliArg(
            _text(entry["writes_template"], Prose(f"{context}.writes_template"))
        )
    return expect


def _parse_override(raw: object, context: Prose) -> Override:
    """Check one CLI's override against the schema and return it typed."""
    entry = as_str_object_dict(raw, context)
    unknown = sorted(entry.keys() - _OVERRIDE_KEYS)
    assert not unknown, f"{context}: keys outside the schema: {unknown}"
    override: Override = {}
    if "args" in entry:
        override["args"] = [
            CliArg(arg) for arg in _str_list(entry["args"], Prose(f"{context}.args"))
        ]
    if "expect" in entry:
        override["expect"] = _parse_expect(entry["expect"], Prose(f"{context}.expect"))
    return override


def _parse_scenario(raw: object, context: Prose) -> Scenario:
    """Check one ``scenarios`` entry against the schema and return it typed.

    Beside each field's own check, two rules join fields: ``fixture_exists``
    stands only beside a fixture, and a run with a ``stdout`` pins nothing read
    back, in ``expect`` or in an override's.
    """
    entry = as_str_object_dict(raw, context)
    unknown = sorted(entry.keys() - _SCENARIO_KEYS)
    assert not unknown, f"{context}: keys outside the schema: {unknown}"
    sid = ScenarioId(_text(entry.get("id"), Prose(f"{context}.id")))
    scenario: Scenario = {
        "id": sid,
        "subcommand": Subcommand(_text(entry.get("subcommand"), Prose(f"{sid}.subcommand"))),
        "args": [CliArg(arg) for arg in _str_list(entry.get("args"), Prose(f"{sid}.args"))],
        "expect": _parse_expect(entry.get("expect"), Prose(f"{sid}.expect")),
    }
    if "fixture" in entry:
        scenario["fixture"] = FixtureName(_text(entry["fixture"], Prose(f"{sid}.fixture")))
    if "fixture_exists" in entry:
        assert "fixture" in entry, f"{sid}: fixture_exists without a fixture"
        exists_flag = entry["fixture_exists"]
        assert isinstance(exists_flag, bool), f"{sid}: fixture_exists must be a bool"
        scenario["fixture_exists"] = exists_flag
    if "overrides" in entry:
        overrides = as_str_object_dict(entry["overrides"], Prose(f"{sid}.overrides"))
        scenario["overrides"] = {
            _cli_name(name, Prose(f"{sid}.overrides")): _parse_override(
                override, Prose(f"{sid}.overrides.{name}")
            )
            for name, override in overrides.items()
        }
    if "stdout" in entry:
        value = entry["stdout"]
        modes: list[StdoutValue] = [mode for mode in _STDOUT_VALUES if value == mode]
        assert modes, f"{sid}: stdout {value!r} is not one of {list(_STDOUT_VALUES)}"
        scenario["stdout"] = modes[0]
        for cli_name in _CLI_NAMES:
            expect = _effective_expect(scenario, cli_name)
            read_back = [pin for pin in _READ_BACK_PINS if pin in expect]
            assert not read_back, (
                f"{sid} on {cli_name}: stdout {value!r} leaves nothing to read back for {read_back}"
            )
    return scenario


def _load_contract() -> tuple[list[Subcommand], list[Scenario]]:
    """Load CLI_SCENARIOS.yaml and return (meta.subcommands, scenarios), each checked."""
    with _SCENARIOS_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = as_str_object_dict(raw, "CLI_SCENARIOS.yaml root")
    meta = as_str_object_dict(root.get("meta"), "meta")
    subcommands = [
        Subcommand(sub) for sub in _str_list(meta.get("subcommands"), Prose("meta.subcommands"))
    ]
    assert subcommands, "meta.subcommands is empty"
    scenarios_raw: object = root.get("scenarios")
    assert isinstance(scenarios_raw, list), "CLI_SCENARIOS.yaml must contain a 'scenarios' list"
    scenarios = [
        _parse_scenario(entry, Prose(f"scenarios[{idx}]"))
        for idx, entry in enumerate(cast("list[object]", scenarios_raw))
    ]
    assert scenarios, "CLI_SCENARIOS.yaml 'scenarios' list is empty"
    return subcommands, scenarios


def _override(scenario: Scenario, cli_name: CliName) -> Override:
    """Return the CLI's override, empty where the scenario has none for it."""
    none: Override = {}
    return scenario.get("overrides", {}).get(cli_name, none)


def _effective_args(scenario: Scenario, cli_name: CliName) -> list[CliArg]:
    """Return the CLI's ``args``, its override's replacing the scenario's wholesale."""
    return _override(scenario, cli_name).get("args", scenario["args"])


def _effective_expect(scenario: Scenario, cli_name: CliName) -> Expect:
    """Return the CLI's ``expect``, its override's replacing the scenario's wholesale."""
    return _override(scenario, cli_name).get("expect", scenario["expect"])


_SUBCOMMANDS, _SCENARIOS = _load_contract()

_SCENARIO_IDS: list[ScenarioId] = [scenario["id"] for scenario in _SCENARIOS]


# ---------------------------------------------------------------------------
# CLI launchers
# ---------------------------------------------------------------------------


@pytest.fixture(scope="session", name="cli_env")
def fixture_cli_env() -> dict[str, str]:
    """Environment for every CLI call: ALETHEIA_LIB -> the repo's built .so."""
    if not _FFI_LIB.exists():
        pytest.skip(f"libaletheia-ffi.so missing at {_FFI_LIB} — run 'cabal run shake -- build'")
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(_FFI_LIB)
    return env


@pytest.fixture(scope="session", name="go_cli")
def fixture_go_cli(tmp_path_factory: pytest.TempPathFactory) -> list[str]:
    """Build the Go CLI once per session; skip loudly without a Go toolchain."""
    go_tool = shutil.which("go")
    if go_tool is None:
        reason = (
            "go toolchain not found on PATH — cannot build go/cmd/aletheia, "
            "so the Go CLI parity lane cannot run; install Go to restore it"
        )
        pytest.skip(reason)
    binary = tmp_path_factory.mktemp("go-cli") / "aletheia-go-cli"
    build = subprocess.run(
        [go_tool, "build", "-o", str(binary), "./cmd/aletheia"],
        cwd=_GO_MODULE_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    assert build.returncode == 0, (
        f"'go build ./cmd/aletheia' failed (exit {build.returncode}):\n{build.stderr}"
    )
    return [str(binary)]


@pytest.fixture(params=_CLI_NAMES, name="cli")
def fixture_cli(request: pytest.FixtureRequest) -> CliUnderTest:
    """One CLI lane per param: python / go / cpp."""
    name = _cli_name(request.param, Prose("the cli fixture's param"))
    if name == "python":
        return CliUnderTest(name, [sys.executable, "-m", "aletheia"])
    if name == "go":
        return CliUnderTest(name, cast("list[str]", request.getfixturevalue("go_cli")))
    if not _CPP_CLI.exists():
        pytest.skip(f"C++ CLI missing at {_CPP_CLI} — run cmake --build cpp/build first")
    return CliUnderTest(name, [str(_CPP_CLI)])


def _run_cli(
    argv: list[str],
    env: dict[str, str],
    stdout: StdoutValue | None = None,
    scratch: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run one CLI invocation from the harness's fixed cwd, its stdout as ``stdout`` says.

    Unset, the output is captured; ``full`` sends it to /dev/full, ``closed``
    starts the program with descriptor 1 closed, ``broken-pipe`` hands it a
    pipe whose reader is gone, and ``over-limit`` a file under ``scratch`` that
    may grow by one block.
    """
    match stdout:
        case None:
            return run_captured(argv, env, cwd=_SUBPROCESS_CWD)
        case "full":
            return run_captured(argv, env, cwd=_SUBPROCESS_CWD, stdout_to=_FULL_DEVICE)
        case "closed":
            return run_captured([*_CLOSED_STDOUT, *argv], env, cwd=_SUBPROCESS_CWD)
        case "broken-pipe":
            reader, writer = os.pipe()
            os.close(reader)
            try:
                return run_captured(argv, env, cwd=_SUBPROCESS_CWD, stdout_to=StdoutFd(writer))
            finally:
                os.close(writer)
        case "over-limit":
            assert scratch is not None, "an over-limit run writes its report under a scratch dir"
            return run_captured(
                [*_ONE_BLOCK_LIMIT, *argv], env, cwd=_SUBPROCESS_CWD, stdout_to=scratch / "report"
            )


# ---------------------------------------------------------------------------
# Scenario resolution
# ---------------------------------------------------------------------------


def _resolve_fixture(scenario: Scenario) -> Path | None:
    """Resolve the scenario's fixture path, if it names one, and check its declared existence."""
    if "fixture" not in scenario:
        return None
    sid = scenario["id"]
    fixture_path = _FIXTURES_DIR / scenario["fixture"]
    if scenario.get("fixture_exists", True):
        assert fixture_path.exists(), f"{sid}: fixture missing: {fixture_path}"
    else:
        assert not fixture_path.exists(), (
            f"{sid}: fixture declared fixture_exists:false but exists: {fixture_path}"
        )
    return fixture_path


def _substitute(arg: CliArg, fixture_path: Path | None, tmp_path: Path, sid: ScenarioId) -> str:
    """Replace the ``{dbc}`` and ``{tmp}`` placeholders of one argument."""
    resolved = arg
    if "{dbc}" in arg:
        assert fixture_path is not None, f"{sid}: an argument names {{dbc}} and there is no fixture"
        resolved = arg.replace("{dbc}", str(fixture_path))
    return resolved.replace("{tmp}", str(tmp_path))


def _digest(path: Path | None) -> str | None:
    """Return the SHA-256 of the file at ``path``, or None where there is none."""
    if path is None or not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _subset_matches(item: object, want: dict[str, object]) -> bool:
    """Report whether ``item`` is a mapping carrying every (key, value) of ``want``."""
    if not isinstance(item, dict):
        return False
    item_map = cast("dict[object, object]", item)
    return all(item_map.get(key) == value for key, value in want.items())


def _assert_json_pins(stdout: str, pins: dict[JsonPinPath, JSONValue], context: Prose) -> None:
    """Parse ``stdout`` as JSON and assert every contract pin against it.

    Dotted paths descend into objects; a path ending in ``[]`` pins list
    membership by subset-match (see the schema comment in CLI_SCENARIOS.yaml).
    """
    parsed = as_str_object_dict(json.loads(stdout), f"{context}: --json stdout")
    for path, expected in pins.items():
        if path.endswith("[]"):
            key = path.removesuffix("[]")
            actual: object = parsed.get(key)
            assert isinstance(actual, list), f"{context}: json pin {path!r}: {key!r} is not a list"
            actual_list = cast("list[object]", actual)
            for want_raw in _pin_entry_list(expected, context, path):
                assert any(_subset_matches(item, want_raw) for item in actual_list), (
                    f"{context}: json pin {path!r}: no entry matches {want_raw!r}"
                    f" in {actual_list!r}"
                )
        else:
            node: object = parsed
            for part in path.split("."):
                node_map = as_str_object_dict(node, f"{context}: json path {path!r}")
                assert part in node_map, f"{context}: json path {path!r}: key {part!r} missing"
                node = node_map[part]
            assert node == expected, (
                f"{context}: json pin {path!r}: expected {expected!r}, got {node!r}"
            )


def _pin_entry_list(expected: object, sid: str, path: str) -> list[dict[str, object]]:
    """Narrow a ``[]``-pin's expected value to a list of partial objects."""
    assert isinstance(expected, list), f"{sid}: json pin {path!r} must hold a list of objects"
    return [
        as_str_object_dict(entry, f"{sid}: json pin {path!r}[{i}]")
        for i, entry in enumerate(cast("list[object]", expected))
    ]


def _failure_report(argv: list[str], result: subprocess.CompletedProcess[str]) -> str:
    """Render one CLI invocation for an assertion message."""
    return (
        f"argv: {argv}\n"
        f"exit: {result.returncode}\n"
        f"--- stdout (tail) ---\n{result.stdout[-2000:]}\n"
        f"--- stderr (tail) ---\n{result.stderr[-2000:]}"
    )


# ---------------------------------------------------------------------------
# The parity tests
# ---------------------------------------------------------------------------


@pytest.mark.process(_RUNS_AS_A_PROGRAM)
@pytest.mark.parametrize("scenario", _SCENARIOS, ids=_SCENARIO_IDS)
def test_scenario(
    cli: CliUnderTest, scenario: Scenario, cli_env: dict[str, str], tmp_path: Path
) -> None:
    """Every contract scenario holds on every CLI (exit code, streams, JSON, files)."""
    sid = scenario["id"]
    fixture_path = _resolve_fixture(scenario)
    fixture_before = _digest(fixture_path)
    argv = [
        *cli.argv,
        scenario["subcommand"],
        *(
            _substitute(arg, fixture_path, tmp_path, sid)
            for arg in _effective_args(scenario, cli.name)
        ),
    ]
    result = _run_cli(argv, cli_env, scenario.get("stdout"), tmp_path)
    assert _digest(fixture_path) == fixture_before, (
        f"{sid} on {cli.name}: the run changed its fixture\n{_failure_report(argv, result)}"
    )
    expect = _effective_expect(scenario, cli.name)
    _assert_expect(expect, argv, result, sid, cli.name)
    if "writes_template" in expect:
        written = Path(_substitute(expect["writes_template"], fixture_path, tmp_path, sid))
        assert written.is_file(), f"{sid} on {cli.name}: no workbook at {written}"
        assert sheet_headers(written) == _TEMPLATE_SHEETS, (
            f"{sid} on {cli.name}: the workbook's sheets and header rows are not the loader's"
        )


def _assert_expect(
    expect: Expect,
    argv: list[str],
    result: subprocess.CompletedProcess[str],
    sid: ScenarioId,
    cli_name: CliName,
) -> None:
    """Assert a run's exit code, stream substrings and JSON pins against ``expect``."""
    assert result.returncode == expect["exit"], (
        f"{sid} on {cli_name}: expected exit {expect['exit']}\n{_failure_report(argv, result)}"
    )
    for needle in expect.get("stdout_contains", []):
        assert needle in result.stdout, (
            f"{sid} on {cli_name}: stdout missing {needle!r}\n{_failure_report(argv, result)}"
        )
    for needle in expect.get("stderr_contains", []):
        assert needle in result.stderr, (
            f"{sid} on {cli_name}: stderr missing {needle!r}\n{_failure_report(argv, result)}"
        )
    if "json" in expect:
        _assert_json_pins(result.stdout, expect["json"], Prose(f"{sid} on {cli_name}"))


# ---------------------------------------------------------------------------
# Subcommand-coverage tripwire
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("subcommand", _SUBCOMMANDS)
def test_every_subcommand_has_a_scenario(subcommand: Subcommand) -> None:
    """Each declared subcommand carries at least one contract scenario."""
    covered = {scenario["subcommand"] for scenario in _SCENARIOS}
    assert subcommand in covered, (
        f"meta.subcommands entry {subcommand!r} has no scenario in CLI_SCENARIOS.yaml — "
        "a subcommand without a scenario is invisible to the parity harness"
    )


def test_scenario_subcommands_are_declared() -> None:
    """No scenario names a subcommand outside meta.subcommands (typo guard)."""
    for scenario in _SCENARIOS:
        sub = scenario["subcommand"]
        assert sub in _SUBCOMMANDS, (
            f"scenario {scenario['id']!r} uses undeclared subcommand {sub!r}"
        )


def test_scenario_ids_unique() -> None:
    """Scenario ids are unique (they key test parametrization)."""
    assert len(set(_SCENARIO_IDS)) == len(_SCENARIO_IDS), (
        f"duplicate scenario ids in CLI_SCENARIOS.yaml: {sorted(_SCENARIO_IDS)}"
    )


def _load_entry(entry: YamlEntry) -> Scenario:
    """Load one self-check entry through the checks every contract scenario passes."""
    return _parse_scenario(yaml.safe_load(entry), Prose("self-check"))


# The fields the refusals start from, which pass every check.
_VALID = "id: self-check, subcommand: validate, args: [x]"


@pytest.mark.parametrize(
    ("entry", "refusal"),
    [
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, stdout_contain: [x]}}"),
            "keys outside the schema",
            id="a scenario key outside the schema",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, stdout_contain: [x]}}}}"),
            "keys outside the schema",
            id="an expect key outside the schema",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, overrides: {{go: {{arg: [x]}}}}}}"),
            "keys outside the schema",
            id="an override key outside the schema",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, overrides: {{rust: {{args: [x]}}}}}}"),
            "expected one of",
            id="an override for a lane the harness does not run",
        ),
        pytest.param(
            YamlEntry("{id: '', subcommand: validate, args: [x], expect: {exit: 0}}"),
            "must be non-empty",
            id="an empty id",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: true}}}}"),
            "expected one of",
            id="a boolean exit, which equals 1",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 3}}}}"),
            "expected one of",
            id="an exit code outside the contract",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: '0'}}}}"),
            "expected one of",
            id="an exit code spelled as a string",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, stderr_contains: ['']}}}}"),
            "an empty substring pins nothing",
            id="an empty substring, which is in every stream",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, json: [status]}}}}"),
            "expected mapping with string keys",
            id="json pins that are not a mapping",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, writes_template: 7}}}}"),
            "expected string",
            id="a workbook path that is not a string",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, fixture_exists: false}}"),
            "fixture_exists without a fixture",
            id="fixture_exists without a fixture",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, fixture: x.dbc, fixture_exists: 'no'}}"),
            "fixture_exists must be a bool",
            id="fixture_exists that is not a boolean",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}, stdout: pipe}}"),
            "is not one of",
            id="a stdout the harness does not know",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, stdout_contains: [x]}}, stdout: full}}"),
            "nothing to read back",
            id="stdout full with a stdout substring",
        ),
        pytest.param(
            YamlEntry(f"{{{_VALID}, expect: {{exit: 0, json: {{x: 0}}}}, stdout: full}}"),
            "nothing to read back",
            id="stdout full with json pins",
        ),
        pytest.param(
            YamlEntry(
                f"{{{_VALID}, expect: {{exit: 0}}, stdout: full,"
                + " overrides: {go: {expect: {exit: 0, json: {x: 0}}}}}"
            ),
            "nothing to read back",
            id="stdout full with json pins in an override",
        ),
    ],
)
def test_an_entry_breaking_the_schema_is_refused(entry: YamlEntry, refusal: Prose) -> None:
    """An entry breaking one rule of the schema is refused at load, naming that rule."""
    with pytest.raises(AssertionError, match=refusal):
        _ = _load_entry(entry)


def test_the_self_checks_start_from_a_valid_entry() -> None:
    """The fields the refusals start from load, so each refusal is its one broken rule's."""
    assert _load_entry(YamlEntry(f"{{{_VALID}, expect: {{exit: 0}}}}")) == {
        "id": "self-check",
        "subcommand": "validate",
        "args": ["x"],
        "expect": {"exit": 0},
    }


def test_an_override_replaces_args_and_expect_for_its_cli_alone() -> None:
    """An override's ``args`` and ``expect`` replace the scenario's for its CLI and no other."""
    scenario = _load_entry(
        YamlEntry(
            "{id: self-check, subcommand: validate, args: [shared], expect: {exit: 0},"
            + " overrides: {go: {args: [own], expect: {exit: 2}}}}"
        )
    )
    assert _effective_args(scenario, "go") == ["own"]
    assert _effective_expect(scenario, "go") == {"exit": 2}
    for other in ("python", "cpp"):
        assert _effective_args(scenario, other) == ["shared"], other
        assert _effective_expect(scenario, other) == {"exit": 0}, other


@pytest.mark.process(_HANDS_A_PROGRAM_ITS_STDOUT)
@pytest.mark.parametrize("stdout", _STDOUT_VALUES)
def test_each_stdout_refuses_a_write(stdout: StdoutValue, tmp_path: Path) -> None:
    """Each ``stdout`` hands the program a standard output whose write fails as its name says.

    The program writes twice, so a limit the first write reaches fails the second.
    """
    argv = [sys.executable, "-I", "-c", "import os\nfor _ in range(2): os.write(1, b'x' * 4096)"]
    result = _run_cli(argv, dict(os.environ), stdout, tmp_path)
    assert f"[Errno {_WRITE_REFUSAL[stdout]}]" in result.stderr, _failure_report(argv, result)
    assert result.stdout == "", _failure_report(argv, result)


@pytest.mark.process(_RUNS_AS_A_PROGRAM)
def test_a_double_dash_before_the_subcommand_is_refused(cli: CliUnderTest) -> None:
    """The subcommand comes first: a ``--`` ahead of it is refused, nothing validated."""
    argv = [*cli.argv, "--", "validate", "--dbc", str(_FIXTURES_DIR / "dbc_corpus" / "minimal.dbc")]
    result = _run_cli(argv, dict(os.environ))
    assert result.returncode == 2, _failure_report(argv, result)
    assert result.stdout == "", _failure_report(argv, result)


@pytest.mark.process(_RUNS_AS_A_PROGRAM)
def test_help_lists_every_subcommand(cli: CliUnderTest, cli_env: dict[str, str]) -> None:
    """Each CLI's --help output names every declared subcommand."""
    argv = [*cli.argv, "--help"]
    result = _run_cli(argv, cli_env)
    assert result.returncode == 0, (
        f"--help on {cli.name}: expected exit 0\n{_failure_report(argv, result)}"
    )
    for subcommand in _SUBCOMMANDS:
        assert subcommand in result.stdout, (
            f"--help on {cli.name}: subcommand {subcommand!r} missing from usage output\n"
            f"{_failure_report(argv, result)}"
        )
