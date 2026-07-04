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

* no ``build/libaletheia-ffi.so``  -> every test skips ("cabal run shake -- build")
* no ``go`` toolchain on PATH      -> the Go CLI lane skips
* no ``cpp/build/aletheia-cli``    -> the C++ CLI lane skips
  ("run cmake --build cpp/build first")

A subcommand-coverage tripwire asserts every ``meta.subcommands`` entry has at
least one scenario and appears in each CLI's ``--help`` output, so a new
subcommand cannot ship uncovered and a CLI cannot silently drop one.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple, cast

import pytest
import yaml
from _yaml_shape import as_str_object_dict

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
_RUN_TIMEOUT_S = 120  # each call brings up the GHC RTS; empirically ~1 s
_BUILD_TIMEOUT_S = 300

_CLI_NAMES: tuple[str, ...] = ("python", "go", "cpp")


class CliUnderTest(NamedTuple):
    """A CLI lane: its contract key (for overrides) and launcher argv."""

    name: str
    argv: list[str]


# ---------------------------------------------------------------------------
# Contract loading (module scope: scenarios parametrize test collection)
# ---------------------------------------------------------------------------


def _str_list(value: object, context: str) -> list[str]:
    """Narrow a YAML value to a list of strings."""
    assert isinstance(value, list), f"{context}: expected list, got {type(value).__name__}"
    out: list[str] = []
    for i, entry in enumerate(cast("list[object]", value)):
        assert isinstance(entry, str), f"{context}[{i}]: expected string, got {entry!r}"
        out.append(entry)
    return out


def _load_contract() -> tuple[list[str], list[dict[str, object]]]:
    """Load CLI_SCENARIOS.yaml and return (meta.subcommands, scenarios)."""
    with _SCENARIOS_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = as_str_object_dict(raw, "CLI_SCENARIOS.yaml root")
    meta = as_str_object_dict(root.get("meta"), "meta")
    subcommands = _str_list(meta.get("subcommands"), "meta.subcommands")
    assert subcommands, "meta.subcommands is empty"
    scenarios_raw: object = root.get("scenarios")
    assert isinstance(scenarios_raw, list), "CLI_SCENARIOS.yaml must contain a 'scenarios' list"
    scenarios: list[dict[str, object]] = []
    for idx, entry in enumerate(cast("list[object]", scenarios_raw)):
        scenarios.append(as_str_object_dict(entry, f"scenarios[{idx}]"))
    assert scenarios, "CLI_SCENARIOS.yaml 'scenarios' list is empty"
    return subcommands, scenarios


_SUBCOMMANDS, _SCENARIOS = _load_contract()


def _scenario_str(scenario: dict[str, object], key: str) -> str:
    """Fetch a required string field from a scenario."""
    value: object = scenario.get(key)
    assert isinstance(value, str), f"scenario field {key!r}: expected string"
    assert value, f"scenario field {key!r}: must be non-empty"
    return value


_SCENARIO_IDS: list[str] = [_scenario_str(s, "id") for s in _SCENARIOS]


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
        timeout=_BUILD_TIMEOUT_S,
        check=False,
    )
    assert build.returncode == 0, (
        f"'go build ./cmd/aletheia' failed (exit {build.returncode}):\n{build.stderr}"
    )
    return [str(binary)]


@pytest.fixture(params=_CLI_NAMES, name="cli")
def fixture_cli(request: pytest.FixtureRequest) -> CliUnderTest:
    """One CLI lane per param: python / go / cpp."""
    name: object = request.param
    assert isinstance(name, str)
    if name == "python":
        return CliUnderTest(name, [sys.executable, "-m", "aletheia"])
    if name == "go":
        return CliUnderTest(name, cast("list[str]", request.getfixturevalue("go_cli")))
    if not _CPP_CLI.exists():
        pytest.skip(f"C++ CLI missing at {_CPP_CLI} — run cmake --build cpp/build first")
    return CliUnderTest(name, [str(_CPP_CLI)])


def _run_cli(argv: list[str], env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    """Run one CLI invocation with the harness's fixed cwd/timeout."""
    return subprocess.run(
        argv,
        cwd=_SUBPROCESS_CWD,
        env=env,
        capture_output=True,
        text=True,
        timeout=_RUN_TIMEOUT_S,
        check=False,
    )


# ---------------------------------------------------------------------------
# Scenario resolution
# ---------------------------------------------------------------------------


def _resolve_fixture(scenario: dict[str, object]) -> Path:
    """Resolve the scenario's fixture path and check its declared existence."""
    sid = _scenario_str(scenario, "id")
    fixture_path = _FIXTURES_DIR / _scenario_str(scenario, "fixture")
    exists_flag: object = scenario.get("fixture_exists", True)
    assert isinstance(exists_flag, bool), f"{sid}: fixture_exists must be a bool"
    if exists_flag:
        assert fixture_path.exists(), f"{sid}: fixture missing: {fixture_path}"
    else:
        assert not fixture_path.exists(), (
            f"{sid}: fixture declared fixture_exists:false but exists: {fixture_path}"
        )
    return fixture_path


def _effective(scenario: dict[str, object], cli_name: str, key: str) -> object:
    """Fetch ``key`` from the scenario, honoring a per-CLI override if present.

    An override replaces the scenario-level value for that key wholesale
    (see the schema comment in CLI_SCENARIOS.yaml).
    """
    overrides_raw: object = scenario.get("overrides")
    if overrides_raw is not None:
        sid = _scenario_str(scenario, "id")
        overrides = as_str_object_dict(overrides_raw, f"{sid}.overrides")
        cli_override_raw: object = overrides.get(cli_name)
        if cli_override_raw is not None:
            cli_override = as_str_object_dict(cli_override_raw, f"{sid}.overrides.{cli_name}")
            if key in cli_override:
                return cli_override[key]
    return scenario.get(key)


def _subset_matches(item: object, want: dict[str, object]) -> bool:
    """Report whether ``item`` is a mapping carrying every (key, value) of ``want``."""
    if not isinstance(item, dict):
        return False
    item_map = cast("dict[object, object]", item)
    return all(item_map.get(key) == value for key, value in want.items())


def _assert_json_pins(stdout: str, pins: dict[str, object], sid: str) -> None:
    """Parse ``stdout`` as JSON and assert every contract pin against it.

    Dotted paths descend into objects; a path ending in ``[]`` pins list
    membership by subset-match (see the schema comment in CLI_SCENARIOS.yaml).
    """
    parsed = as_str_object_dict(json.loads(stdout), f"{sid}: --json stdout")
    for path, expected in pins.items():
        if path.endswith("[]"):
            key = path.removesuffix("[]")
            actual: object = parsed.get(key)
            assert isinstance(actual, list), f"{sid}: json pin {path!r}: {key!r} is not a list"
            actual_list = cast("list[object]", actual)
            for want_raw in _pin_entry_list(expected, sid, path):
                assert any(_subset_matches(item, want_raw) for item in actual_list), (
                    f"{sid}: json pin {path!r}: no entry matches {want_raw!r} in {actual_list!r}"
                )
        else:
            node: object = parsed
            for part in path.split("."):
                node_map = as_str_object_dict(node, f"{sid}: json path {path!r}")
                assert part in node_map, f"{sid}: json path {path!r}: key {part!r} missing"
                node = node_map[part]
            assert node == expected, (
                f"{sid}: json pin {path!r}: expected {expected!r}, got {node!r}"
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


@pytest.mark.parametrize("scenario", _SCENARIOS, ids=_SCENARIO_IDS)
def test_scenario(cli: CliUnderTest, scenario: dict[str, object], cli_env: dict[str, str]) -> None:
    """Every contract scenario holds on every CLI (exit code, streams, JSON)."""
    sid = _scenario_str(scenario, "id")
    fixture_path = _resolve_fixture(scenario)
    args = _str_list(_effective(scenario, cli.name, "args"), f"{sid}.args")
    argv = [
        *cli.argv,
        _scenario_str(scenario, "subcommand"),
        *(arg.replace("{dbc}", str(fixture_path)) for arg in args),
    ]
    result = _run_cli(argv, cli_env)

    expect = as_str_object_dict(_effective(scenario, cli.name, "expect"), f"{sid}.expect")
    expected_exit: object = expect.get("exit")
    assert isinstance(expected_exit, int), f"{sid}.expect.exit must be an int"
    assert result.returncode == expected_exit, (
        f"{sid} on {cli.name}: expected exit {expected_exit}\n{_failure_report(argv, result)}"
    )
    if "stdout_contains" in expect:
        for needle in _str_list(expect["stdout_contains"], f"{sid}.expect.stdout_contains"):
            assert needle in result.stdout, (
                f"{sid} on {cli.name}: stdout missing {needle!r}\n{_failure_report(argv, result)}"
            )
    if "stderr_contains" in expect:
        for needle in _str_list(expect["stderr_contains"], f"{sid}.expect.stderr_contains"):
            assert needle in result.stderr, (
                f"{sid} on {cli.name}: stderr missing {needle!r}\n{_failure_report(argv, result)}"
            )
    if "json" in expect:
        pins = as_str_object_dict(expect["json"], f"{sid}.expect.json")
        _assert_json_pins(result.stdout, pins, f"{sid} on {cli.name}")


# ---------------------------------------------------------------------------
# Subcommand-coverage tripwire
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("subcommand", _SUBCOMMANDS)
def test_every_subcommand_has_a_scenario(subcommand: str) -> None:
    """Each declared subcommand carries at least one contract scenario."""
    covered = {_scenario_str(s, "subcommand") for s in _SCENARIOS}
    assert subcommand in covered, (
        f"meta.subcommands entry {subcommand!r} has no scenario in CLI_SCENARIOS.yaml — "
        "a subcommand without a scenario is invisible to the parity harness"
    )


def test_scenario_subcommands_are_declared() -> None:
    """No scenario names a subcommand outside meta.subcommands (typo guard)."""
    for scenario in _SCENARIOS:
        sub = _scenario_str(scenario, "subcommand")
        assert sub in _SUBCOMMANDS, (
            f"scenario {_scenario_str(scenario, 'id')!r} uses undeclared subcommand {sub!r}"
        )


def test_scenario_ids_unique() -> None:
    """Scenario ids are unique (they key test parametrization)."""
    assert len(set(_SCENARIO_IDS)) == len(_SCENARIO_IDS), (
        f"duplicate scenario ids in CLI_SCENARIOS.yaml: {sorted(_SCENARIO_IDS)}"
    )


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
