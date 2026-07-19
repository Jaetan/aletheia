# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Real-workflow validation of a release bundle across the compiled bindings.

Unpacks a distribution tarball (``cabal run shake -- dist``), runs its
installers CAPTURING the printed integration recipes, and then EXECUTES those
exact recipe lines to build one small consumer program per compiled binding
(C++, Go, Rust).  Each consumer drives the same scenario the release workflow's
smoke test proves for Python — env-constructor (the ``ALETHEIA_LIB`` seam set
by ``env.sh``/``env.fish``) → ``parse_dbc_text`` of a real ``.dbc`` →
``set_properties`` with an LTL property → ``start_stream`` → a conforming and
a violating frame → exactly one violation on the expected property →
``end_stream``.  A REAL workflow through the verified kernel from the shipped
artifact, not a load check.

The recipes users read are the recipes this tool runs: the per-language blocks
are extracted from the captured installer output, never re-typed here, so an
installer edit that breaks a recipe fails this gate instead of drifting past
it.  Both installers run whenever both shells are present and their
per-language recipe blocks must be IDENTICAL, and ``env.sh``/``env.fish`` are
each sourced from a foreign cwd and must agree on an ABSOLUTE ``ALETHEIA_LIB``
— the multi-shell divergence class the v4.0.0 review caught by hand.

A binding whose toolchain is absent is skipped with a precise error locally
(mirroring ``tools/mutation_run.py``); ``--require`` turns those skips into
failures for CI.

``--self-test`` proves the gate has teeth: it corrupts a COPY of the bundle
several ways (deleting the shared library, dropping the Go module file,
truncating the Rust crate root) and asserts each corrupted bundle FAILS
validation — a gate that cannot fail has a bug.

The heavy end-to-end path (unpack, CMake/go/cargo consumer builds, GHC RTS
startup) lives here in the tool rather than in pytest: it needs a built
bundle, the per-binding language toolchains, and network access for the C++
FetchContent configure step, so it runs as an explicit gate invocation.  The
pure logic (recipe extraction, shape checks, CLI parsing, corruption
plumbing) is unit-tested in ``python/tests/test_bundle_validate.py``.

Usage:
  python3 -m tools.bundle_validate dist/aletheia.tar.gz --require cpp,go,rust
  python3 -m tools.bundle_validate dist/aletheia.tar.gz --shell fish
  python3 -m tools.bundle_validate dist/aletheia.tar.gz --self-test
"""

from __future__ import annotations

import argparse
import os
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import emit, find_executable

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_DIR = REPO_ROOT / "tools" / "bundle_validation"
DEFAULT_DBC = REPO_ROOT / "examples" / "demo" / "vehicle.dbc"

# The consumer bindings this tool can drive, in run order.
BINDINGS: tuple[str, ...] = ("cpp", "go", "rust")

# Directory name at the root of the distribution tarball.
BUNDLE_DIR_NAME = "aletheia"

# Trailing characters of combined child output kept in a failure message.
OUTPUT_TAIL_CHARS = 2000

# Characters of the Rust crate root kept by the self-test truncation — enough
# to leave a syntactically broken torso, far too few for a working crate.
_TRUNCATE_KEEP_CHARS = 200

# Placeholder in the Rust consumer's Cargo.toml template that receives the
# [dependencies] block printed by the installer, verbatim.
_DEPENDENCIES_PLACEHOLDER = "@ALETHEIA_DEPENDENCIES@"

# installer + env script per supported shell.
_SHELL_FILES: dict[str, tuple[str, str]] = {
    "bash": ("install.sh", "env.sh"),
    "fish": ("install.fish", "env.fish"),
}

# Start of each binding's recipe-section header line as the installers print
# it (the header continues with a parenthesised toolchain note).
_RECIPE_HEADERS: dict[str, str] = {"cpp": "C++", "go": "Go", "rust": "Rust"}

# Shape contract for each extracted recipe block: one prefix per expected
# line, in order.  A block that deviates fails validation before anything is
# executed — the shape check is what makes "execute the emitted text" safe.
_RECIPE_SHAPES: dict[str, tuple[str, ...]] = {
    "cpp": ('add_subdirectory("', "target_link_libraries(your_app "),
    "go": ("go mod edit -replace ", "go get "),
    "rust": ("[dependencies]", "aletheia = { path = "),
}


class BundleValidationError(Exception):
    """A validation step failed; the message names the step and carries output."""


@dataclass(frozen=True)
class Config:
    """One validation run's inputs, as parsed from the CLI."""

    tarball: Path
    bindings: tuple[str, ...]
    require: frozenset[str]
    shell: str
    dbc: Path
    keep_work: bool = False
    fetchcontent_cache: Path | None = None


@dataclass(frozen=True)
class ConsumerOutcome:
    """How one binding's consumer fared: ran to success, or skipped and why."""

    binding: str
    status: str  # "ok" | "skip"
    detail: str = ""


# ── Recipe extraction (pure logic; unit-tested) ─────────────────────────────


def extract_recipes(installer_output: str) -> dict[str, list[str]]:
    """Extract the per-language recipe blocks from captured installer output.

    The installers print each language section as a header line (e.g. one
    beginning ``C++  (``) followed by indented recipe lines, terminated by a
    blank line.  Comment lines (leading ``#``) are advisory prose, not part
    of the executable recipe, and are dropped.
    """
    recipes: dict[str, list[str]] = {}
    lines = installer_output.splitlines()
    index = 0
    while index < len(lines):
        binding = _match_header(lines[index])
        if binding is None:
            index += 1
            continue
        block: list[str] = []
        index += 1
        while index < len(lines) and lines[index].strip():
            entry = lines[index].strip()
            if not entry.startswith("#"):
                block.append(entry)
            index += 1
        recipes[binding] = block
    return recipes


def _match_header(line: str) -> str | None:
    """Return the binding whose recipe-section header ``line`` is, if any."""
    stripped = line.strip()
    for binding, title in _RECIPE_HEADERS.items():
        if stripped.startswith(title + "  ("):
            return binding
    return None


def recipe_shape_errors(recipes: dict[str, list[str]]) -> list[str]:
    """Check each extracted block against its shape contract; return problems."""
    problems: list[str] = []
    for binding, prefixes in _RECIPE_SHAPES.items():
        block = recipes.get(binding)
        if block is None:
            problems.append(f"{binding}: recipe block not found in the installer output")
            continue
        if len(block) != len(prefixes):
            problems.append(
                f"{binding}: expected {len(prefixes)} recipe lines, got {len(block)}: {block}"
            )
            continue
        for line, prefix in zip(block, prefixes, strict=True):
            if not line.startswith(prefix):
                problems.append(f"{binding}: recipe line {line!r} does not start with {prefix!r}")
    return problems


# ── Step execution ──────────────────────────────────────────────────────────


def _run_step(
    name: str,
    argv: list[str],
    *,
    cwd: Path | None = None,
    env: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run one external step, emit its timing, and fail loudly on non-zero exit."""
    started = time.monotonic()
    proc = subprocess.run(argv, capture_output=True, text=True, cwd=cwd, env=env, check=False)
    elapsed = time.monotonic() - started
    if proc.returncode != 0:
        tail = (proc.stdout + proc.stderr)[-OUTPUT_TAIL_CHARS:]
        message = f"{name} failed (exit {proc.returncode}):\n{tail}"
        raise BundleValidationError(message)
    emit(f"[bundle] {name}: ok ({elapsed:.1f}s)")
    return proc


def _available_shells() -> tuple[str, ...]:
    """Return the supported shells present on this host (bash is mandatory)."""
    return tuple(shell for shell in _SHELL_FILES if shutil.which(shell) is not None)


# ── Installer + environment scripts ─────────────────────────────────────────


def run_installer(bundle: Path, shell: str) -> str:
    """Run the bundle's installer for ``shell``, returning its captured stdout."""
    installer, _ = _SHELL_FILES[shell]
    proc = _run_step(installer, [find_executable(shell), str(bundle / installer)])
    return proc.stdout


def source_env(bundle: Path, shell: str) -> Path:
    """Source the env script from a foreign cwd; return the ALETHEIA_LIB path.

    Fails unless the exported value is an ABSOLUTE path to an existing file —
    the property that makes the bundle usable from any directory.
    """
    _, env_file = _SHELL_FILES[shell]
    target = shlex.quote(str(bundle / env_file))
    if shell == "bash":
        script = f'cd / && source {target} && printf %s "$ALETHEIA_LIB"'
    else:
        script = f"cd /; source {target}; printf %s $ALETHEIA_LIB"
    proc = _run_step(f"{env_file} (foreign cwd)", [find_executable(shell), "-c", script])
    value = proc.stdout.strip()
    if not value.startswith("/"):
        message = f"{env_file}: ALETHEIA_LIB is not absolute: {value!r}"
        raise BundleValidationError(message)
    lib = Path(value)
    if not lib.is_file():
        message = f"{env_file}: ALETHEIA_LIB does not name a file: {value}"
        raise BundleValidationError(message)
    return lib


def _installer_recipes(bundle: Path, shell: str) -> dict[str, list[str]]:
    """Run every available installer, check parity, return ``shell``'s recipes."""
    shells = _available_shells()
    outputs = {name: run_installer(bundle, name) for name in shells}
    extracted = {name: extract_recipes(output) for name, output in outputs.items()}
    problems = recipe_shape_errors(extracted[shell])
    if "fish" in extracted and "bash" in extracted:
        problems.extend(parity_problems(extracted["bash"], extracted["fish"]))
        emit("[bundle] recipes: install.sh / install.fish parity checked")
    else:
        emit("[bundle] fish not in PATH — installer parity leg skipped")
    if problems:
        message = "installer recipe problems:\n" + "\n".join(problems)
        raise BundleValidationError(message)
    return extracted[shell]


def parity_problems(
    bash_recipes: dict[str, list[str]], fish_recipes: dict[str, list[str]]
) -> list[str]:
    """Diff both installers' per-language recipe blocks (must be identical)."""
    return [
        f"{binding}: install.sh and install.fish print different recipes: "
        + f"{bash_recipes.get(binding)} vs {fish_recipes.get(binding)}"
        for binding in _RECIPE_SHAPES
        if bash_recipes.get(binding) != fish_recipes.get(binding)
    ]


def _resolve_lib(bundle: Path, shell: str) -> Path:
    """Source every available env script; all must agree on ALETHEIA_LIB."""
    shells = _available_shells()
    libs = {name: source_env(bundle, name) for name in shells}
    if len(set(libs.values())) > 1:
        message = f"env scripts disagree on ALETHEIA_LIB: {libs}"
        raise BundleValidationError(message)
    return libs[shell]


# ── Consumers ───────────────────────────────────────────────────────────────


# Per-binding toolchain prerequisites: (executable, precise-skip message).
_TOOL_REQUIREMENTS: dict[str, tuple[tuple[str, str], ...]] = {
    "cpp": (
        ("cmake", "cmake not in PATH; install CMake 3.25+"),
        ("clang++-22", "clang++-22 not in PATH; the bundled C++ binding is Clang-only"),
    ),
    "go": (("go", "go not in PATH; install the Go toolchain"),),
    "rust": (("cargo", "cargo not in PATH; install the Rust toolchain"),),
}


def missing_tool(binding: str) -> str | None:
    """Name the missing toolchain piece for ``binding``, or None when runnable."""
    for tool, message in _TOOL_REQUIREMENTS[binding]:
        if shutil.which(tool) is None:
            return message
    return None


def _consumer_env(lib: Path) -> dict[str, str]:
    """Child-process environment with the resolved ALETHEIA_LIB exported."""
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(lib)
    return env


def assert_consumer_ok(binding: str, stdout: str) -> None:
    """Verify the consumer by its summary line, not its exit code alone."""
    marker = f"BUNDLE-CONSUMER {binding}: OK"
    if marker not in stdout:
        message = f"{binding}: consumer exited zero but did not print {marker!r}"
        raise BundleValidationError(message)


def run_cpp_consumer(work: Path, recipe: list[str], lib: Path, cfg: Config) -> None:
    """Build + run the C++ consumer via the printed CMake recipe lines."""
    src = work / "consumer_cpp"
    _ = shutil.copytree(FIXTURE_DIR / "consumer_cpp", src)
    recipe_file = src / "recipe.cmake"
    _ = recipe_file.write_text("\n".join(recipe) + "\n")
    build = src / "build"
    cmake = find_executable("cmake")
    configure = [
        cmake,
        "-S",
        str(src),
        "-B",
        str(build),
        "-DCMAKE_BUILD_TYPE=Release",
        "-DCMAKE_CXX_COMPILER=clang++-22",
        f"-DALETHEIA_RECIPE_CMAKE={recipe_file}",
    ]
    if cfg.fetchcontent_cache is not None:
        configure.append(f"-DFETCHCONTENT_BASE_DIR={cfg.fetchcontent_cache.resolve()}")
    _ = _run_step("cpp: cmake configure", configure)
    jobs = str(os.cpu_count() or 1)
    build_cmd = [cmake, "--build", str(build), "--parallel", jobs, "--target", "your_app"]
    _ = _run_step("cpp: cmake build", build_cmd)
    scenario = _run_step(
        "cpp: scenario", [str(build / "your_app"), str(cfg.dbc)], env=_consumer_env(lib)
    )
    assert_consumer_ok("cpp", scenario.stdout)


def run_go_consumer(work: Path, recipe: list[str], lib: Path, cfg: Config) -> None:
    """Build + run the Go consumer via the printed go recipe lines, verbatim."""
    src = work / "consumer_go"
    src.mkdir()
    _ = shutil.copy(FIXTURE_DIR / "consumer_go" / "main.go", src / "main.go")
    go = find_executable("go")
    env = _consumer_env(lib)
    env["CGO_ENABLED"] = "1"
    _ = _run_step("go: mod init", [go, "mod", "init", "consumer"], cwd=src, env=env)
    for line in recipe:
        argv = shlex.split(line)
        argv[0] = go  # the shape check pinned the leading word; resolve it on PATH
        _ = _run_step(f"go: {line}", argv, cwd=src, env=env)
    _ = _run_step("go: build", [go, "build", "-o", "consumer", "."], cwd=src, env=env)
    scenario = _run_step("go: scenario", [str(src / "consumer"), str(cfg.dbc)], env=env)
    assert_consumer_ok("go", scenario.stdout)


def run_rust_consumer(work: Path, recipe: list[str], lib: Path, cfg: Config) -> None:
    """Build + run the Rust consumer with the printed [dependencies] block."""
    src = work / "consumer_rust"
    (src / "src").mkdir(parents=True)
    template = (FIXTURE_DIR / "consumer_rust" / "Cargo.toml.in").read_text()
    if template.count(_DEPENDENCIES_PLACEHOLDER) != 1:
        message = (
            f"Cargo.toml.in must contain the {_DEPENDENCIES_PLACEHOLDER} placeholder exactly "
            + "once (a stray occurrence — e.g. in a comment — would also be substituted)"
        )
        raise BundleValidationError(message)
    manifest = template.replace(_DEPENDENCIES_PLACEHOLDER, "\n".join(recipe))
    _ = (src / "Cargo.toml").write_text(manifest)
    _ = shutil.copy(FIXTURE_DIR / "consumer_rust" / "src" / "main.rs", src / "src" / "main.rs")
    cargo = find_executable("cargo")
    env = _consumer_env(lib)
    _ = _run_step("rust: cargo build", [cargo, "build"], cwd=src, env=env)
    scenario_bin = src / "target" / "debug" / "consumer"
    scenario = _run_step("rust: scenario", [str(scenario_bin), str(cfg.dbc)], env=env)
    assert_consumer_ok("rust", scenario.stdout)


_CONSUMER_RUNNERS: dict[str, Callable[[Path, list[str], Path, Config], None]] = {
    "cpp": run_cpp_consumer,
    "go": run_go_consumer,
    "rust": run_rust_consumer,
}


def _run_consumers(
    cfg: Config, work: Path, recipes: dict[str, list[str]], lib: Path
) -> list[ConsumerOutcome]:
    """Run each selected consumer; skip-with-reason on a missing toolchain."""
    outcomes: list[ConsumerOutcome] = []
    for binding in cfg.bindings:
        problem = missing_tool(binding)
        if problem is not None:
            if binding in cfg.require:
                message = f"{binding} is required but its toolchain is missing: {problem}"
                raise BundleValidationError(message)
            emit(f"[bundle] skip {binding}: {problem}")
            outcomes.append(ConsumerOutcome(binding, "skip", problem))
            continue
        _CONSUMER_RUNNERS[binding](work, recipes[binding], lib, cfg)
        outcomes.append(ConsumerOutcome(binding, "ok"))
    return outcomes


# ── Validation flow ─────────────────────────────────────────────────────────


def _unpack(tarball: Path, work: Path) -> Path:
    """Unpack the distribution tarball into ``work``; return the bundle root."""
    with tarfile.open(tarball, "r:gz") as archive:
        archive.extractall(work, filter="data")
    bundle = work / BUNDLE_DIR_NAME
    if not bundle.is_dir():
        message = f"tarball did not unpack to a {BUNDLE_DIR_NAME}/ directory: {tarball}"
        raise BundleValidationError(message)
    return bundle


def _validate_in(cfg: Config, work: Path) -> list[ConsumerOutcome]:
    """Unpack, run installers + env scripts, then drive the consumers."""
    bundle = _unpack(cfg.tarball, work)
    if cfg.shell not in _available_shells():
        message = f"--shell {cfg.shell} requested but {cfg.shell} is not in PATH"
        raise BundleValidationError(message)
    recipes = _installer_recipes(bundle, cfg.shell)
    lib = _resolve_lib(bundle, cfg.shell)
    return _run_consumers(cfg, work, recipes, lib)


def validate(cfg: Config) -> int:
    """Run the full bundle validation; return the process exit code."""
    if not cfg.tarball.is_file():
        emit(f"bundle validation: FAIL — tarball not found: {cfg.tarball}")
        return 1
    if not cfg.dbc.is_file():
        emit(f"bundle validation: FAIL — scenario DBC not found: {cfg.dbc}")
        return 1
    work = Path(tempfile.mkdtemp(prefix="aletheia-bundle-"))
    try:
        outcomes = _validate_in(cfg, work)
    except BundleValidationError as error:
        emit(f"bundle validation: FAIL — {error}")
        return 1
    else:
        summary = ", ".join(
            outcome.binding + (" ok" if outcome.status == "ok" else f" skip ({outcome.detail})")
            for outcome in outcomes
        )
        emit(f"bundle validation: PASS — {summary or 'no consumers selected'}")
        return 0
    finally:
        if cfg.keep_work:
            emit(f"[bundle] work tree kept at {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)


# ── Self-test (the gate's teeth) ────────────────────────────────────────────


def corrupt_missing_so(bundle: Path) -> None:
    """Delete the shared library — the installers must refuse the bundle."""
    (bundle / "lib" / "libaletheia-ffi.so").unlink()


def corrupt_go_mod(bundle: Path) -> None:
    """Drop the Go module file — the printed go recipe must stop resolving."""
    (bundle / "bindings" / "go" / "go.mod").unlink()


def corrupt_rust_lib(bundle: Path) -> None:
    """Truncate the Rust crate root — the consumer build must break."""
    lib_rs = bundle / "bindings" / "rust" / "src" / "lib.rs"
    _ = lib_rs.write_text(lib_rs.read_text()[:_TRUNCATE_KEEP_CHARS])


# Each case scopes validation to the binding(s) that must catch the damage —
# required, so a toolchain skip can never mask a corruption going undetected.
# The missing-so case is caught by the installers before any consumer runs;
# it is scoped to the cheapest consumer only to keep the case fast.
_SELF_TEST_CASES: tuple[tuple[str, Callable[[Path], None], tuple[str, ...]], ...] = (
    ("missing-so", corrupt_missing_so, ("go",)),
    ("go-mod-dropped", corrupt_go_mod, ("go",)),
    ("rust-lib-truncated", corrupt_rust_lib, ("rust",)),
)


def _run_corruption(
    cfg: Config, name: str, corrupt: Callable[[Path], None], bindings: tuple[str, ...]
) -> int:
    """Corrupt a copy of the bundle, re-pack it, and validate the copy."""
    with tempfile.TemporaryDirectory(prefix="aletheia-selftest-") as tmp:
        tmp_path = Path(tmp)
        bundle = _unpack(cfg.tarball, tmp_path)
        corrupt(bundle)
        corrupted = tmp_path / f"corrupted-{name}.tar.gz"
        with tarfile.open(corrupted, "w:gz") as archive:
            archive.add(bundle, arcname=BUNDLE_DIR_NAME)
        scoped = Config(
            tarball=corrupted,
            bindings=bindings,
            require=frozenset(bindings),
            shell=cfg.shell,
            dbc=cfg.dbc,
            keep_work=False,
            fetchcontent_cache=cfg.fetchcontent_cache,
        )
        return validate(scoped)


def self_test(cfg: Config) -> int:
    """Prove the gate can fail: every corrupted bundle must FAIL validation."""
    if not cfg.tarball.is_file():
        emit(f"bundle validator self-test: FAIL — tarball not found: {cfg.tarball}")
        return 1
    survived: list[str] = []
    for name, corrupt, bindings in _SELF_TEST_CASES:
        blockers = [
            f"{binding}: {problem}"
            for binding in bindings
            if (problem := missing_tool(binding)) is not None
        ]
        if blockers:
            # Without the scoped toolchain the run would fail at the require
            # check, not because the corruption was caught — a misleading
            # teeth-proof.  Skip visibly instead (CI has every toolchain).
            emit(f"[self-test] skip {name}: {'; '.join(blockers)}")
            continue
        emit(f"[self-test] {name}: corrupting a copy of the bundle")
        returncode = _run_corruption(cfg, name, corrupt, bindings)
        if returncode == 0:
            survived.append(name)
            emit(f"[self-test] {name}: BUG — the corrupted bundle PASSED validation")
        else:
            emit(f"[self-test] {name}: ok (validation failed as it must)")
    if survived:
        emit(f"bundle validator self-test: FAIL — corruptions survived: {', '.join(survived)}")
        return 1
    emit("bundle validator self-test: PASS — every corruption failed validation")
    return 0


# ── CLI ─────────────────────────────────────────────────────────────────────


def _parse_binding_list(parser: argparse.ArgumentParser, flag: str, raw: str) -> tuple[str, ...]:
    """Parse a comma-separated binding list, normalized to BINDINGS order."""
    names = [name for name in (part.strip() for part in raw.split(",")) if name]
    unknown = [name for name in names if name not in BINDINGS]
    if unknown:
        parser.error(
            f"{flag}: unknown binding(s) {', '.join(unknown)}; valid: {', '.join(BINDINGS)}"
        )
    return tuple(name for name in BINDINGS if name in names)


def parse_args(argv: list[str] | None = None) -> tuple[Config, bool]:
    """Parse the CLI into a Config plus the self-test flag."""
    parser = argparse.ArgumentParser(prog="bundle_validate", description=__doc__)
    parser.add_argument(
        "tarball", type=Path, help="distribution tarball built by `cabal run shake -- dist`"
    )
    parser.add_argument(
        "--bindings",
        default=",".join(BINDINGS),
        help="comma-separated consumers to run (default: all)",
    )
    parser.add_argument(
        "--require",
        default="",
        help="comma-separated bindings whose missing toolchain FAILS the run instead of skipping",
    )
    parser.add_argument(
        "--shell",
        choices=tuple(_SHELL_FILES),
        default="bash",
        help="which installer/env pair drives the consumer builds",
    )
    parser.add_argument(
        "--dbc", type=Path, default=DEFAULT_DBC, help="scenario .dbc file for the consumers"
    )
    parser.add_argument(
        "--keep-work", action="store_true", help="keep the temporary work tree for debugging"
    )
    parser.add_argument(
        "--fetchcontent-cache",
        type=Path,
        default=None,
        help="FETCHCONTENT_BASE_DIR for the C++ consumer configure (CI cache seam)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="corrupt copies of the bundle and assert each fails validation",
    )
    args = parser.parse_args(argv)
    cfg = Config(
        tarball=args.tarball,
        bindings=_parse_binding_list(parser, "--bindings", args.bindings),
        require=frozenset(_parse_binding_list(parser, "--require", args.require)),
        shell=args.shell,
        dbc=args.dbc,
        keep_work=args.keep_work,
        fetchcontent_cache=args.fetchcontent_cache,
    )
    return cfg, bool(args.self_test)


def main(argv: list[str] | None = None) -> int:
    """CLI entry point."""
    cfg, run_self_test = parse_args(argv)
    try:
        return self_test(cfg) if run_self_test else validate(cfg)
    except BundleValidationError as error:
        emit(f"bundle validation: FAIL — {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
