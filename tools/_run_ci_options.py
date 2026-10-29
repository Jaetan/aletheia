# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The offline CI sweep's command line: its options and the opt-in lanes they enable.

``tools/run_ci.py`` documents the options and reads them through
:func:`parse_args`; each opt-in lane is enabled by its flag or its environment
variable, the flag winning.
"""

from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from typing import NewType

# A lane's name, as a step registers into it (``Step.lane``), and the text
# ``--lanes`` takes: lane names separated by commas.
LaneName = NewType("LaneName", str)
LaneSpec = NewType("LaneSpec", str)


@dataclass
class OptInLanes:
    """The opt-in lanes, each adding its steps to the sweep when enabled."""

    repro: bool
    stability: bool
    mutation: bool
    coverage: bool


@dataclass
class OptInOptions:
    """Resolved opt-in state.  CLI > env > default-off precedence."""

    lanes: OptInLanes
    # Mode flag, NOT a timing lane: switches the IWYU gate (step 9) from
    # `--diff` (branch-scoped, fast — local pre-push-hook parity) to `--all`
    # (whole-tree, airtight against cross-file deadness — the server-side
    # merge gate).  It adds no step and does not change total_steps.
    iwyu_all: bool = False
    # Lane-parallel gate execution + the heavy-step concurrency cap.  Default
    # serial (run_lanes executor=None): exit-code-identical to today.  --parallel
    # opts into the lane scheduler; heavy_limit bounds concurrent big-memory
    # steps (the OOM guard) and is only consulted in parallel mode.
    parallel: bool = False
    heavy_limit: int = 2
    # Build-staleness scheduling (see tools/_ci_steps should_run_staleness):
    # "auto" (default) registers the staleness gate's step
    # (check_build_incremental, ~2 .so relinks) only when a build-graph file
    # changed; "always" is the push:main backstop, "never" an escape hatch.
    # Not a lane — it adds the one step.
    build_staleness: str = "auto"
    # Pre-commit FAST tier: restrict the sweep to the compile-free static gates
    # (tools._ci_steps.FAST_STEPS) and skip the `build` prereq.  Used by the
    # pre-commit hook to block non-conforming commits in seconds; pre-push still
    # runs the full sweep.  A no-op subset filter, so it never changes a step's
    # command — no gate drift between commit-time and push-time definitions.
    fast: bool = False
    # Run only these lanes, and the `build` prereq they all need: how the
    # full-CI workflow spreads one sweep over two runners.  Empty runs every
    # lane.  Like the fast tier, a subset filter that never alters a step's
    # command, and a subset sweep vouches for no build-source digest, since it
    # is no evidence that every gate observed the tree.
    only_lanes: tuple[LaneName, ...] = ()


def _lane_list(spec: LaneSpec) -> tuple[LaneName, ...] | None:
    """Read ``--lanes``: its lane names, or None where one of them is empty."""
    names = tuple(LaneName(name.strip()) for name in spec.split(","))
    return names if all(names) else None


def _resolve_flag(*, cli_value: bool | None, env_var: str) -> bool:
    """Resolve a tri-state CLI flag against an env-var fallback.

    The flag is ``--lane`` / ``--no-lane`` / unset; returns True iff the lane
    should run.
    """
    if cli_value is not None:
        return cli_value
    return os.environ.get(env_var) == "1"


def _resolve_heavy_limit(cli_value: int | None) -> int:
    """Resolve the OOM heavy-step limit: CLI > env > default, clamped to >= 1.

    A non-integer ``ALETHEIA_CI_HEAVY_LIMIT`` falls back to the default rather
    than crashing the sweep, and a non-positive value is clamped to 1 so the
    startup banner and the scheduler's ``Semaphore(max(1, n))`` agree on the
    effective limit (no misleading "heavy-limit 0").
    """
    default = 2
    if cli_value is not None:
        return max(1, cli_value)
    try:
        return max(1, int(os.environ.get("ALETHEIA_CI_HEAVY_LIMIT", str(default))))
    except ValueError:
        return default


_BUILD_STALENESS_MODES = ("auto", "always", "never")


def _resolve_build_staleness(cli_value: str | None) -> str:
    """Resolve build-staleness mode: CLI > env > "auto" default; invalid env → "auto"."""
    if cli_value in _BUILD_STALENESS_MODES:
        return cli_value
    env = os.environ.get("ALETHEIA_BUILD_STALENESS")
    return env if env in _BUILD_STALENESS_MODES else "auto"


def parse_args(argv: list[str] | None = None) -> OptInOptions:
    """Parse argv into resolved opt-in lane state (CLI > env > default-off)."""
    parser = argparse.ArgumentParser(
        prog="tools/run_ci.py",
        description="Offline CI orchestrator.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Opt-in lanes can be enabled via CLI flags, env vars, or `--full`.\n"
            "CLI flags override env vars; env vars override the default (off).\n"
            "\n"
            "Examples:\n"
            "  tools/run_ci.py                       # always-on steps only "
            "(incl. UBSan; ~22-27 min)\n"
            "  tools/run_ci.py --full                # everything (45-85 min)\n"
            "  tools/run_ci.py --stability --repro   # two specific opt-in lanes\n"
            "  tools/run_ci.py --full --no-mutation  # all opt-ins except mutation\n"
            "  ALETHEIA_REPRO_CHECK=1 tools/run_ci.py  # legacy env-var trigger\n"
            "\n"
            "See also docs/development/CI_LOCAL.md.\n"
        ),
    )

    def _add_lane(flag: str, env: str, help_msg: str) -> None:
        # argparse `--name / --no-name` pattern: action=BooleanOptionalAction
        # gives us both forms with paired help + None-default for "not set".
        parser.add_argument(
            f"--{flag}",
            action=argparse.BooleanOptionalAction,
            default=None,
            help=f"{help_msg} (env: {env}=1)",
        )

    _add_lane(
        "repro",
        "ALETHEIA_REPRO_CHECK",
        "reproducible-build hash gate (~10 min cold)",
    )
    _add_lane(
        "stability",
        "ALETHEIA_STABILITY_CHECK",
        "long-run stability bench (~5 min cold)",
    )
    _add_lane(
        "mutation",
        "ALETHEIA_MUTATION_CHECK",
        "mutation testing across 3 bindings (~30 min+)",
    )
    _add_lane(
        "coverage",
        "ALETHEIA_COVERAGE_CHECK",
        "coverage floors across 4 bindings (~3 min)",
    )

    parser.add_argument(
        "--full",
        action="store_true",
        help=(
            "Enable every opt-in lane (equivalent to --repro --stability "
            "--mutation --coverage).  Individual --no-<lane> flags can still subtract from "
            "the --full set (e.g. --full --no-mutation runs everything except "
            "mutation testing)."
        ),
    )

    parser.add_argument(
        "--iwyu-all",
        action="store_true",
        default=False,
        help=(
            "Run the IWYU import gate (step 9) over the WHOLE tree (`--all`) "
            "instead of the branch diff (`--diff`).  Airtight against "
            "cross-file deadness; this is what the server-side PR merge gate "
            "uses.  (env: ALETHEIA_IWYU_ALL=1)"
        ),
    )

    parser.add_argument(
        "--fast",
        action="store_true",
        default=False,
        help=(
            "Pre-commit FAST tier: run ONLY the compile-free static gates "
            "(format checks, SPDX/review-mark/venv hygiene, ruff, pylint) and "
            "skip the build prereq.  Seconds, not minutes; no build artifacts "
            "needed.  Used by the pre-commit hook; a push asks for a full sweep."
        ),
    )
    parser.add_argument(
        "--parallel",
        action=argparse.BooleanOptionalAction,
        default=None,
        help=(
            "Run independent toolchain lanes concurrently (Agda / Python / Go / "
            "C++ / Rust / meta) rather than serially.  Default off — serial is "
            "exit-code-identical to the historic sweep.  (env: ALETHEIA_CI_PARALLEL=1)"
        ),
    )
    parser.add_argument(
        "--ci-heavy-limit",
        type=int,
        default=None,
        help=(
            "Max big-memory steps run at once in --parallel mode (the OOM guard); "
            "default 2.  (env: ALETHEIA_CI_HEAVY_LIMIT)"
        ),
    )
    parser.add_argument(
        "--build-staleness",
        choices=_BUILD_STALENESS_MODES,
        default=None,
        help=(
            "When the sweep runs the staleness gate (check_build_incremental, "
            "~2 .so relinks) as a step of its own after the lanes.  `auto` (default) runs it "
            "only when the diff vs `main` touches a build-graph file (Shakefile.hs, "
            "shake/, shake.cabal, aletheia.agda-lib, the haskell-shim/, "
            "tools/check_build_incremental.py, tools/_warm.py); `always` is the "
            "push:main backstop, `never` an escape hatch.  (env: ALETHEIA_BUILD_STALENESS)"
        ),
    )

    parser.add_argument(
        "--lanes",
        default=None,
        help=(
            "Run only the named lanes (comma-separated, e.g. cpp,ubsan,asan) and the "
            "build prereq; an unknown lane name is refused.  How full CI spreads the "
            "sweep over two runners; a subset sweep vouches for no build-source digest."
        ),
    )
    args = parser.parse_args(argv)
    only_lanes = () if args.lanes is None else _lane_list(LaneSpec(args.lanes))
    if only_lanes is None:
        parser.error(f"--lanes takes comma-separated lane names, got {args.lanes!r}")

    # --full sets every unset CLI flag to True; explicit --no-<lane> keeps False.
    # The order matters: apply --full BEFORE _resolve_flag so the env var still
    # gets to enable a lane that --full + --no-<other> didn't touch.
    if args.full:
        for lane in ("repro", "stability", "mutation", "coverage"):
            if getattr(args, lane) is None:
                setattr(args, lane, True)

    return OptInOptions(
        lanes=OptInLanes(
            repro=_resolve_flag(cli_value=args.repro, env_var="ALETHEIA_REPRO_CHECK"),
            stability=_resolve_flag(cli_value=args.stability, env_var="ALETHEIA_STABILITY_CHECK"),
            mutation=_resolve_flag(cli_value=args.mutation, env_var="ALETHEIA_MUTATION_CHECK"),
            coverage=_resolve_flag(cli_value=args.coverage, env_var="ALETHEIA_COVERAGE_CHECK"),
        ),
        iwyu_all=args.iwyu_all or os.environ.get("ALETHEIA_IWYU_ALL") == "1",
        parallel=_resolve_flag(cli_value=args.parallel, env_var="ALETHEIA_CI_PARALLEL"),
        heavy_limit=_resolve_heavy_limit(args.ci_heavy_limit),
        build_staleness=_resolve_build_staleness(args.build_staleness),
        fast=args.fast or os.environ.get("ALETHEIA_CI_FAST") == "1",
        only_lanes=only_lanes,
    )
