# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_dist_staging.py — always-on gate over the release bundle's staging inputs.

``cabal run shake -- dist`` stages each language binding into the release
bundle with ``git archive HEAD <pathspecs>`` (the ``stageBinding`` call sites
in ``Shakefile.hs``), copies the consumer entry scripts from ``packaging/``,
and ships ``LICENSE.md``.  All of that runs only at release time, so a broken
input — a renamed path, a dead exclude glob, an untracked script — used to
surface (or worse, NOT surface) only when a tag was cut.  This gate re-checks
the same inputs on every CI run and pre-commit (``git ls-files`` reads the
index, which is exactly the staged content the pre-commit FAST tier checks):

* every ``stageBinding`` positive pathspec must match at least one tracked
  file, else ``git archive`` would fail the release — that failure moves here,
  to PR time;
* every ``:(exclude)`` pathspec's INNER glob must also match tracked files.
  This is coverage ``git archive`` itself does not provide: empirically, git
  archive passes silently over a dead exclude, so if the Go test files moved,
  the exclude aimed at them would rot and they would silently ship in the
  bundle;
* ``go/go.work`` must not be selected by the go binding's pathspecs (it would
  hijack a consumer's Go module resolution).  The dist self-check inspects the
  packed output at release time; this front-runs it, always-on;
* the ``packaging/`` consumer entry scripts must be git-tracked and
  syntax-clean (``bash -n`` for the ``.sh`` pair, ``fish --no-execute`` for
  the ``.fish`` pair).  With ``GITHUB_ACTIONS`` set (or ``--require-fish``),
  a missing fish is a runner misconfiguration and fails closed; locally an
  absent fish skips only the ``.fish`` syntax checks, with a printed notice;
* ``LICENSE.md`` must be git-tracked (dist ships it with the bundle — BSD-2
  requires the notice to travel with redistributions).

The pathspec lists are parsed out of ``Shakefile.hs`` as literal Haskell
list-of-string arguments.  The parse fails CLOSED: an expected binding
missing, a call site not followed by a literal ``[...]`` list, a string using
Haskell escape/gap syntax (which this gate does not interpret), an
unterminated literal, or unknown pathspec magic all exit 2 rather than
checking a partial read; a quote-count cross-check additionally asserts that
every double-quoted literal inside each block was captured.

Exit codes:
  0 — all staging inputs resolve.
  1 — at least one broken input (dead pathspec, leaked go.work, untracked or
      syntax-broken packaging script), each named with a remedy.
  2 — could not check: unparseable Shakefile, missing input, or a required
      tool absent on a CI runner (a vacuous pass is refused).

Forward-revert verified 2026-07-19: pointing --shakefile at a doctored copy
(renamed positive path / dead exclude glob / a go positive matching go.work)
exits 1 naming the pathspec, and a multiline-gap literal exits 2; the real
tree returns to exit 0.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path

from tools._common import emit, find_executable, run_capture

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SHAKEFILE = REPO_ROOT / "Shakefile.hs"

# The bindings the dist bundle ships; a stageBinding call site must exist for
# each (Shakefile.hs is the staging SSOT — adding a binding there extends this
# set in the same commit).
EXPECTED_BINDINGS: frozenset[str] = frozenset({"python", "cpp", "go", "rust"})

# The consumer entry scripts dist copies into the bundle root.
PACKAGING_SCRIPTS: tuple[str, ...] = (
    "packaging/env.sh",
    "packaging/env.fish",
    "packaging/install.sh",
    "packaging/install.fish",
)

LICENSE_FILE = "LICENSE.md"
GO_WORK = "go/go.work"

_EXCLUDE_PREFIX = ":(exclude)"

# A call site passes the binding name as a string literal; the local definition
# (`stageBinding name paths = do`) and its type signature carry no quoted
# argument, so this matches call sites only.
_CALL_SITE_RE = re.compile(r'stageBinding\s+"([^"\n]+)"')

COULD_NOT_CHECK = 2


class DistStagingError(Exception):
    """The staging inputs cannot be checked (unparseable / missing / misconfigured)."""


@dataclass(frozen=True)
class BindingSpec:
    """One ``stageBinding`` call site's parsed pathspec list."""

    name: str
    positives: tuple[str, ...]
    excludes: tuple[str, ...]  # inner globs, ``:(exclude)`` prefix stripped
    raw: tuple[str, ...]  # every literal as written (archive-order semantics)


def find_fish() -> str | None:
    """Locate the fish binary on PATH (module-level so tests can monkeypatch it)."""
    return shutil.which("fish")


def _skip_whitespace(text: str, start: int) -> int:
    """Return the index of the first non-whitespace character at or after ``start``."""
    i = start
    while i < len(text) and text[i] in " \t\r\n":
        i += 1
    return i


def _bracket_block(text: str, search_from: int, name: str) -> str:
    """Return the content of the literal ``[...]`` list following a call site.

    ``search_from`` is the index just past the binding-name literal.  Tracks
    string state so a bracket inside a pathspec cannot end the block early.
    Raises :class:`DistStagingError` when the next token is not ``[`` or the
    list never closes — either means the call site is no longer a literal
    list this gate can trust.
    """
    i = _skip_whitespace(text, search_from)
    if i >= len(text) or text[i] != "[":
        message = f'stageBinding "{name}" is not followed by a literal [pathspec, ...] list'
        raise DistStagingError(message)
    start = i
    depth = 0
    in_string = False
    while i < len(text):
        ch = text[i]
        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
        elif ch == '"':
            in_string = True
        elif ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return text[start + 1 : i]
        i += 1
    message = f'stageBinding "{name}": unbalanced [ ... ] pathspec list'
    raise DistStagingError(message)


def _scan_string_literals(block: str, name: str) -> list[str]:
    """Return every plain double-quoted string literal in ``block``, in order.

    Fails closed on any Haskell string syntax beyond plain literals: a
    backslash inside a string (escape or multiline gap) and an unterminated
    string both raise :class:`DistStagingError`, because the gate would
    otherwise check a misread pathspec.
    """
    literals: list[str] = []
    current: list[str] | None = None
    for ch in block:
        if current is None:
            if ch == '"':
                current = []
        elif ch == "\\":
            message = (
                f'stageBinding "{name}": a pathspec literal uses Haskell escape/gap '
                + "syntax, which this gate does not interpret — write it as a plain string"
            )
            raise DistStagingError(message)
        elif ch == '"':
            literals.append("".join(current))
            current = None
        else:
            current.append(ch)
    if current is not None:
        message = f'stageBinding "{name}": unterminated string literal in its pathspec list'
        raise DistStagingError(message)
    return literals


def _classify(name: str, literals: list[str]) -> BindingSpec:
    """Split one block's literals into positive pathspecs and exclude inner globs.

    Unknown pathspec magic and an empty positive set both raise — the former
    because the gate cannot model semantics it does not know, the latter
    because a binding staging nothing is a vacuous archive.
    """
    positives: list[str] = []
    excludes: list[str] = []
    for lit in literals:
        if lit.startswith(_EXCLUDE_PREFIX):
            inner = lit[len(_EXCLUDE_PREFIX) :]
            if not inner:
                message = f'stageBinding "{name}": empty :(exclude) pathspec'
                raise DistStagingError(message)
            excludes.append(inner)
        elif lit.startswith(":"):
            message = (
                f"stageBinding \"{name}\": unrecognised pathspec magic '{lit}' — "
                + "extend tools/check_dist_staging.py to model it"
            )
            raise DistStagingError(message)
        elif lit:
            positives.append(lit)
        else:
            message = f'stageBinding "{name}": empty pathspec literal'
            raise DistStagingError(message)
    if not positives:
        message = f'stageBinding "{name}" carries no positive pathspec — it would stage nothing'
        raise DistStagingError(message)
    return BindingSpec(
        name=name,
        positives=tuple(positives),
        excludes=tuple(excludes),
        raw=tuple(literals),
    )


def parse_stage_bindings(text: str) -> list[BindingSpec]:
    """Parse every ``stageBinding`` call site's pathspec list out of the Shakefile.

    Raises :class:`DistStagingError` when any expected binding is missing or
    any block cannot be read as a literal list of plain strings.  A
    quote-count cross-check per block asserts the scanner captured every
    double-quoted literal between the ``[`` and the ``]`` — an uncaptured
    literal means a partial parse, which must never be checked.
    """
    bindings: list[BindingSpec] = []
    for match in _CALL_SITE_RE.finditer(text):
        name = match.group(1)
        block = _bracket_block(text, match.end(), name)
        literals = _scan_string_literals(block, name)
        if block.count('"') != 2 * len(literals):
            message = (
                f'stageBinding "{name}": a string literal between its [ and ] escaped '
                + "the parser — refusing to check a partial pathspec list"
            )
            raise DistStagingError(message)
        bindings.append(_classify(name, literals))
    missing = EXPECTED_BINDINGS - {b.name for b in bindings}
    if missing:
        message = (
            f"expected stageBinding call sites not found for: {', '.join(sorted(missing))} "
            + "— the staging layout in Shakefile.hs changed; update this gate with it"
        )
        raise DistStagingError(message)
    return bindings


def git_ls_files(repo_root: Path, pathspecs: tuple[str, ...]) -> list[str]:
    """Return the tracked paths matching ``pathspecs`` (git pathspec semantics).

    Raises :class:`DistStagingError` when git itself errors (not-a-repo,
    invalid pathspec) — that is a could-not-check condition, distinct from an
    empty match.
    """
    result = run_capture(
        [find_executable("git"), "ls-files", "--", *pathspecs],
        cwd=repo_root,
    )
    if result.returncode != 0:
        message = (
            f"git ls-files failed for {list(pathspecs)} in {repo_root}: " + result.stderr.strip()
        )
        raise DistStagingError(message)
    return result.stdout.splitlines()


def check_pathspecs_resolve(repo_root: Path, bindings: list[BindingSpec]) -> list[str]:
    """Return a failure per pathspec (positive or exclude-inner) matching nothing."""
    failures: list[str] = []
    for binding in bindings:
        failures.extend(
            f"binding '{binding.name}': positive pathspec '{spec}' matches no "
            + "tracked file — git archive would fail at release time; fix the "
            + "path in Shakefile.hs or restore the files"
            for spec in binding.positives
            if not git_ls_files(repo_root, (spec,))
        )
        failures.extend(
            f"binding '{binding.name}': exclude pathspec "
            + f"'{_EXCLUDE_PREFIX}{inner}' matches no tracked file — git archive "
            + "passes SILENTLY over a dead exclude, so the files it was meant to "
            + "keep out of the bundle would ship; fix the glob in Shakefile.hs"
            for inner in binding.excludes
            if not git_ls_files(repo_root, (inner,))
        )
    return failures


def check_go_work_not_staged(repo_root: Path, bindings: list[BindingSpec]) -> list[str]:
    """Return a failure when the go binding's pathspecs select ``go/go.work``.

    Runs the binding's full literal list (positives AND excludes) through
    ``git ls-files``, replicating the selection ``git archive`` would make.
    """
    failures: list[str] = []
    for binding in bindings:
        if binding.name != "go":
            continue
        if GO_WORK in git_ls_files(repo_root, binding.raw):
            failures.append(
                f"binding 'go': its pathspecs select '{GO_WORK}', which would ship in "
                + "the bundle and hijack a consumer's Go module resolution — narrow the "
                + "pathspecs in Shakefile.hs"
            )
    return failures


def check_packaging_scripts(repo_root: Path, fish: str | None) -> list[str]:
    """Return a failure per packaging script that is untracked or syntax-broken.

    ``fish`` is the fish binary path, or None when the ``.fish`` syntax checks
    are being skipped (the caller has already applied the CI fail-closed
    policy and printed the skip notice).
    """
    failures: list[str] = []
    for rel in PACKAGING_SCRIPTS:
        if not git_ls_files(repo_root, (rel,)):
            failures.append(
                f"packaging script '{rel}' is not git-tracked — dist copies it into the "
                + "bundle, so the release would break without it; git add it"
            )
            continue
        if rel.endswith(".sh"):
            checker = [find_executable("bash"), "-n", str(repo_root / rel)]
        elif fish is not None:
            checker = [fish, "--no-execute", str(repo_root / rel)]
        else:
            continue  # fish absent locally — skip notice already printed
        result = run_capture(checker)
        if result.returncode != 0:
            detail = result.stderr.strip() or result.stdout.strip()
            failures.append(f"packaging script '{rel}' fails its syntax check: {detail}")
    return failures


def check_license_tracked(repo_root: Path) -> list[str]:
    """Return a failure when the license file dist ships is not git-tracked."""
    if not git_ls_files(repo_root, (LICENSE_FILE,)):
        return [
            f"'{LICENSE_FILE}' is not git-tracked — dist ships it with the bundle "
            + "(BSD-2 requires the notice to travel with redistributions); git add it"
        ]
    return []


def _read_shakefile(path: Path) -> str:
    """Return the Shakefile's text, raising the could-not-check class when absent."""
    if not path.is_file():
        message = f"Shakefile not found: {path}"
        raise DistStagingError(message)
    return path.read_text(encoding="utf-8")


def _resolve_fish(*, require_fish: bool) -> str | None:
    """Apply the fish policy: fail closed on CI, skip loudly elsewhere.

    Returns the fish binary path, or None when the ``.fish`` syntax checks may
    be skipped.  Raises :class:`DistStagingError` when fish is absent but
    required (``GITHUB_ACTIONS`` set, or ``--require-fish``) — a CI runner
    without fish is a misconfiguration, not a skip.
    """
    fish = find_fish()
    if fish is not None:
        return fish
    if require_fish or os.environ.get("GITHUB_ACTIONS"):
        message = (
            "fish is not installed, but this is a CI runner (GITHUB_ACTIONS set) or "
            + "--require-fish was passed — the packaging *.fish syntax checks must not "
            + "be silently skipped there; install fish on the runner"
        )
        raise DistStagingError(message)
    emit(
        "check-dist-staging: fish not installed — skipping the packaging *.fish "
        + "syntax checks locally (CI enforces them)"
    )
    return None


def main() -> int:
    """Check every dist staging input; report each broken one with a remedy."""
    parser = argparse.ArgumentParser(
        description="Enforce that the release bundle's staging inputs all resolve."
    )
    _ = parser.add_argument(
        "--shakefile", type=Path, default=DEFAULT_SHAKEFILE, help="Shakefile path (test seam)"
    )
    _ = parser.add_argument(
        "--repo-root", type=Path, default=REPO_ROOT, help="git work tree to check (test seam)"
    )
    _ = parser.add_argument(
        "--require-fish",
        action="store_true",
        help="treat a missing fish as a failure even off CI",
    )
    args = parser.parse_args()
    shakefile: Path = args.shakefile
    repo_root: Path = args.repo_root

    try:
        bindings = parse_stage_bindings(_read_shakefile(shakefile))
        fish = _resolve_fish(require_fish=args.require_fish)
        failures = check_pathspecs_resolve(repo_root, bindings)
        failures += check_go_work_not_staged(repo_root, bindings)
        failures += check_packaging_scripts(repo_root, fish)
        failures += check_license_tracked(repo_root)
    except (DistStagingError, RuntimeError) as exc:
        _ = sys.stderr.write(f"check-dist-staging: COULD NOT CHECK — {exc}\n")
        return COULD_NOT_CHECK

    if failures:
        _ = sys.stderr.write("check-dist-staging: broken release-staging inputs\n\n")
        for failure in failures:
            _ = sys.stderr.write(f"  - {failure}\n")
        _ = sys.stderr.write(
            f"\nfound {len(failures)} broken staging input(s).  These are what "
            + "`cabal run shake -- dist` stages at release time; fixing them now keeps "
            + "the release from failing — or silently shipping the wrong file set — "
            + "at tag time.\n"
        )
        return 1

    n_pos = sum(len(b.positives) for b in bindings)
    n_exc = sum(len(b.excludes) for b in bindings)
    fish_note = "bash+fish syntax OK" if fish else "bash syntax OK; fish absent, .fish skipped"
    emit(
        f"check-dist-staging: {len(bindings)} bindings, {n_pos} positive + {n_exc} exclude "
        + f"pathspecs all resolve; {GO_WORK} stays out; packaging scripts tracked, "
        + f"{fish_note}; {LICENSE_FILE} tracked"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
