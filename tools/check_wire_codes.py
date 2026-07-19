# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_wire_codes.py — Kernel ↔ ``docs/WIRE_CODES.yaml`` wire-code parity gate.

The Agda kernel emits exactly two string-code vocabularies onto the JSON
wire: DBC validation issue codes (``formatIssueCode`` in
``src/Aletheia/Protocol/ResponseFormat.agda``, the ``issues[].code`` field)
and error codes (the per-ADT ``*ErrorCode`` formatter families plus the
top-level ``errorCode`` in ``src/Aletheia/Error.agda``, the error
envelope's ``code`` field).  Every
binding mirrors both vocabularies, but all four decoders deliberately pass
unknown codes through at runtime (the forward-compatibility channel), so a
NEW kernel code reaches production as an unrecognised string without any
test failing.

``docs/WIRE_CODES.yaml`` is the cross-binding SSOT for both vocabularies.
This gate anchors it to the kernel: it collects the literal-RHS formatter
arms from the two Agda sources and asserts the YAML matches — reciprocal
set equality per vocabulary, plus kernel declaration order (which the YAML
header promises, because MAlonzo numbers ADT constructors in declaration
order).  Per-binding parity tests (``python/tests/test_wire_codes_parity.py``)
then anchor each binding's vocabulary to the YAML, closing the
kernel → SSOT → binding chain.

Delegating formatter arms (e.g. ``parseErrorCode (InContext _ inner) =
parseErrorCode inner``) have no string-literal RHS and are skipped — only
literal arms mint wire codes.

Exit codes:
  0 — both vocabularies in parity (sets AND order).
  1 — divergence detected (missing / phantom / duplicate / reordered codes).
  2 — could not check: missing input file, malformed YAML, or zero codes
      parsed from a source that must carry them (a vacuous pass is refused).

Forward-revert verified 2026-07-19: adding a phantom row to the YAML or a
phantom ``formatIssueCode`` arm to the Agda source fires this gate; reverting
returns to exit 0.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_AGDA_ROOT = REPO_ROOT / "src"
DEFAULT_YAML_PATH = REPO_ROOT / "docs" / "WIRE_CODES.yaml"

# Vocabulary sources, relative to the Agda root (the --agda-root test seam).
ISSUE_CODE_SOURCE = Path("Aletheia") / "Protocol" / "ResponseFormat.agda"
ERROR_CODE_SOURCE = Path("Aletheia") / "Error.agda"

# The issue-code formatter: one literal arm per IssueCode constructor.
ISSUE_CODE_FUNCTIONS: tuple[str, ...] = ("formatIssueCode",)

# The per-ADT ``*ErrorCode`` functions plus the top-level ``errorCode``
# (which carries the consolidated ``input_bound_exceeded`` literal directly;
# its other arms delegate to the family formatters).
ERROR_CODE_FUNCTIONS: tuple[str, ...] = (
    "errorCode",
    "parseErrorCode",
    "frameErrorCode",
    "extractionErrorCode",
    "routeErrorCode",
    "handlerErrorCode",
    "dispatchErrorCode",
    "dbcTextParseErrorCode",
)

# Lines like:   parseErrorCode (MissingField _)   = "parse_missing_field"
# A delegating arm's RHS is not a string literal, so it does not match.
_RHS_STRING_RE = re.compile(r'=\s*"([^"\n]+)"\s*$')

COULD_NOT_CHECK = 2


class WireCodesError(Exception):
    """The inputs cannot be checked (missing file / malformed YAML / vacuous parse)."""


def collect_arm_literals(text: str, function_names: tuple[str, ...]) -> list[str]:
    """Return the string literals emitted by the named formatters' arms, in file order."""
    codes: list[str] = []
    for line in text.splitlines():
        stripped = line.lstrip()
        if not any(stripped.startswith(fn + " ") for fn in function_names):
            continue
        match = _RHS_STRING_RE.search(line)
        if match:
            codes.append(match.group(1))
    return codes


def parse_kernel_codes(
    agda_root: Path, relative: Path, functions: tuple[str, ...], label: str
) -> list[str]:
    """Parse one vocabulary's wire strings from its Agda source, in declaration order.

    Raises :class:`WireCodesError` when the source is missing or yields zero
    codes — either would make a "pass" vacuous.
    """
    source = agda_root / relative
    if not source.is_file():
        message = f"Agda source not found: {source}"
        raise WireCodesError(message)
    codes = collect_arm_literals(source.read_text(encoding="utf-8"), functions)
    if not codes:
        message = f"parsed zero {label} from {source} — the regex or the Agda layout changed"
        raise WireCodesError(message)
    return codes


def _entry_field(entry: dict[object, object], key: str, context: str) -> str:
    """Return the non-empty string field ``key`` of one YAML entry, or raise."""
    value = entry.get(key)
    if not isinstance(value, str) or not value:
        message = f"{context}: missing or empty '{key}'"
        raise WireCodesError(message)
    return value


def load_wire_codes(yaml_path: Path) -> dict[str, list[dict[str, str]]]:
    """Load and shape-check the SSOT, returning both sections' entries in file order.

    Every entry must carry a non-empty ``name`` and ``description``; a missing
    file, a malformed root, or a missing/empty section raises
    :class:`WireCodesError` (the could-not-check class — never a hollow pass).
    """
    if not yaml_path.is_file():
        message = f"SSOT not found: {yaml_path}"
        raise WireCodesError(message)
    raw: object = yaml.safe_load(yaml_path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        message = f"{yaml_path}: root must be a mapping"
        raise WireCodesError(message)
    root = cast("dict[object, object]", raw)
    sections: dict[str, list[dict[str, str]]] = {}
    for section in ("issue_codes", "error_codes"):
        entries_raw = root.get(section)
        if not isinstance(entries_raw, list) or not entries_raw:
            message = f"{yaml_path}: missing or empty '{section}' list"
            raise WireCodesError(message)
        entries: list[dict[str, str]] = []
        for idx, entry_raw in enumerate(cast("list[object]", entries_raw)):
            if not isinstance(entry_raw, dict):
                message = f"{yaml_path}: {section}[{idx}] must be a mapping"
                raise WireCodesError(message)
            entry = cast("dict[object, object]", entry_raw)
            context = f"{yaml_path}: {section}[{idx}]"
            entries.append(
                {
                    "name": _entry_field(entry, "name", context),
                    "description": _entry_field(entry, "description", context),
                }
            )
        sections[section] = entries
    return sections


def compare_vocabulary(label: str, kernel: list[str], ssot: list[str]) -> list[str]:
    """Return the divergences between one kernel vocabulary and its YAML section.

    Checks duplicates on both sides, then reciprocal set inclusion, then —
    only when the sets already agree — declaration order, so the order
    message never drowns out a genuine membership diff.
    """
    diffs: list[str] = []
    for side, codes in (("kernel", kernel), ("YAML", ssot)):
        seen: set[str] = set()
        for code in codes:
            if code in seen:
                diffs.append(f"{label}: duplicate code '{code}' on the {side} side")
            seen.add(code)
    kernel_set, ssot_set = set(kernel), set(ssot)
    diffs.extend(
        f"{label}: kernel emits '{code}' but docs/WIRE_CODES.yaml has no row — add one"
        for code in kernel
        if code not in ssot_set
    )
    diffs.extend(
        f"{label}: docs/WIRE_CODES.yaml declares '{code}' but no kernel formatter arm "
        + "emits it — remove the row or add the missing arm"
        for code in ssot
        if code not in kernel_set
    )
    if not diffs and kernel != ssot:
        diffs.append(
            f"{label}: same code set but the YAML order differs from kernel declaration "
            + "order — reorder the YAML rows to match the formatter arms "
            + "(the YAML header promises declaration order)"
        )
    return diffs


def main() -> int:
    """Check both wire-code vocabularies against the SSOT; report any divergence."""
    parser = argparse.ArgumentParser(
        description="Enforce kernel <-> docs/WIRE_CODES.yaml wire-code parity."
    )
    _ = parser.add_argument(
        "--agda-root", type=Path, default=DEFAULT_AGDA_ROOT, help="Agda source root (test seam)"
    )
    _ = parser.add_argument(
        "--yaml", type=Path, default=DEFAULT_YAML_PATH, help="SSOT YAML path (test seam)"
    )
    args = parser.parse_args()

    try:
        issue_kernel = parse_kernel_codes(
            args.agda_root, ISSUE_CODE_SOURCE, ISSUE_CODE_FUNCTIONS, "issue codes"
        )
        error_kernel = parse_kernel_codes(
            args.agda_root, ERROR_CODE_SOURCE, ERROR_CODE_FUNCTIONS, "error codes"
        )
        sections = load_wire_codes(args.yaml)
    except WireCodesError as exc:
        _ = sys.stderr.write(f"check-wire-codes: COULD NOT CHECK — {exc}\n")
        return COULD_NOT_CHECK

    diffs = compare_vocabulary(
        "issue_codes", issue_kernel, [entry["name"] for entry in sections["issue_codes"]]
    )
    diffs += compare_vocabulary(
        "error_codes", error_kernel, [entry["name"] for entry in sections["error_codes"]]
    )

    if diffs:
        _ = sys.stderr.write("check-wire-codes: divergences detected\n\n")
        for diff in diffs:
            _ = sys.stderr.write(f"  - {diff}\n")
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between the kernel formatters "
            + "(formatIssueCode / the *ErrorCode families) and docs/WIRE_CODES.yaml.\n"
            + "Reconcile by updating the YAML (when a kernel code was intentionally "
            + "added or removed) or the Agda formatter — and mirror the change in every "
            + "binding's vocabulary per the YAML header's addition protocol.\n"
        )
        return 1

    emit(
        f"check-wire-codes: {len(issue_kernel)} issue codes + {len(error_kernel)} error "
        + "codes — docs/WIRE_CODES.yaml matches the kernel formatters "
        + "(both directions, declaration order)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
