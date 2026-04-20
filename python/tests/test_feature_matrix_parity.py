"""Feature matrix parity test — Python side.

Reads ``docs/FEATURE_MATRIX.yaml`` and verifies:

1. Every feature row has a well-formed schema (id / name / description /
   bindings for all three languages, each with a valid status).
2. Every binding with ``status: implemented`` carries an ``entry`` field.
3. Every Python ``implemented`` entry resolves via ``importlib`` + recursive
   ``getattr`` — catches silent removal or rename of a public symbol.
4. Every binding with ``status: not_applicable`` carries a non-empty
   ``reason`` string — the escape hatch must stay honest.

A failure here means the Python public surface drifted from what the matrix
declares. Fix: either the code (add the symbol back), or the matrix (mark
the feature as ``planned`` or ``not_applicable`` with justification).

See ``docs/development/PARITY_PLAN.md`` for the rationale and roadmap.
"""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import cast

import pytest
import yaml

_VALID_STATUSES: frozenset[str] = frozenset(
    {"implemented", "not_applicable", "planned"}
)
_BINDINGS: tuple[str, ...] = ("python", "cpp", "go")

_REPO_ROOT = Path(__file__).resolve().parents[2]
_MATRIX_PATH = _REPO_ROOT / "docs" / "FEATURE_MATRIX.yaml"


def _as_str_object_dict(value: object, context: str) -> dict[str, object]:
    """Validate that ``value`` is a dict with string keys; cast and return it."""
    assert isinstance(value, dict), (
        f"{context}: expected mapping, got {type(value).__name__}"
    )
    narrowed: dict[object, object] = cast("dict[object, object]", value)
    for key in narrowed:
        assert isinstance(key, str), (
            f"{context}: non-string key {key!r} in mapping"
        )
    return cast("dict[str, object]", value)


def _load_matrix() -> list[dict[str, object]]:
    """Load and return the matrix's features list with minimal shape guarantees."""
    with _MATRIX_PATH.open("r", encoding="utf-8") as fh:
        raw: object = yaml.safe_load(fh)
    root = _as_str_object_dict(raw, "FEATURE_MATRIX.yaml root")
    features_raw: object = root.get("features")
    assert isinstance(features_raw, list), (
        "FEATURE_MATRIX.yaml must contain a 'features' list"
    )
    narrowed_list: list[object] = cast("list[object]", features_raw)
    assert narrowed_list, "FEATURE_MATRIX.yaml 'features' list is empty"
    validated: list[dict[str, object]] = []
    for idx, feat in enumerate(narrowed_list):
        validated.append(_as_str_object_dict(feat, f"features[{idx}]"))
    return validated


_FEATURES: list[dict[str, object]] = _load_matrix()


def _feature_id(feature: dict[str, object]) -> str:
    fid: object = feature["id"]
    assert isinstance(fid, str)
    return fid


_FEATURE_IDS: list[str] = [_feature_id(f) for f in _FEATURES]


def _resolve(dotted_path: str) -> object:
    """Resolve a dotted path via longest-importable-prefix + recursive getattr.

    Handles three shapes:
      - ``aletheia``                           (module)
      - ``aletheia.client._log``               (sub-module)
      - ``aletheia.AletheiaClient.parse_dbc``  (class.method)
    """
    parts = dotted_path.split(".")
    module: object = None
    resolved_prefix_len = 0
    for i in range(len(parts), 0, -1):
        candidate = ".".join(parts[:i])
        try:
            module = importlib.import_module(candidate)
            resolved_prefix_len = i
            break
        except ImportError:
            continue
    if module is None:
        raise ImportError(f"Could not import any prefix of {dotted_path!r}")
    obj: object = module
    for attr in parts[resolved_prefix_len:]:
        next_obj: object = getattr(obj, attr)
        obj = next_obj
    return obj


def _get_str(mapping: dict[str, object], key: str) -> str | None:
    value: object = mapping.get(key)
    return value if isinstance(value, str) else None


@pytest.mark.parametrize("feature", _FEATURES, ids=_FEATURE_IDS)
def test_feature_schema(feature: dict[str, object]) -> None:
    """Schema integrity — every row is well-formed across all three bindings."""
    fid = _feature_id(feature)

    name = _get_str(feature, "name")
    assert name and name.strip(), f"{fid}: missing name"
    description = _get_str(feature, "description")
    assert description and description.strip(), f"{fid}: missing description"

    bindings = _as_str_object_dict(feature.get("bindings"), f"{fid}.bindings")

    for binding_name in _BINDINGS:
        binding = _as_str_object_dict(
            bindings.get(binding_name), f"{fid}.{binding_name}"
        )

        status = _get_str(binding, "status")
        assert status in _VALID_STATUSES, (
            f"{fid}.{binding_name}: status={status!r} "
            f"not in {sorted(_VALID_STATUSES)}"
        )

        if status == "implemented":
            entry = _get_str(binding, "entry")
            assert entry and entry.strip(), (
                f"{fid}.{binding_name}: status=implemented requires "
                "non-empty entry"
            )

        if status == "not_applicable":
            reason = _get_str(binding, "reason")
            assert reason and reason.strip(), (
                f"{fid}.{binding_name}: status=not_applicable requires "
                "non-empty reason — the escape hatch must stay honest"
            )


def _is_python_implemented(feature: dict[str, object]) -> bool:
    bindings = feature.get("bindings")
    if not isinstance(bindings, dict):
        return False
    bindings_narrowed = _as_str_object_dict(cast("object", bindings), "bindings")
    python = bindings_narrowed.get("python")
    if not isinstance(python, dict):
        return False
    python_narrowed = _as_str_object_dict(cast("object", python), "python")
    return _get_str(python_narrowed, "status") == "implemented"


def _python_entry(feature: dict[str, object]) -> str:
    bindings = _as_str_object_dict(feature["bindings"], "bindings")
    python = _as_str_object_dict(bindings["python"], "python")
    entry = _get_str(python, "entry")
    assert entry is not None
    return entry


_PYTHON_IMPLEMENTED: list[dict[str, object]] = [
    f for f in _FEATURES if _is_python_implemented(f)
]
_PYTHON_IMPLEMENTED_IDS: list[str] = [_feature_id(f) for f in _PYTHON_IMPLEMENTED]


@pytest.mark.parametrize(
    "feature", _PYTHON_IMPLEMENTED, ids=_PYTHON_IMPLEMENTED_IDS
)
def test_python_entry_resolves(feature: dict[str, object]) -> None:
    """Every Python ``implemented`` entry must resolve via importlib + getattr.

    Catches silent removal or rename of a public symbol. If this fails, either
    the code regressed (symbol gone) or the matrix is stale (needs update).
    """
    entry = _python_entry(feature)
    try:
        resolved = _resolve(entry)
    except (ImportError, AttributeError) as exc:
        pytest.fail(
            f"{_feature_id(feature)}: Python entry {entry!r} did not resolve: {exc}"
        )
    assert resolved is not None, (
        f"{_feature_id(feature)}: Python entry {entry!r} resolved to None"
    )
