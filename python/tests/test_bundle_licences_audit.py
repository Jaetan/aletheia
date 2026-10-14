# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the arms of ``tools.bundle_licences`` that hold the licence audit's verdict file.

The verdict file names each tarball scanned with its SHA-256 and a verdict per
hit.  Without reading a tarball, ``check`` holds it to the record (every
tarball a library's own licence text was taken from scanned, at the SHA-256
the record names) and holds each verdict to naming one kept text or one
reason.
"""

from __future__ import annotations

import hashlib
from typing import TYPE_CHECKING, Literal

import pytest
from _licence_fixtures import KEPT_TEXTS, Texts, plant

from tools.bundle_licences import (
    AUDIT,
    GHC_TARBALL,
    KEPT,
    Audit,
    Digest,
    LicenceUnreadError,
    SourcePath,
    TarballName,
    TextPath,
    Verdict,
    audit_findings,
    read_audit,
    read_record,
    scanned_tarballs,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_GHC_DIGEST = Digest("1" * 64)
_AGDA = TarballName("Agda-2.8.0")
_AGDA_DIGEST = Digest("2" * 64)
_WHERE = KEPT / AUDIT
_SCANNED = f'tarballs:\n  ghc: "{_GHC_DIGEST}"\n'


def _record_text(texts: Texts) -> Prose:
    """Return a record of ``texts``, the Agda one taken from Agda's tarball."""
    rows = "".join(
        f"  {path}:\n"
        + ("    source: Agda-2.8.0\n" if path.startswith("Agda-") else "")
        + f'    from: x\n    sha256: "{hashlib.sha256(text).hexdigest()}"\n'
        for path, text in texts.items()
    )
    return Prose(
        'ghc: "9.8.4"\ntarball:\n  url: https://example.org/ghc-9.8.4-src.tar.xz\n'
        + f'  sha256: "{_GHC_DIGEST}"\nsources:\n  Agda-2.8.0:\n'
        + f'    url: https://example.org/Agda-2.8.0.tar.gz\n    sha256: "{_AGDA_DIGEST}"\n'
        + f"texts:\n{rows}"
    )


_RTS = SourcePath("rts/RtsUtils.c")


def _hit(*, covered_by: TextPath | None = None, dismissed: Prose | None = None) -> Verdict:
    """Return a verdict on one hit in GHC's tarball, judged as the arguments say."""
    verdict = Verdict(tarball=GHC_TARBALL, path=_RTS, line=Prose("/* borrowed */"))
    if covered_by is not None:
        verdict["covered_by"] = covered_by
    if dismissed is not None:
        verdict["dismissed"] = dismissed
    return verdict


def _audit(verdicts: list[Verdict], tarballs: dict[TarballName, Digest] | None = None) -> Audit:
    """Return an audit of both tarballs at the record's digests, unless ``tarballs`` says."""
    scanned = {GHC_TARBALL: _GHC_DIGEST, _AGDA: _AGDA_DIGEST} if tarballs is None else tarballs
    return Audit(tarballs=scanned, verdicts=verdicts)


def _findings(tmp_path: Path, audit: Audit) -> list[Prose]:
    """Return the audit arms' findings for ``audit`` against the kept texts."""
    kept = plant(tmp_path / "kept", KEPT_TEXTS)
    return audit_findings(read_record(_record_text(KEPT_TEXTS)), audit, kept)


def test_scanned_tarballs_are_those_a_librarys_own_licence_came_from() -> None:
    """GHC's for the packages, Agda's for the kernel's Agda text; a second text adds none."""
    assert scanned_tarballs(read_record(_record_text(KEPT_TEXTS))) == [_AGDA, GHC_TARBALL]


def test_audit_findings_holds_a_current_audit_with_complete_verdicts(tmp_path: Path) -> None:
    """Both tarballs at the record's digests, each verdict one covering text or one reason."""
    verdicts = [
        _hit(covered_by=TextPath("rts-1.0.2/LICENSE")),
        Verdict(tarball=_AGDA, path=SourcePath("x"), line=Prose("y"), dismissed=Prose("prose")),
    ]
    assert not _findings(tmp_path, _audit(verdicts))


def test_audit_findings_names_a_tarball_scanned_at_another_digest(tmp_path: Path) -> None:
    """A tarball scanned at a SHA-256 the record does not name is a stale audit."""
    stale = {GHC_TARBALL: Digest("3" * 64), _AGDA: _AGDA_DIGEST}
    assert _findings(tmp_path, _audit([], stale)) == [
        Prose(f"{_WHERE}: scanned ghc at a SHA-256 the record does not name")
    ]


def test_audit_findings_names_a_tarball_the_record_wants_scanned(tmp_path: Path) -> None:
    """A tarball a library's own licence came from, left unscanned, is a finding."""
    assert _findings(tmp_path, _audit([], {GHC_TARBALL: _GHC_DIGEST})) == [
        Prose(f"{_WHERE}: scanned no Agda-2.8.0; scan it with tools.licence_audit")
    ]


def test_audit_findings_names_a_tarball_scanned_the_record_does_not_name(tmp_path: Path) -> None:
    """A tarball the record does not name at all is no current scan."""
    extra = {GHC_TARBALL: _GHC_DIGEST, _AGDA: _AGDA_DIGEST, TarballName("gone"): Digest("4" * 64)}
    assert _findings(tmp_path, _audit([], extra)) == [
        Prose(f"{_WHERE}: scanned gone at a SHA-256 the record does not name")
    ]


@pytest.mark.parametrize(
    "verdict",
    [
        _hit(),
        _hit(covered_by=TextPath("")),
        _hit(dismissed=Prose("")),
        _hit(covered_by=TextPath("rts-1.0.2/LICENSE"), dismissed=Prose("both")),
    ],
)
def test_audit_findings_names_a_verdict_not_one_text_or_one_reason(
    tmp_path: Path, verdict: Verdict
) -> None:
    """A verdict with neither, an empty one, or both is unjudged."""
    assert _findings(tmp_path, _audit([verdict])) == [
        Prose(f"{_WHERE}: ghc:{_RTS}: its verdict needs one of covered_by and dismissed, not both")
    ]


def test_audit_findings_names_a_covering_text_not_kept(tmp_path: Path) -> None:
    """A verdict covered by a text the tree does not keep is a finding."""
    verdict = _hit(covered_by=TextPath("rts-1.0.2/LICENSE-gone"))
    assert _findings(tmp_path, _audit([verdict])) == [
        Prose(f"{_WHERE}: ghc:{_RTS}: covered by rts-1.0.2/LICENSE-gone, which is not kept")
    ]


def test_read_audit_reads_the_tarballs_and_the_verdicts() -> None:
    """An audit reads as its tarballs and its verdicts."""
    text = Prose(
        f'tarballs:\n  ghc: "{_GHC_DIGEST}"\nverdicts:\n'
        + "- tarball: ghc\n  path: rts/RtsUtils.c\n  line: x\n  dismissed: prose\n"
        + "- tarball: ghc\n  path: rts/Hash.c\n  line: y\n  covered_by: rts-1.0.2/LICENSE\n"
    )
    assert read_audit(text) == _audit(
        [
            Verdict(tarball=GHC_TARBALL, path=_RTS, line=Prose("x"), dismissed=Prose("prose")),
            Verdict(
                tarball=GHC_TARBALL,
                path=SourcePath("rts/Hash.c"),
                line=Prose("y"),
                covered_by=TextPath("rts-1.0.2/LICENSE"),
            ),
        ],
        {GHC_TARBALL: _GHC_DIGEST},
    )


@pytest.mark.parametrize(
    ("text", "reason"),
    [
        (Prose("verdicts: []\n"), Prose("lacks the key 'tarballs'")),
        (Prose(_SCANNED), Prose("lacks the key 'verdicts'")),
        (
            Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  line: x\n"),
            Prose("lacks the key 'path'"),
        ),
        (
            Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: 1\n  line: x\n"),
            Prose("is not shaped as an audit: "),
        ),
        (Prose("- a list\n"), Prose("is not shaped as an audit: ")),
    ],
)
def test_read_audit_refuses_an_audit_lacking_a_value(text: Prose, reason: Prose) -> None:
    """An audit without one of its values, or with a place that is not text, is unread."""
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE} {reason}"):
        _ = read_audit(text)


def test_read_audit_refuses_a_tarball_digest_not_a_sha256() -> None:
    """A tarball scanned at a value that is no SHA-256 digest is unread."""
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE}: 'short' is not a SHA-256 digest$"):
        _ = read_audit(Prose('tarballs:\n  ghc: "short"\nverdicts: []\n'))


_DIGEST_TEXT = f'"{_GHC_DIGEST}"'


@pytest.mark.parametrize(
    ("text", "key"),
    [
        (Prose(f"tarballs:\n  ghc: {_DIGEST_TEXT}\n  ghc: {_DIGEST_TEXT}\nverdicts: []\n"), "ghc"),
        (Prose(f"tarballs:\n  ghc: {_DIGEST_TEXT}\nverdicts: []\nverdicts: []\n"), "verdicts"),
        (
            Prose(
                f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: p\n  line: l\n"
                + "  covered_by: gone-1.0/LICENSE\n  covered_by: rts-1.0.2/LICENSE\n"
            ),
            "covered_by",
        ),
    ],
)
def test_read_audit_refuses_a_repeated_key(
    text: Prose, key: Literal["ghc", "verdicts", "covered_by"]
) -> None:
    """YAML keeps the last of two equal keys, so an earlier wrong value would be read past."""
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE} repeats the key '{key}'$"):
        _ = read_audit(text)


@pytest.mark.parametrize(
    "text",
    [
        Prose(f"{_SCANNED}verdicts: {{}}\n"),
        Prose(f"{_SCANNED}verdicts: ''\n"),
        Prose("tarballs:\nverdicts: []\n"),
        Prose("tarballs:\n  ghc: 1\nverdicts: []\n"),
        Prose(f"tarballs:\n  1: {_DIGEST_TEXT}\nverdicts: []\n"),
        Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: p\n  line: 1\n  dismissed: r\n"),
        Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: p\n  line: l\n  covered_by: [a]\n"),
        Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: p\n  line: l\n  dismissed: true\n"),
        Prose(f"{_SCANNED}verdicts: []\nnotes: x\n"),
        Prose(f"{_SCANNED}verdicts:\n- tarball: ghc\n  path: p\n  line: l\n  covred_by: x\n"),
    ],
)
def test_read_audit_refuses_a_value_out_of_shape(text: Prose) -> None:
    """Verdicts not a list, tarballs not a mapping, a place not text, or a key no audit has."""
    with pytest.raises(LicenceUnreadError, match=f"^{_WHERE} is not shaped as an audit: "):
        _ = read_audit(text)


def test_audit_findings_reads_a_blank_judgement_as_none(tmp_path: Path) -> None:
    """A reason or a covering text of spaces judges nothing."""
    for verdict in (_hit(dismissed=Prose("   ")), _hit(covered_by=TextPath("  "))):
        assert _findings(tmp_path / str(id(verdict)), _audit([verdict])) == [
            Prose(
                f"{_WHERE}: ghc:{_RTS}: its verdict needs one of covered_by and dismissed, not both"
            )
        ]


def test_audit_findings_names_a_verdict_on_a_tarball_never_scanned(tmp_path: Path) -> None:
    """A verdict judges a hit of a scanned tarball, or it judges nothing."""
    verdict = Verdict(tarball=TarballName("zlib"), path=_RTS, line=Prose("x"), dismissed=Prose("r"))
    assert _findings(tmp_path, _audit([verdict])) == [
        Prose(f"{_WHERE}: zlib:{_RTS}: judges a hit in zlib, which it never scanned")
    ]


def test_audit_findings_names_a_second_verdict_for_one_hit(tmp_path: Path) -> None:
    """Two verdicts on one hit, even agreeing, leave its judgement two ways to read."""
    verdicts = [_hit(dismissed=Prose("r")), _hit(covered_by=TextPath("rts-1.0.2/LICENSE"))]
    assert _findings(tmp_path, _audit(verdicts)) == [
        Prose(f"{_WHERE}: ghc:{_RTS}: a second verdict for '/* borrowed */'")
    ]
