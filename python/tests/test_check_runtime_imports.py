# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_runtime_imports``: the runtime's code reaches no proof the kernel erases.

Each test of the walk builds a tree of its own: a foreign library stanza in
``haskell-shim/aletheia.cabal`` listing the shim's modules, their sources under
its ``hs-source-dirs``, generated modules under ``build/MAlonzo/Code`` and,
where a row is held by its source alone, a module under ``src``.  A closure
reaching every required layer and no refused proof passes; one reaching a
refused proof, by any path, or missing a required layer fails, and so does a
refused proof that exists nowhere.  Exit 2 holds what would cut the walk
short: a file it cannot read, a stanza the reader cannot read or one importing
a common stanza, a listed module with no source or two, shim modules importing
no generated module, a reached module with no generated file, and each line
form the reader refuses, in the shim and in generated code.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal

import pytest

from tools._common import RelPath
from tools.check_runtime_imports import (
    PASSED,
    REFUSED,
    UNREADABLE,
    CabalText,
    HaskellModule,
    HaskellSource,
    generated_file,
    generated_imports,
    run,
)

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.common_types import Prose

LAYER = HaskellModule("MAlonzo.Code.Aletheia.Layer")
PROOF = HaskellModule("MAlonzo.Code.Aletheia.Layer.Proof")
MIDDLE = HaskellModule("MAlonzo.Code.Aletheia.Middle")
ENTRY = HaskellModule("MAlonzo.Code.Aletheia.Entry")
SHIM_MODULE = HaskellModule("AletheiaFFI")
SHIM_FILE = RelPath("haskell-shim/src/AletheiaFFI.hs")
EMPTY = HaskellSource("")


def _imports(*modules: HaskellModule) -> HaskellSource:
    return HaskellSource("".join(f"import qualified {m}\n" for m in modules))


def _cabal(*modules: HaskellModule) -> CabalText:
    """Build a cabal file whose foreign library lists ``modules`` beside MAlonzo's own."""
    listed = [*modules, "-- BEGIN GENERATED", ENTRY, "MAlonzo.RTE", "-- END GENERATED"]
    return CabalText(
        "cabal-version: 3.0\nname: shim\n\n"
        + "foreign-library aletheia-ffi\n"
        + "    type:             native-shared\n"
        + "    other-modules:    "
        + "\n                      ".join(listed)
        + "\n    hs-source-dirs:   src, .\n"
        + "    build-depends:\n        base >= 4.14 && < 5,\n        text >= 1.2\n"
        + "    ghc-options:\n        -threaded\n        -- a note\n        -O2\n\n"
        + "test-suite other\n    other-modules:    Unlisted\n    hs-source-dirs:   test\n"
    )


def _module_of(rel: RelPath) -> HaskellModule:
    path = rel.removeprefix("haskell-shim/").removeprefix("src/")
    return HaskellModule(path.rsplit(".", 1)[0].replace("/", "."))


def _tree(
    root: Path,
    shim: dict[RelPath, HaskellSource],
    generated: dict[HaskellModule, HaskellSource],
    *,
    sources: tuple[RelPath, ...] = (),
    cabal: CabalText | None = None,
) -> Path:
    """Write ``root``'s files, and a stanza listing each shim source given unless ``cabal`` is."""
    files: dict[RelPath, HaskellSource | CabalText] = {
        **shim,
        **{rel: HaskellSource("") for rel in sources},
    }
    if cabal is not None or shim:
        listed = [_module_of(rel) for rel in shim if rel.endswith((".hs", ".hsc"))]
        files[RelPath("haskell-shim/aletheia.cabal")] = cabal or _cabal(*listed)
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        _ = (root / rel).write_text(text, encoding="utf-8")
    for module, text in generated.items():
        path = generated_file(root, module)
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(text, encoding="utf-8")
    return root


def _shim(*modules: HaskellModule) -> dict[RelPath, HaskellSource]:
    return {
        SHIM_FILE: HaskellSource(
            "module AletheiaFFI where\n"
            + "".join(f"import qualified {m} as Agda{n}\n" for n, m in enumerate(modules))
        )
    }


def _clean(root: Path) -> Path:
    """Build a tree whose shim imports ENTRY, which reaches LAYER, PROOF compiled but unreached."""
    return _tree(root, _shim(ENTRY), {ENTRY: _imports(LAYER), LAYER: EMPTY, PROOF: _imports(LAYER)})


def test_a_closure_reaching_the_layer_and_no_proof_passes(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A closure reaching the layer and no proof passes."""
    assert run(_clean(tmp_path), (LAYER,), (PROOF,)) == PASSED
    assert "reach 2 modules, the 1 required among them and none of the 1" in capsys.readouterr().out


def test_a_proof_reached_through_a_chain_is_refused_with_the_chain(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A proof reached two imports down is refused, naming the chain to it."""
    root = _tree(
        tmp_path,
        _shim(ENTRY),
        {ENTRY: _imports(MIDDLE, LAYER), MIDDLE: _imports(PROOF), LAYER: EMPTY, PROOF: EMPTY},
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED
    assert capsys.readouterr().err == (
        "check-runtime-imports: the runtime reaches Aletheia.Layer.Proof <- Aletheia.Middle"
        + f" <- Aletheia.Entry <- {SHIM_FILE}\n"
    )


def test_the_chain_named_is_a_shortest_one(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A proof reached by a short path between two long ones is named by the short one."""
    far, farther, wide, wider = (
        HaskellModule(f"MAlonzo.Code.Aletheia.{name}")
        for name in ("Far", "Farther", "Wide", "Wider")
    )
    root = _tree(
        tmp_path,
        _shim(ENTRY),
        {
            ENTRY: _imports(far, MIDDLE, wide, LAYER),
            far: _imports(farther),
            farther: _imports(PROOF),
            MIDDLE: _imports(PROOF),
            wide: _imports(wider),
            wider: _imports(PROOF),
            LAYER: EMPTY,
            PROOF: EMPTY,
        },
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED
    assert "reaches Aletheia.Layer.Proof <- Aletheia.Middle <- Aletheia.Entry <-" in (
        capsys.readouterr().err
    )


def test_a_proof_the_shim_imports_itself_is_refused(tmp_path: Path) -> None:
    """A proof the shim imports itself is refused."""
    root = _tree(
        tmp_path, _shim(ENTRY, PROOF), {ENTRY: _imports(LAYER), LAYER: EMPTY, PROOF: EMPTY}
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED


def test_a_shim_module_in_another_source_directory_is_read(tmp_path: Path) -> None:
    """A listed shim module found under the stanza's second source directory is read."""
    hidden = {RelPath("haskell-shim/AletheiaFFI/Hidden.hs"): _imports(PROOF)}
    root = _tree(
        tmp_path, {**_shim(ENTRY), **hidden}, {ENTRY: _imports(LAYER), LAYER: EMPTY, PROOF: EMPTY}
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED


def test_a_shim_module_behind_a_symlinked_directory_is_read(tmp_path: Path) -> None:
    """A listed shim module whose directory is a symlink is read through it."""
    outside = tmp_path / "outside"
    outside.mkdir()
    _ = (outside / "Hidden.hs").write_text(_imports(PROOF), encoding="utf-8")
    root = _clean(tmp_path / "tree")
    (root / "haskell-shim/src/AletheiaFFI").symlink_to(outside)
    _ = _tree(root, {}, {}, cabal=_cabal(SHIM_MODULE, HaskellModule("AletheiaFFI.Hidden")))
    assert run(root, (LAYER,), (PROOF,)) == REFUSED


def test_a_file_the_stanza_does_not_list_is_not_read(tmp_path: Path) -> None:
    """A source the stanza does not list, here or in another stanza's directory, is not read."""
    root = _clean(tmp_path)
    unlisted = {
        RelPath("haskell-shim/src/Unlisted.hs"): _imports(PROOF),
        RelPath("haskell-shim/test/Unlisted.hs"): _imports(PROOF),
        RelPath("haskell-shim/src/notes.txt"): HaskellSource(f"import {PROOF}\n"),
    }
    _ = _tree(root, unlisted, {}, cabal=_cabal(SHIM_MODULE))
    assert run(root, (LAYER,), (PROOF,)) == PASSED


def test_an_hsc_source_is_read(tmp_path: Path) -> None:
    """A listed module whose source is .hsc seeds the walk."""
    wire = {RelPath("haskell-shim/src/AletheiaFFI/Wire.hsc"): _imports(PROOF)}
    root = _tree(
        tmp_path, {**_shim(ENTRY), **wire}, {ENTRY: _imports(LAYER), LAYER: EMPTY, PROOF: EMPTY}
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED


@pytest.mark.parametrize(
    "files",
    [
        (RelPath("haskell-shim/src/AletheiaFFI/Hidden.lhs"),),
        (),
        (
            RelPath("haskell-shim/src/AletheiaFFI/Hidden.hs"),
            RelPath("haskell-shim/AletheiaFFI/Hidden.hs"),
        ),
    ],
    ids=["literate-only", "none", "two"],
)
def test_a_listed_module_without_one_source_cannot_be_read(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose], files: tuple[RelPath, ...]
) -> None:
    """A listed module whose name gives no .hs or .hsc file, or two, is refused."""
    root = _clean(tmp_path)
    _ = _tree(
        root,
        {rel: _imports(PROOF) for rel in files},
        {},
        cabal=_cabal(SHIM_MODULE, HaskellModule("AletheiaFFI.Hidden")),
    )
    assert run(root, (LAYER,), (PROOF,)) == UNREADABLE
    count = 2 if len(files) == 2 else 0
    assert f"AletheiaFFI.Hidden has {count} .hs or .hsc sources under ['src', '.']" in (
        capsys.readouterr().err
    )


@pytest.mark.parametrize(
    ("cabal", "reason"),
    [
        (CabalText("library\n    other-modules: AletheiaFFI\n"), "has no `foreign-library"),
        (
            CabalText(
                "foreign-library aletheia-ffi\n    other-modules: AletheiaFFI\n"
                + "    if flag(x)\n      hs-source-dirs: src\n"
            ),
            "a line of the stanza the reader does not read:     if flag(x)",
        ),
        (
            CabalText(
                "foreign-library aletheia-ffi\n    other-modules: MAlonzo.RTE\n"
                + "    hs-source-dirs: src\n"
            ),
            "lists no shim module or no hs-source-dirs",
        ),
        (
            CabalText("foreign-library aletheia-ffi\n    other-modules: AletheiaFFI\n"),
            "lists no shim module or no hs-source-dirs",
        ),
        (
            CabalText(
                "common shim\n    other-modules: AletheiaFFI.Extra\n\n"
                + "foreign-library aletheia-ffi\n    import: shim\n"
                + "    other-modules: AletheiaFFI\n    hs-source-dirs: src\n"
            ),
            "the stanza imports a common stanza the reader does not read",
        ),
    ],
    ids=["no-stanza", "unread-line", "no-shim-module", "no-source-dirs", "common-stanza"],
)
def test_a_stanza_the_reader_cannot_read_is_refused(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose], cabal: CabalText, reason: Prose
) -> None:
    """A missing stanza, a line in it the reader does not read or a missing field is refused."""
    root = _tree(tmp_path, _shim(ENTRY), {ENTRY: _imports(LAYER), LAYER: EMPTY}, cabal=cabal)
    assert run(root, (LAYER,), ()) == UNREADABLE
    assert reason in capsys.readouterr().err


def test_a_required_layer_not_reached_is_refused(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A required layer not reached is refused."""
    root = _tree(tmp_path, _shim(ENTRY), {ENTRY: EMPTY, LAYER: EMPTY})
    assert run(root, (LAYER,), ()) == REFUSED
    assert capsys.readouterr().err == (
        f"check-runtime-imports: the runtime does not reach {LAYER}\n"
    )


def test_a_refused_proof_that_exists_nowhere_is_refused(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A refused proof neither generated nor in src/ is a row that cannot fire."""
    gone = HaskellModule("MAlonzo.Code.Aletheia.Gone")
    assert run(_clean(tmp_path), (LAYER,), (PROOF, gone)) == REFUSED
    assert capsys.readouterr().err == (
        f"check-runtime-imports: {gone} exists neither in src/ nor in build/MAlonzo/Code/\n"
    )


def test_a_refused_proof_held_by_its_source_alone_is_a_live_row(tmp_path: Path) -> None:
    """A refused proof that src/ holds and the build does not compile passes."""
    root = _clean(tmp_path)
    _ = _tree(root, {}, {}, sources=(RelPath("src/Aletheia/Layer/Unbuilt.agda"),))
    unbuilt = HaskellModule("MAlonzo.Code.Aletheia.Layer.Unbuilt")
    assert run(root, (LAYER,), (PROOF, unbuilt)) == PASSED


def test_shim_modules_importing_no_generated_module_cannot_be_read(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Shim modules importing no generated module leave nothing to walk."""
    root = _tree(tmp_path, {SHIM_FILE: HaskellSource("import Data.Text\n")}, {})
    assert run(root, (), ()) == UNREADABLE
    assert capsys.readouterr().err == (
        "check-runtime-imports: cannot read the closure: the shim's modules import no "
        + "generated module\n"
    )


def test_a_reached_module_without_its_generated_file_cannot_be_read(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A reached module with no generated file would cut the walk short."""
    root = _tree(tmp_path, _shim(ENTRY), {ENTRY: _imports(MIDDLE), LAYER: EMPTY})
    assert run(root, (), ()) == UNREADABLE
    err = capsys.readouterr().err
    assert err.startswith(
        "check-runtime-imports: cannot read the closure: Aletheia.Middle <- Aletheia.Entry"
        + f" <- {SHIM_FILE}: no generated file "
    )
    assert err.endswith("build/MAlonzo/Code/Aletheia/Middle.hs\n")


REFUSED_FORMS = (
    HaskellSource(f"import {MIDDLE}"),
    HaskellSource(f"import {MIDDLE} qualified as M"),
    HaskellSource(f"import {{-# SOURCE #-}} qualified {MIDDLE}"),
    HaskellSource(f"import qualified {MIDDLE} (d_f)"),
    HaskellSource(f"import qualified {MIDDLE} hiding (d_f)"),
    HaskellSource(f"import qualified {MIDDLE} as M -- a note"),
    HaskellSource(f"import  qualified {MIDDLE}"),
    HaskellSource(f"import{{- c -}}qualified {MIDDLE} as M"),
    HaskellSource(f"{{- c -}} import qualified {MIDDLE} as M"),
    HaskellSource(f"; import qualified {MIDDLE} as M"),
    HaskellSource(f"module AletheiaFFI where import qualified {MIDDLE} as M"),
    HaskellSource(f"import qualified\n  {MIDDLE} as M"),
    HaskellSource(f"import\n  qualified {MIDDLE}"),
    HaskellSource(f"import {{-# SOURCE #-}}\n  qualified {MIDDLE}"),
    HaskellSource(f"import Data.Text; import qualified\n  {MIDDLE} as M"),
    HaskellSource("import Data.Text -- and the import below"),
    HaskellSource(f'#include "imports.inc"\n{_imports(MIDDLE)}'),
    HaskellSource(f'#include "aletheia.h"\n{_imports(MIDDLE)}'),
)


@pytest.mark.parametrize("text", REFUSED_FORMS)
@pytest.mark.parametrize("where", ["shim", "generated"])
def test_a_line_the_reader_refuses_cannot_be_read(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    text: HaskellSource,
    where: Literal["shim", "generated"],
) -> None:
    """Each form that could hide an import is refused, read from the shim or a generated module."""
    if where == "shim":
        shim = {SHIM_FILE: HaskellSource(f"{_imports(ENTRY)}{text}\n")}
        root = _tree(tmp_path, shim, {ENTRY: EMPTY, MIDDLE: EMPTY})
    else:
        root = _tree(tmp_path, _shim(ENTRY), {ENTRY: HaskellSource(f"{text}\n"), MIDDLE: EMPTY})
    importer = SHIM_FILE if where == "shim" else ENTRY
    assert run(root, (), ()) == UNREADABLE
    first = text.splitlines()[0]
    assert f"{importer}: a line the reader refuses: {first}\n" in capsys.readouterr().err


def test_lines_that_hide_no_generated_import_are_read_as_such() -> None:
    """Other imports in GHC's spellings, comments and foreign imports pass."""
    text = HaskellSource(
        "import MAlonzo.RTE (coe)\n"
        + "import qualified Data.Text as T\n"
        + "import Data.Map(lookup)\n"
        + 'import "text" Data.Text\n'
        + "import {-# SOURCE #-} Data.Foo\n"
        + "import safe Data.Foo\n"
        + "-- we import nothing here\n"
        + 'foreign import ccall unsafe "f" f :: IO ()\n'
        + f"importer = {MIDDLE}.d_f\n"
        + f"  x = {MIDDLE}.d_g\n"
        + f"  import qualified {LAYER}\r\n"
        + f"import qualified {ENTRY} as E\n"
    )
    assert generated_imports(text) == ([LAYER, ENTRY], [])


def test_an_hsc_source_includes_for_its_c_program_alone(tmp_path: Path) -> None:
    """An include in .hsc source, which hsc2hs gives the C program it runs, passes."""
    text = HaskellSource(f'#include "aletheia.h"\n#include <stdint.h>\n{_imports(ENTRY)}')
    assert generated_imports(text, hsc=True) == ([ENTRY], [])
    wire = {RelPath("haskell-shim/src/AletheiaFFI/Wire.hsc"): text}
    root = _tree(tmp_path, wire, {ENTRY: _imports(LAYER), LAYER: EMPTY})
    assert run(root, (LAYER,), ()) == PASSED


@pytest.mark.parametrize("damage", ["no-cabal", "not-utf-8"])
def test_a_file_the_walk_cannot_read_exits_2(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    damage: Literal["no-cabal", "not-utf-8"],
) -> None:
    """A missing stanza file or a generated file that is not UTF-8 cannot be read."""
    root = _clean(tmp_path)
    if damage == "no-cabal":
        (root / "haskell-shim/aletheia.cabal").unlink()
    else:
        _ = generated_file(root, LAYER).write_bytes(b"import qualified \xff\n")
    assert run(root, (LAYER,), (PROOF,)) == UNREADABLE
    assert "check-runtime-imports: cannot read the closure: " in capsys.readouterr().err


def test_an_import_cycle_is_walked_once(tmp_path: Path) -> None:
    """Two generated modules importing each other end the walk, the proof beyond still seen."""
    root = _tree(
        tmp_path,
        _shim(ENTRY),
        {ENTRY: _imports(LAYER), LAYER: _imports(ENTRY, PROOF), PROOF: EMPTY},
    )
    assert run(root, (LAYER,), (PROOF,)) == REFUSED
