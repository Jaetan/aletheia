# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Guards for the generated git-hook bodies in ``tools/install_hooks.py``.

The hook bodies are f-strings, so any literal ``{`` in the embedded shell / git
commands must be doubled (``{{``) or the f-string silently substitutes it.  A
``stash@{0}`` that rendered as ``stash@0`` once disabled the whole pre-commit
stash-restore path (an invalid git ref → no restore → lost unstaged work), and
``compile()`` does NOT catch it (``stash@0`` is valid string content).  Pin the
rendered bodies here.
"""

from __future__ import annotations

from tools.install_hooks import PRE_COMMIT_BODY, PRE_PUSH_BODY


def test_hook_bodies_are_valid_python() -> None:
    """Both generated hook bodies compile (an f-string typo can break them)."""
    compile(PRE_COMMIT_BODY, "<pre-commit>", "exec")
    compile(PRE_PUSH_BODY, "<pre-push>", "exec")


def test_pre_commit_stash_ref_survived_the_fstring() -> None:
    """The stash ref renders as ``stash@{0}`` — the f-string must not eat the braces.

    ``stash@{0}`` in an f-string body renders the ``{0}`` field as ``0`` unless
    doubled to ``{{0}}``; the resulting ``stash@0`` is an invalid git ref that
    silently disables the hook's stash restore. Compilation can't catch it.
    """
    assert "stash@{0}" in PRE_COMMIT_BODY
    assert "stash@0" not in PRE_COMMIT_BODY
