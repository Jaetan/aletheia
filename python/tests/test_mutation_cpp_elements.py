# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the shape of Mull's Elements report (``tools.mutation_cpp_elements``).

Mull names a file by its absolute path under the tree it swept; the lane
reads every path at its ``cpp/`` component, so a record taken in one tree
reads in another.
"""

from __future__ import annotations

from tools.mutation_cpp_elements import MullPath, repo_relative


def test_a_path_is_made_repository_relative_at_its_cpp_component() -> None:
    """The first ``/cpp/`` cuts the path; a path without one is kept as Mull wrote it.

    A directory whose name only ends or starts with ``cpp`` is not that component.
    """
    assert repo_relative(MullPath("/home/user/tree/cpp/src/a.cpp")) == "cpp/src/a.cpp"
    assert repo_relative(MullPath("/w/cpp/x/cpp/b.hpp")) == "cpp/x/cpp/b.hpp"
    assert repo_relative(MullPath("/home/srccpp/cpp/src/a.cpp")) == "cpp/src/a.cpp"
    assert repo_relative(MullPath("/usr/include/c++/vector")) == "/usr/include/c++/vector"
    assert repo_relative(MullPath("/opt/libcpp/cpplib/a.hpp")) == "/opt/libcpp/cpplib/a.hpp"
