# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Bundle-consumer fixture (C++): a minimal downstream CMake project wired to
# an unpacked Aletheia release bundle exactly the way the bundle's install.sh
# instructs.  tools/bundle_validate.py extracts the add_subdirectory +
# target_link_libraries lines VERBATIM from the captured installer output into
# a recipe file and passes its path as ALETHEIA_RECIPE_CMAKE.  The executable
# target is named your_app because that is the target name the printed recipe
# links against — the recipe users read is the recipe this project builds with.
cmake_minimum_required(VERSION 3.25)
project(aletheia-bundle-consumer LANGUAGES CXX)

if(NOT DEFINED ALETHEIA_RECIPE_CMAKE)
    message(FATAL_ERROR
            "Pass -DALETHEIA_RECIPE_CMAKE=<file holding the recipe lines printed by install.sh>")
endif()

add_executable(your_app main.cpp)

# The recipe lines printed by the bundle's install.sh, injected verbatim.
# The bundled binding propagates its language requirements (cxx_std_23) and
# include directories through the aletheia::aletheia-cpp target.
include("${ALETHEIA_RECIPE_CMAKE}")
