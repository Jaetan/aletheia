# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# A project of its own that finds the installed C++ package, as a downstream
# user's does, and links one program per surface whose symbols sit behind a
# dependency of the library: the client, the YAML loader and the Excel loader.
# tools/check_cpp_installed_consumer.py configures it with CMAKE_PREFIX_PATH
# naming the prefix it installed the package to.
cmake_minimum_required(VERSION 3.25)
project(aletheia-installed-consumer LANGUAGES CXX)

find_package(aletheia-cpp REQUIRED CONFIG)

foreach(program client yaml_loader excel_loader)
    add_executable(${program} ${program}.cpp)
    target_link_libraries(${program} PRIVATE aletheia::aletheia-cpp)
endforeach()
