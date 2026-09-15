# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/cmake/aletheia-cpp-config.cmake.in.
# Claim: after `cmake --install`, a separate project that finds the package
# with find_package(aletheia-cpp REQUIRED CONFIG) can link a program that uses
# the YAML check loader, whose symbols sit behind the library's yaml-cpp
# dependency. Non-zero exit: the install, the find or the link fails, which is
# the state this probe records until the export carries or installs that
# dependency. Exits 2 when cpp/build is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
scratch=cpp/build/probe-scratch/installed-consumer-loader
rm -rf "$scratch"; mkdir -p "$scratch/consumer" || exit 2
cmake --build cpp/build --target aletheia-cpp > "$scratch/build.log" 2>&1 || { tail -3 "$scratch/build.log"; exit 1; }
cmake --install cpp/build --prefix "$scratch/prefix" > "$scratch/install.log" 2>&1 || { tail -5 "$scratch/install.log"; exit 1; }
cat > "$scratch/consumer/CMakeLists.txt" <<CMAKE
cmake_minimum_required(VERSION 3.25)
project(consumer LANGUAGES CXX)
find_package(aletheia-cpp REQUIRED CONFIG)
add_executable(yaml_user yaml_user.cpp)
target_link_libraries(yaml_user PRIVATE aletheia::aletheia-cpp)
CMAKE
cat > "$scratch/consumer/yaml_user.cpp" <<CPP
#include <aletheia/yaml.hpp>
int main() {
    auto checks = aletheia::load_checks_from_yaml("does-not-exist.yaml");
    return checks ? 1 : 0;
}
CPP
cmake -S "$scratch/consumer" -B "$scratch/consumer/build" -DCMAKE_CXX_COMPILER=clang++-22 \
    -DCMAKE_PREFIX_PATH="$(pwd)/$scratch/prefix" > "$scratch/configure.log" 2>&1 || { tail -5 "$scratch/configure.log"; exit 1; }
cmake --build "$scratch/consumer/build" > "$scratch/consumer-build.log" 2>&1 || { grep -m3 -E 'error|undefined' "$scratch/consumer-build.log"; exit 1; }
"$scratch/consumer/build/yaml_user"
