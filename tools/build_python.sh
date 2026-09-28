#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Builds CPython from the python.org source release named by the first argument
# (3.15.0, or a pre-release such as 3.15.0rc2) and installs it into the prefix
# given as the second, with `make altinstall`, so the prefix gains pythonX.Y and
# never a bare python3.
#
# The tarball is verified against its Sigstore bundle, which the release
# manager's identity signs, before it is unpacked.  The build uses the project's
# compiler, clang-23, with PGO, LTO, the tail-calling interpreter and BOLT.  It
# has every optional module a Linux build can have: PYTHONSTRICTEXTENSIONBUILD
# makes CPython's own module check fail the build when a module's dependency is
# missing or a built module fails to import, so a build that finishes has them
# all, and only the modules configure disables for another platform are absent.
# Beyond the modules, --with-dtrace adds the USDT probes and
# --enable-loadable-sqlite-extensions lets sqlite3 load extensions.  tkinter
# links the system Tk 9.0, which draws its fonts through Xft and fontconfig;
# configure would take the distribution's default Tk, so its flags are given,
# and the build is refused unless _tkinter reports that version.
#
# Needs cosign, curl, taskset and the packages "Python interpreter from source"
# in docs/development/BUILDING.md lists.  The build runs on CPUs 0-19.
set -euo pipefail

llvm=23
tk=9.0
[ $# -eq 2 ] || { echo "usage: build_python.sh <version> <prefix>" >&2; exit 2; }
version=$1
prefix=$2
base=${version%%[a-z]*}
minor=${base%.*}

# The Sigstore identity that signs each release series, from
# https://www.python.org/downloads/metadata/sigstore/.
case $minor in
    3.14 | 3.15) identity=hugo@python.org ;;
    *)
        echo "build_python: no signing identity recorded for $minor; add it from python.org's Sigstore page" >&2
        exit 1
        ;;
esac

for tool in "clang-$llvm" cosign curl dtrace pkg-config taskset; do
    command -v "$tool" > /dev/null || { echo "build_python: $tool is not on PATH" >&2; exit 1; }
done
for tool in llvm-profdata llvm-ar llvm-bolt merge-fdata; do
    [ -x "/usr/lib/llvm-$llvm/bin/$tool" ] || { echo "build_python: /usr/lib/llvm-$llvm/bin/$tool is missing" >&2; exit 1; }
done

work=$(mktemp -d)
# A failed build keeps its tree, because config.log is where configure says
# which dependency it could not find.
cleanup() {
    if [ "$1" -eq 0 ]; then
        rm -rf "$work"
    else
        echo "build_python: the build tree is kept in $work" >&2
    fi
}
trap 'cleanup $?' EXIT

# Debian's tk9.0.pc requires the generic tcl, which is the default Tcl 8.6; a
# tcl.pc naming Tcl 9.0, first on the search path of these queries alone,
# resolves it to the Tcl that Tk was built against.
mkdir "$work/pkgconfig"
ln -s "$(pkg-config --variable=pcfiledir "tcl$tk")/tcl$tk.pc" "$work/pkgconfig/tcl.pc"
tcltk() {
    PKG_CONFIG_PATH=$work/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH} \
        pkg-config --print-errors "$@" "tcl$tk" "tk$tk"
}
if ! tcltk_cflags=$(tcltk --cflags) || ! tcltk_libs=$(tcltk --libs); then
    echo "build_python: pkg-config cannot resolve tcl$tk and tk$tk" >&2
    exit 1
fi

tarball=Python-$version.tar.xz
url=https://www.python.org/ftp/python/$base/$tarball
curl -fsSL --retry 5 --retry-all-errors -o "$work/$tarball" "$url"
curl -fsSL --retry 5 --retry-all-errors -o "$work/$tarball.sigstore" "$url.sigstore"
cosign verify-blob --new-bundle-format --bundle "$work/$tarball.sigstore" \
    --certificate-identity "$identity" --certificate-oidc-issuer https://github.com/login/oauth \
    "$work/$tarball"
tar -xf "$work/$tarball" -C "$work"

# LLVM 23's BOLT instrumentation reserves a large diagnostic buffer in the
# functions it instruments (https://github.com/llvm/llvm-project/issues/225479),
# so the instrumented interpreter overflows its stack in these tests, which
# recurse in C until they expect a RecursionError, before CPython's own guard
# fires.  The profile runs leave them out; the finished interpreter runs their
# files whole below.
profile_task="-m test --pgo --timeout=\$(TESTTIMEOUT)"
for test in test.test_functools.TestLRUC.test_lru_recursion \
    'test.test_functools.*.test_recursive_pickle' \
    test.test_json.test_recursion.TestCRecursion.test_endless_recursion \
    test.test_xml_etree_c.BadElementTest.test_deeply_nested_deepcopy; do
    profile_task+=" --ignore '$test'"
done

# configure finds the LLVM tools by their unversioned names.
export PATH=/usr/lib/llvm-$llvm/bin:$PATH
export PYTHONSTRICTEXTENSIONBUILD=1
cd "$work/Python-$version"
taskset -c 0-19 ./configure --prefix="$prefix" CC="clang-$llvm" CXX="clang++-$llvm" \
    --enable-optimizations --with-lto --with-tail-call-interp --enable-bolt \
    --with-system-expat --with-system-libmpdec \
    --with-dtrace --enable-loadable-sqlite-extensions \
    TCLTK_CFLAGS="$tcltk_cflags" TCLTK_LIBS="$tcltk_libs" PROFILE_TASK="$profile_task"
taskset -c 0-19 make -j20
taskset -c 0-19 ./python -m test -j20 test_functools test_json test_xml_etree_c
./python -c "import sys, tkinter; sys.exit(f'_tkinter links Tk {tkinter.TkVersion}' if str(tkinter.TkVersion) != '$tk' else 0)"
taskset -c 0-19 make altinstall
echo "build_python: $prefix/bin/python$minor"
