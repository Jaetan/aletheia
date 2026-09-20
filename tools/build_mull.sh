#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Builds Mull from source against the system LLVM of the supported Clang and
# installs mull-runner, mull-reporter and the mull-ir-frontend clang plugin
# into ~/.local/bin, or into the directory given as the first argument.
#
# Mull 0.34.1 stops at LLVM 22, so the build applies the patch below: LLVM 23
# joins Mull's supported-version list, and its ubuntu:24.04 and debian:13 maps
# name that version alone, because Mull reads every LLVM directory its map
# names and a leftover /usr/lib/llvm-<n> holding no lib/ aborts the build;
# libirm is taken at the commit that truncates a call replacement's constant to
# the call's return width, because at the commit Mull pins the scalar-call
# mutator builds a 42 for a bool-returning call and LLVM's APInt asserts on it,
# which aborts clang on every source with such a call; libirm also gets the one
# include and the one call LLVM 23 changed (Constant::isZeroValue is gone, and
# a ConstantFP's own isZero together with Constant::isNullValue says the same),
# and its void-call mutator both reaches an invoke and separates the
# destructors a statement runs implicitly from the calls the source writes
# (tools/mull/libirm-void-call-mutator.patch, with Mull's half of the second
# in tools/mull/mull-implicit-destructor-mutator.patch): a void call that can
# throw is an invoke, so testing the Call opcode alone left every throwing
# call unmutated, and an implicit destructor carries its statement's range,
# so one was being reported as the other.  Its scalar-call replacement reaches
# an invoke too (tools/mull/libirm-scalar-call-invoke.patch), for the same
# reason, and it is one file per patch because Bazel matches each patch it is
# given against the archive as extracted.  A Debian release without a
# VERSION_ID in /etc/os-release (testing, sid) is read as the debian:13 row,
# and every mutant gets an identifier of its own
# (tools/mull/mull-unique-mutant-ids.patch), where Mull named two mutations
# of one statement, a temporary's destructor on the normal path and in the
# exception-cleanup landing pad, or two instantiations of one template, by
# one name and ran only the last it registered.
#
# Needs clang-<version>, /usr/lib/llvm-<version> (the llvm-<version>-dev and
# libclang-<version>-dev packages), git and curl.  bazelisk is fetched into the
# install directory and used for the build, whatever bazel PATH carries, so the
# Bazel release Mull's own .bazelversion names is the one that runs.
set -euo pipefail

llvm=23
mull_tag=0.34.1
bazelisk=v1.27.0
dest=${1:-$HOME/.local/bin}

[ -x "/usr/lib/llvm-$llvm/bin/llvm-config" ] || {
    echo "build_mull: /usr/lib/llvm-$llvm is missing; install llvm-$llvm-dev and libclang-$llvm-dev" >&2
    exit 1
}
for tool in "clang-$llvm" git curl; do
    command -v "$tool" > /dev/null || { echo "build_mull: $tool is not on PATH" >&2; exit 1; }
done
mkdir -p "$dest"
bazel=$dest/bazel
curl -fsSL --retry 5 --retry-all-errors -o "$bazel" \
    "https://github.com/bazelbuild/bazelisk/releases/download/$bazelisk/bazelisk-linux-amd64"
chmod +x "$bazel"

src=$(mktemp -d)
trap 'rm -rf "$src"' EXIT
git clone --quiet --depth 1 --branch "$mull_tag" --recursive \
    https://github.com/mull-project/mull "$src"
# libirm's two call mutators are patched, the void-call one to reach an invoke
# and to leave implicit destructors alone, the scalar-call one to reach an
# invoke; the patch files travel with this script and are handed to Bazel as
# labels in the mull workspace.
cp "$(dirname "$0")/mull/libirm-void-call-mutator.patch" "$src/"
cp "$(dirname "$0")/mull/libirm-void-call-mutator-header.patch" "$src/"
cp "$(dirname "$0")/mull/libirm-scalar-call-invoke.patch" "$src/"
git -C "$src" apply - <<'PATCH'
diff --git a/MODULE.bazel b/MODULE.bazel
index 2d6bf93..02e30f1 100644
--- a/MODULE.bazel
+++ b/MODULE.bazel
@@ -144,13 +144,7 @@ mull_supported_llvm_versions.configure(
             "15",
         ],
         "ubuntu:24.04": [
-            "14",
-            "15",
-            "16",
-            "17",
-            "18",
-            "19",
-            "20",
+            "23",
         ],
         "ubuntu:26.04": [
             "17",
@@ -161,9 +155,7 @@ mull_supported_llvm_versions.configure(
             "22",
         ],
         "debian:13": [
-            "17",
-            "18",
-            "19",
+            "23",
         ],
         "rhel:9.6": ["21"],
         "rhel:10.0": ["21"],
@@ -185,6 +177,7 @@ SUPPORTED_LLVM_VERSIONS = [
     "20",
     "21",
     "22",
+    "23",
 ]
 
 available_llvm_versions = use_extension("//:mull_available_llvm_versions.bzl", "available_llvm_versions")
diff --git a/bazel/os_detection.bzl b/bazel/os_detection.bzl
index 004ef56..15137ef 100644
--- a/bazel/os_detection.bzl
+++ b/bazel/os_detection.bzl
@@ -34,7 +34,7 @@ def os_version(repository_ctx):
     if is_macos(repository_ctx):
         result = repository_ctx.execute(["sw_vers", "--productVersion"])
         return result.stdout.strip()
-    return _os_release_kv(repository_ctx)["VERSION_ID"]
+    return _os_release_kv(repository_ctx).get("VERSION_ID", "13")
 
 def os_dist_extension(repository_ctx):
     if is_macos(repository_ctx):
diff --git a/mull_deps.bzl b/mull_deps.bzl
--- a/mull_deps.bzl
+++ b/mull_deps.bzl
@@ -153,10 +153,20 @@ def _mull_deps_extension(module_ctx):
                 )
                 http_archive(
                     name = irm_repo_name,
-                    integrity = "sha256-8pmIPDJX0cgDlNljcIcWd73Wb2WB8cgK/086RxOyqrE=",
-                    urls = ["https://github.com/mull-project/libirm/archive/08eab0634575aeb721d07f05daf4a0aad8feba36.zip"],
-                    strip_prefix = "libirm-08eab0634575aeb721d07f05daf4a0aad8feba36",
+                    integrity = "sha256-CvDe8vg+9snrInk7JWLfzXdGHyIs/NzvjXCEpamOI2g=",
+                    urls = ["https://github.com/mull-project/libirm/archive/b1888b732f1c2d166ec88f83912ac296ca32beea.zip"],
+                    strip_prefix = "libirm-b1888b732f1c2d166ec88f83912ac296ca32beea",
                     build_file_content = IRM_BUILD_FILE.format(LLVM_VERSION = version),
+                    patches = [
+                        "//:libirm-void-call-mutator.patch",
+                        "//:libirm-void-call-mutator-header.patch",
+                        "//:libirm-scalar-call-invoke.patch",
+                    ],
+                    patch_args = ["-p1"],
+                    patch_cmds = [
+                        "sed -i '1i #include <llvm/IR/Constants.h>' lib/ConstantReplacement.cpp",
+                        "sed -i 's/constant->isZeroValue()/(llvm::isa<llvm::ConstantFP>(constant) ? llvm::cast<llvm::ConstantFP>(constant)->isZero() : constant->isNullValue())/' lib/ConstantReplacement.cpp",
+                    ],
                 )
 
     return modules.use_all_repos(module_ctx)
PATCH
git -C "$src" apply "$(cd "$(dirname "$0")" && pwd)/mull/mull-unique-mutant-ids.patch"
git -C "$src" apply "$(cd "$(dirname "$0")" && pwd)/mull/mull-implicit-destructor-mutator.patch"
(cd "$src" && "$bazel" build \
    "//rust/mull-tools:mull-runner-$llvm" \
    "//rust/mull-tools:mull-reporter-$llvm" \
    "//:mull-ir-frontend-$llvm")
# Bazel writes its outputs read-only; install replaces an earlier copy that cp
# would refuse to overwrite, and sets the mode the runner and reporter need.
for built in "rust/mull-tools/mull-runner-$llvm" "rust/mull-tools/mull-reporter-$llvm" \
    "mull-ir-frontend-$llvm"; do
    install -m 755 "$src/bazel-bin/$built" "$dest/"
done
echo "build_mull: mull-runner-$llvm, mull-reporter-$llvm and mull-ir-frontend-$llvm are in $dest"
