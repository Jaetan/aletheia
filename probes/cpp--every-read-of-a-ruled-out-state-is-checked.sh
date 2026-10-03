#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src and cpp/include.
# Claim: the library reads no state a check has ruled out without a checked
# read. Every value of an optional or an expected is read through value(),
# every subscript, front and back of a vector, an array or a string through
# at(), every error of an expected through detail::error_of, every slice of a
# span through detail::subspan_at, and every narrowing of a string view
# through substr(); a span's front and back have no checked form in C++23 and
# are not held. The only unchecked reads are the two helpers' own, in
# cpp/include/aletheia/detail/checked.hpp. Read by clang-query over every
# translation unit the build compiles, the tests included, since a template a
# public header defines is instantiated there; a match counts where its
# expansion lies in the library's own sources, the test double held out.
# Non-zero exit: 1 when an unchecked read is named; 2 when the census could
# not be taken: clang-query-23, the interpreter or the build's compile
# database missing, or the query failing.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang-query-23 > /dev/null || { echo "clang-query-23 not installed"; exit 2; }
py=python/.venv/bin/python
[ -x "$py" ] || { echo "no $py"; exit 2; }
db=cpp/build/compile_commands.json
[ -f "$db" ] || { echo "no $db: configure cpp/build first"; exit 2; }
mkdir -p tools/ci-output || exit 2
work=$(mktemp -d tools/ci-output/.checked-reads-XXXXXX) || exit 2
trap 'rm -rf "$work"' EXIT
library='"/cpp/(src|include)/.*[.](cpp|hpp)$"'
cat > "$work/census.query" <<EOF
set output diag
set bind-root false
match cxxOperatorCallExpr(anyOf(hasOverloadedOperatorName("*"), hasOverloadedOperatorName("->")), hasArgument(0, expr(hasType(hasUnqualifiedDesugaredType(recordType(hasDeclaration(classTemplateSpecializationDecl(anyOf(hasName("::std::optional"), hasName("::std::expected"))))))))), isExpansionInFileMatching($library)).bind("unchecked value")
match cxxMemberCallExpr(callee(cxxMethodDecl(hasName("error"), ofClass(classTemplateSpecializationDecl(hasName("::std::expected"))))), isExpansionInFileMatching($library)).bind("unchecked error")
match cxxOperatorCallExpr(hasOverloadedOperatorName("[]"), hasArgument(0, expr(hasType(hasUnqualifiedDesugaredType(recordType(hasDeclaration(classTemplateSpecializationDecl(anyOf(hasName("::std::vector"), hasName("::std::array"), hasName("::std::basic_string"), hasName("::std::basic_string_view"))))))))), isExpansionInFileMatching($library)).bind("unchecked subscript")
match cxxMemberCallExpr(callee(cxxMethodDecl(anyOf(hasName("subspan"), hasName("first"), hasName("last")), ofClass(classTemplateSpecializationDecl(hasName("::std::span"))))), isExpansionInFileMatching($library)).bind("unchecked slice")
match cxxMemberCallExpr(callee(cxxMethodDecl(anyOf(hasName("remove_prefix"), hasName("remove_suffix")), ofClass(classTemplateSpecializationDecl(hasName("::std::basic_string_view"))))), isExpansionInFileMatching($library)).bind("unchecked narrowing")
match cxxMemberCallExpr(callee(cxxMethodDecl(anyOf(hasName("front"), hasName("back")), ofClass(classTemplateSpecializationDecl(anyOf(hasName("::std::vector"), hasName("::std::array"), hasName("::std::basic_string"), hasName("::std::basic_string_view")))))), isExpansionInFileMatching($library)).bind("unchecked end")
EOF
# Every translation unit of the project's own, out of the compile database.
"$py" - "$db" > "$work/units" <<'PY' || exit 2
import json
import sys

units = sorted({entry["file"] for entry in json.load(open(sys.argv[1], encoding="utf-8"))
                if "/cpp/" in entry["file"] and "/_deps/" not in entry["file"]})
print("\n".join(units))
PY
[ -s "$work/units" ] || { echo "the compile database names no unit"; exit 2; }
mapfile -t units < "$work/units"
clang-query-23 -p cpp/build -f "$work/census.query" "${units[@]}" > "$work/census.log" 2>&1 || {
    tail -5 "$work/census.log"
    echo "the query failed, so the census was not taken"
    exit 2
}
grep -oE '^.+:[0-9]+:[0-9]+: note: "unchecked [a-z]+" binds here' "$work/census.log" |
    grep -vE '/cpp/include/aletheia/detail/checked\.hpp:|/cpp/src/detail/mock_backend\.hpp:' |
    sed -E 's#^.*/(cpp/[^:]+:[0-9]+):[0-9]+: note: "(unchecked [a-z]+)" binds here#\1 \2#' |
    sort -u > "$work/hits"
if [ -s "$work/hits" ]; then
    cat "$work/hits"
    exit 1
fi
echo "every read of a ruled-out state is checked over ${#units[@]} units"
