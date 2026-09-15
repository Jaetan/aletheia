# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/detail/mock_backend.hpp.
# Claim: the <binary:OP> sentinels the C++ mock records are exactly the set
# the Python, Go and Rust mock backends record, so a mock-driven test reads
# the same request log in every binding. Non-zero exit: a sentinel exists in
# one binding's mock and not another's.
set -u
cd "$(dirname "$0")/.." || exit 2
tokens() { grep -rhoE '<binary:[A-Za-z]+>' "$@" | sort -u; }
cpp=$(tokens cpp/src/detail/mock_backend.hpp)
py=$(tokens $(grep -rl --include='*.py' '<binary:' python/aletheia | grep -v test))
go=$(tokens $(grep -rl --include='*.go' '<binary:' go/aletheia | grep -v _test))
rs=$(tokens $(grep -rl --include='*.rs' '<binary:' rust/src))
status=0
for name in py go rs; do
    other=$(eval "printf '%s\n' \"\$$name\"")
    if ! diff <(printf '%s\n' "$cpp") <(printf '%s\n' "$other") > /dev/null; then
        echo "cpp mock sentinels differ from $name:"; diff <(printf '%s\n' "$cpp") <(printf '%s\n' "$other") | grep '^[<>]'; status=1
    fi
done
printf 'cpp sentinels: %s\n' "$(printf '%s' "$cpp" | wc -l)"
exit $status
