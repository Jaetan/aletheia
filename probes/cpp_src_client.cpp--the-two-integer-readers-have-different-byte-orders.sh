#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/client.cpp and cpp/src/detail/loader_utils.cpp.
# Claim: the binding's two multi-byte integer readers are not a clone. The
# binary extraction layout carries the host's byte order, which is what the
# kernel writes, and the ZIP records an .xlsx carries are little-endian
# whatever the host is. Merging them would be correct only under the
# assertion that forbids a big-endian build, so the two stay separate and
# each says which order it reads. This probe records a candidate dismissed,
# so a later round re-runs it instead of re-suspecting the clone.
# Non-zero exit: either reader stops naming its byte order, the kernel stops
# documenting the layout as native, or the host assertion goes away.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

grep -q 'native byte order' src/Aletheia/Main/Binary.agda || {
    echo "the kernel no longer documents the binary layout as native byte order"
    status=1
}
grep -q 'read_native' cpp/src/client.cpp || {
    echo "the binary-layout reader no longer names the host order it reads"
    status=1
}
grep -q 'read_le' cpp/src/client.cpp && {
    echo "the binary-layout reader claims a little-endian read of a native-order wire"
    status=1
}
grep -q 'always LE per APPNOTE' cpp/src/detail/loader_utils.cpp || {
    echo "the ZIP readers no longer state that their byte order is the format's"
    status=1
}
grep -q 'std::endian::native == std::endian::little' cpp/src/client.cpp || {
    echo "the host-order assertion is gone, so the two readers may now disagree"
    status=1
}
exit $status
