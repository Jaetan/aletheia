// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Each read of the allocation count reaches the kernel, and the whole
//! unsigned 64-bit count comes back. The real kernel's count moves with
//! whatever the runtime ran, so the one library whose answers are known is the
//! recording kernel the build makes beside the library, which answers 2^63
//! plus the number of reads made before. Its own test binary (= its own process)
//! because a library stays loaded for the process lifetime, and this one must
//! be the first the process loads, so the first read is the process's first.

mod stand_in;

use aletheia::Client;

/// What the recording kernel adds the reads made before to: the count's top
/// bit, so an answer cut to fewer bits or read as signed reads differently.
const BASE: u64 = 1 << 63;

#[test]
fn each_read_reaches_the_kernel_and_carries_the_whole_unsigned_count() {
    std::env::set_var("ALETHEIA_LIB", stand_in::stand_in("recording_kernel"));
    // The client starts the runtime the count is read from.
    let _client = Client::new().expect("a client on the recording kernel");
    assert_eq!(aletheia::allocated_bytes(), Some(BASE), "the first read");
    assert_eq!(
        aletheia::allocated_bytes(),
        Some(BASE + 1),
        "the second read"
    );
}
