// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The stand-in kernels `cabal run shake -- build` makes beside the library the
//! tests run against.

use std::path::{Path, PathBuf};

/// The stand-in kernel `name`, from the directory of the library `ALETHEIA_LIB`
/// names: read it before a test points the variable at the stand-in itself.
pub fn stand_in(name: &str) -> PathBuf {
    let lib = std::env::var("ALETHEIA_LIB")
        .expect("ALETHEIA_LIB names the library the tests run against, the stand-ins beside it");
    let path = Path::new(&lib)
        .with_file_name("stand-ins")
        .join(format!("{name}.so"));
    assert!(
        path.exists(),
        "stand-in {} not built; run 'cabal run shake -- build'",
        path.display()
    );
    path
}
