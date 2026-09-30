// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The doc-example harness, the Rust counterpart of the Python one under
//! `pytest --markdown-docs` and of the Go and C++ harnesses: every Rust fence
//! of the documents [`DOC_FILES`] lists is built as a program and run against
//! the kernel, and a fence that fails to build or to run fails the test under
//! its file and line. A fence declaring `fn main` is a program as it stands;
//! any other is a body fragment, placed inside a synthesised `main` returning
//! `Result<(), aletheia::Error>` under `use aletheia::*`, after a client that
//! has loaded the kernel and parsed the Rust suite's minimal DBC, and `ts`,
//! `id`, `dlc` and `data` for one frame of its first message. The Rust fences
//! of a document [`PATH_DOCS`] lists are one program cut into steps, joined in
//! order and run whole. A fence that cannot run opens with tildes, which the
//! extractor does not read.
//!
//! Two structural gates hold the lists to the tree the way the Python
//! harness's list is held: a tracked document with a Rust fence is listed, and
//! a listed one is tracked and carries one. A third refuses a Rust fence
//! hidden from the extractor behind a suffixed info word, and a fourth keeps a
//! floor under the number of fences the listed documents carry.
//!
//! The fences are the binaries of one scratch crate under the target's
//! temporary directory, built by a cargo of their own that inherits none of
//! the instrumentation a coverage run sets.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::process::Command;

/// Every tracked Markdown file carrying a Rust fence, less those [`PATH_DOCS`]
/// names, relative to the repository root. Code no check runs opens with
/// tildes, which the extractor does not read.
const DOC_FILES: [&str; 4] = [
    "docs/PITCH.md",
    "docs/development/DISTRIBUTION.md",
    "docs/reference/INTERFACES.md",
    "docs/reference/RUST_API.md",
];

/// The tracked documents whose Rust fences, read in order, are one program
/// cut into steps: the Tutorial's Rust path.
const PATH_DOCS: [&str; 1] = ["docs/guides/TUTORIAL.md"];

/// One Rust fence of a document.
struct RustFence {
    doc: String,
    /// 1-based line of the opening fence.
    line: usize,
    content: String,
}

impl RustFence {
    fn name(&self) -> String {
        format!("{}:L{}", self.doc, self.line)
    }
}

fn crate_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn repo_root() -> &'static Path {
    crate_dir()
        .parent()
        .expect("the crate sits in the repository")
}

/// What a line opens, read by the first word of its info string. An info
/// string holding a backtick opens nothing, CommonMark reading the line as
/// inline code.
#[derive(Debug, PartialEq, Eq)]
enum FenceOpening {
    /// Any other line.
    Other,
    /// The harness's reading: leading blanks stripped, then a fence whose info
    /// string's first word is exactly `rust`.
    Run,
    /// `rust` followed by ASCII punctuation (`rust,ignore`): a reader still
    /// takes the fence for Rust, and the harness neither runs nor counts it.
    Hidden,
}

fn rust_fence_opening(line: &str) -> FenceOpening {
    let Some(rest) = line.trim_start_matches([' ', '\t']).strip_prefix("```rust") else {
        return FenceOpening::Other;
    };
    match rest.bytes().next() {
        _ if rest.contains('`') => FenceOpening::Other,
        None | Some(b' ' | b'\t') => FenceOpening::Run,
        Some(next) if next.is_ascii_punctuation() && next != b'_' => FenceOpening::Hidden,
        Some(_) => FenceOpening::Other,
    }
}

/// Every Rust fence of one document: an opening line the harness runs, closed
/// by a line that is exactly the fence.
fn extract_rust_fences(doc: &str) -> Vec<RustFence> {
    let path = repo_root().join(doc);
    let text =
        fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
    let mut fences = Vec::new();
    let mut open: Option<(usize, String)> = None;
    for (index, line) in text.lines().enumerate() {
        match &mut open {
            None => {
                if rust_fence_opening(line) == FenceOpening::Run {
                    open = Some((index + 1, String::new()));
                }
            }
            Some((start, body)) => {
                if line.trim() == "```" {
                    fences.push(RustFence {
                        doc: doc.to_owned(),
                        line: *start,
                        content: std::mem::take(body),
                    });
                    open = None;
                } else {
                    body.push_str(line);
                    body.push('\n');
                }
            }
        }
    }
    if let Some((start, _)) = open {
        panic!("{doc}: unterminated ```rust fence opened at line {start}");
    }
    fences
}

/// Every tracked Markdown file, repository-relative, as git lists it: the set
/// a fresh checkout holds, so an untracked file in the working tree is never
/// read.
fn tracked_markdown() -> Vec<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo_root())
        .args(["ls-files", "-z", "--", "*.md", "*.mdx", "*.svx"])
        .output()
        .expect("run git ls-files");
    assert!(out.status.success(), "git ls-files failed ({})", out.status);
    String::from_utf8(out.stdout)
        .expect("git lists paths as UTF-8")
        .split('\0')
        .filter(|path| !path.is_empty())
        .map(str::to_owned)
        .collect()
}

#[test]
fn every_tracked_rust_fence_is_in_a_listed_document() {
    let unlisted: Vec<String> = tracked_markdown()
        .into_iter()
        .filter(|doc| {
            ![&DOC_FILES[..], &PATH_DOCS]
                .iter()
                .any(|list| list.contains(&doc.as_str()))
        })
        .filter(|doc| !extract_rust_fences(doc).is_empty())
        .collect();
    assert!(
        unlisted.is_empty(),
        "Rust fences the harness does not run: {unlisted:?}"
    );
}

#[test]
fn every_listed_document_is_tracked_and_carries_a_rust_fence() {
    let tracked = tracked_markdown();
    let mut problems = Vec::new();
    let listed = [&DOC_FILES[..], &PATH_DOCS].concat();
    for (i, doc) in listed.iter().enumerate() {
        if listed[..i].contains(doc) {
            problems.push(format!("{doc} is listed twice"));
        }
        if !tracked.iter().any(|path| path == doc) {
            problems.push(format!("{doc} is listed and not tracked"));
        }
        if extract_rust_fences(doc).is_empty() {
            problems.push(format!(
                "{doc} carries no Rust fence, so the harness runs nothing in it"
            ));
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// The floor under the number of Rust fences the documents [`DOC_FILES`] lists
/// carry together, so a mass rename cannot silently empty the harness.
const MIN_FENCES: usize = 5;

#[test]
fn the_listed_documents_keep_a_floor_of_rust_fences() {
    let total: usize = DOC_FILES
        .iter()
        .map(|doc| extract_rust_fences(doc).len())
        .sum();
    assert!(
        total >= MIN_FENCES,
        "expected at least {MIN_FENCES} Rust fences across the listed documents, saw {total}"
    );
}

#[test]
fn no_rust_fence_hides_behind_a_suffix() {
    let mut hidden = Vec::new();
    for doc in tracked_markdown() {
        let path = repo_root().join(&doc);
        let text = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
        for (index, line) in text.lines().enumerate() {
            if rust_fence_opening(line) == FenceOpening::Hidden {
                hidden.push(format!("{doc}:{}", index + 1));
            }
        }
    }
    assert!(
        hidden.is_empty(),
        "Rust fences the harness neither runs nor counts, a suffix on their info word: \
         {hidden:?}; write rust, or open a fence that cannot run with tildes"
    );
}

#[test]
fn a_rust_fence_is_read_by_its_first_info_word() {
    for (line, want) in [
        ("```rust", FenceOpening::Run),
        ("   ```rust", FenceOpening::Run),
        ("```rust notest", FenceOpening::Run),
        ("```rust\tx", FenceOpening::Run),
        ("```rust,ignore", FenceOpening::Hidden),
        ("```rust{.x}", FenceOpening::Hidden),
        ("```rust:main.rs", FenceOpening::Hidden),
        ("  ```rust``` / ```go``` block", FenceOpening::Other),
        ("```rust `x`", FenceOpening::Other),
        ("```rust_x", FenceOpening::Other),
        ("```rustc", FenceOpening::Other),
        ("```", FenceOpening::Other),
        ("```text", FenceOpening::Other),
    ] {
        assert_eq!(rust_fence_opening(line), want, "{line:?}");
    }
}

/// The fence as a program: as it stands when it declares `fn main`, otherwise
/// inside the synthesised one.
fn program(fence: &RustFence) -> String {
    let header = format!("// {}, wrapped by the doc-example harness\n", fence.name());
    if fence
        .content
        .lines()
        .any(|line| line.trim_start().starts_with("fn main("))
    {
        return header + &fence.content;
    }
    let dbc = repo_root().join("python/tests/fixtures/dbc_corpus/minimal.dbc");
    format!(
        "{header}\
         // the fence may leave any predeclared name or import unused\n\
         #![allow(unused)]\n\
         use aletheia::*;\n\
         \n\
         const DBC: &str = include_str!({dbc:?});\n\
         \n\
         fn main() -> std::result::Result<(), aletheia::Error> {{\n\
         \x20   let client = Client::new()?;\n\
         \x20   client.parse_dbc_text(DBC)?;\n\
         \x20   let ts = Timestamp(0);\n\
         \x20   let id = CanId::standard(0x100)?;\n\
         \x20   let dlc = Dlc::new(8)?;\n\
         \x20   let data = [0u8; 8];\n\
         \x20   // a nested block, so a fence redeclaring a predeclared name shadows it\n\
         \x20   {{\n\
         {content}\
         \x20   }};\n\
         \x20   Ok(())\n\
         }}\n",
        content = fence.content,
    )
}

/// The variables through which a coverage run instruments what cargo builds,
/// and the prefixes of the ones cargo-llvm-cov adds: the nested build and the
/// programs it makes carry none of them.
const INSTRUMENTATION: [&str; 6] = [
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTDOCFLAGS",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "LLVM_PROFILE_FILE",
];
const INSTRUMENTATION_PREFIXES: [&str; 2] = ["CARGO_LLVM_COV", "__CARGO_LLVM_COV"];

fn is_instrumentation(key: &OsString) -> bool {
    let key = key.to_string_lossy();
    INSTRUMENTATION.contains(&key.as_ref())
        || INSTRUMENTATION_PREFIXES
            .iter()
            .any(|prefix| key.starts_with(prefix))
}

fn uninstrumented(mut command: Command) -> Command {
    for (key, _) in env::vars_os().filter(|(key, _)| is_instrumentation(key)) {
        command.env_remove(key);
    }
    command
}

#[test]
fn every_rust_fence_of_the_listed_documents_builds_and_runs() {
    let lib = env::var_os("ALETHEIA_LIB")
        .expect("ALETHEIA_LIB names the built libaletheia-ffi.so the fences run against");
    // Each program as its name in a failure, the stem of its binary, and its
    // source: every fence of a listed document, then every path whole.
    let programs: Vec<(String, String, String)> = DOC_FILES
        .iter()
        .flat_map(|doc| extract_rust_fences(doc))
        .enumerate()
        .map(|(i, fence)| (fence.name(), format!("fence_{i}"), program(&fence)))
        .chain(PATH_DOCS.iter().enumerate().map(|(i, doc)| {
            let steps: String = extract_rust_fences(doc)
                .iter()
                .map(|fence| fence.content.as_str())
                .collect();
            (
                format!("{doc} (its Rust path whole)"),
                format!("path_{i}"),
                format!("// {doc}, its Rust path joined by the doc-example harness\n{steps}"),
            )
        }))
        .collect();

    let work = Path::new(env!("CARGO_TARGET_TMPDIR")).join("doc_examples");
    let bins = work.join("src").join("bin");
    let target = work.join("target");
    let built = target.join("debug");
    // A program the documents no longer carry must not build from an earlier
    // run's source, nor one that no longer builds run an earlier binary.
    for stale in [&bins, &built] {
        if stale.exists() {
            for entry in fs::read_dir(stale).expect("read the scratch crate") {
                let path = entry.expect("read the scratch crate").path();
                let is_program = path.file_name().is_some_and(|n| {
                    let n = n.to_string_lossy();
                    n.starts_with("fence_") || n.starts_with("path_")
                });
                if is_program && path.is_file() {
                    fs::remove_file(&path).expect("remove an earlier run's program");
                }
            }
        }
    }
    fs::create_dir_all(&bins).expect("create the scratch crate");
    let manifest = format!(
        "[package]\n\
         name = \"aletheia-doc-examples\"\n\
         version = \"0.0.0\"\n\
         edition = \"2021\"\n\
         publish = false\n\
         \n\
         [dependencies]\n\
         aletheia = {{ path = {:?} }}\n\
         \n\
         [workspace]\n",
        crate_dir().display().to_string(),
    );
    fs::write(work.join("Cargo.toml"), manifest).expect("write the scratch manifest");
    // The binding's own lock, so the fences build against the versions its
    // suite does, offline.
    fs::copy(crate_dir().join("Cargo.lock"), work.join("Cargo.lock"))
        .expect("copy the binding's lock");
    for (_, stem, source) in &programs {
        fs::write(bins.join(format!("{stem}.rs")), source).expect("write a program");
    }

    let cargo = env::var_os("CARGO").expect("CARGO, which cargo sets for the tests it runs");
    let build = uninstrumented(Command::new(cargo))
        .args([
            "build",
            "--offline",
            "--bins",
            "--keep-going",
            "--message-format=short",
        ])
        .current_dir(&work)
        .env("CARGO_TARGET_DIR", &target)
        .output()
        .expect("run cargo build");

    let mut failures = Vec::new();
    if !build.status.success() {
        failures.push(format!(
            "cargo build failed ({}):\n{}",
            build.status,
            String::from_utf8_lossy(&build.stderr)
        ));
    }
    for (name, stem, _) in &programs {
        let bin = built.join(stem);
        if !bin.is_file() {
            failures.push(format!("{name} does not build (src/bin/{stem}.rs)"));
            continue;
        }
        let run = uninstrumented(Command::new(&bin))
            .env("ALETHEIA_LIB", &lib)
            .output()
            .expect("run a program");
        if !run.status.success() {
            failures.push(format!(
                "{name} failed ({}):\n{}{}",
                run.status,
                String::from_utf8_lossy(&run.stdout),
                String::from_utf8_lossy(&run.stderr)
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
