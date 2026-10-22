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
//! the instrumentation a coverage run sets. Each runs against the forwarding
//! stand-in kernel, which hands every call to the library and logs every
//! refusal it answers: a fence fails unless the kernel refused exactly the
//! codes a `<!-- refuses: <code> ... -->` line directly above it names, so a
//! fence that discards a refused call fails too.

mod instrumentation;
mod stand_in;

use std::env;
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
    /// The codes the line directly above names, in order.
    refuses: Vec<String>,
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

/// The codes a line names when it is the mark directly above a fence that
/// shows refusals, in the order the kernel answers them; none for any other
/// line.
fn stated_refusals(line: &str) -> Vec<String> {
    let Some(codes) = line
        .strip_prefix("<!-- refuses: ")
        .and_then(|rest| rest.strip_suffix(" -->"))
    else {
        return Vec::new();
    };
    let named: Vec<String> = codes.split(' ').map(str::to_owned).collect();
    let well_formed = named.iter().all(|code| {
        !code.is_empty()
            && code
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
    });
    if well_formed {
        named
    } else {
        Vec::new()
    }
}

/// The code of each refusal the forwarding stand-in logged, in order: a line
/// is the entry, a tab and the kernel's envelope. No file is no refusal.
fn refusal_codes(log: &Path) -> Vec<String> {
    let Ok(text) = fs::read_to_string(log) else {
        return Vec::new();
    };
    text.lines()
        .map(|line| {
            line.split_once("\"code\": \"")
                .and_then(|(_, rest)| rest.split_once('"'))
                .map(|(code, _)| code.to_owned())
                .unwrap_or_else(|| panic!("an unreadable refusal log line: {line}"))
        })
        .collect()
}

/// Every Rust fence of one document: an opening line the harness runs, closed
/// by a line that is exactly the fence.
fn extract_rust_fences(doc: &str) -> Vec<RustFence> {
    let path = repo_root().join(doc);
    let text =
        fs::read_to_string(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
    let mut fences = Vec::new();
    let mut open: Option<(usize, String, Vec<String>)> = None;
    let mut previous = "";
    for (index, line) in text.lines().enumerate() {
        match &mut open {
            None => {
                if rust_fence_opening(line) == FenceOpening::Run {
                    open = Some((index + 1, String::new(), stated_refusals(previous)));
                }
                previous = line;
            }
            Some((start, body, refuses)) => {
                if line.trim() == "```" {
                    fences.push(RustFence {
                        doc: doc.to_owned(),
                        line: *start,
                        content: std::mem::take(body),
                        refuses: std::mem::take(refuses),
                    });
                    open = None;
                    previous = line;
                } else {
                    body.push_str(line);
                    body.push('\n');
                }
            }
        }
    }
    if let Some((start, _, _)) = open {
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

/// Denies a statement that drops a `Result`: an error a binding raised
/// itself, which the forwarding stand-in kernel never sees, cannot be thrown
/// away by a bare call.
const DENY_DROPPED_RESULTS: &str = "#![deny(unused_must_use)]\n";

/// The check a value the example binds and never reads is handed to: the
/// forwarding stand-in kernel sees only the kernel's refusals, and a binding
/// refuses some inputs itself (an identifier out of range, a DLC above 15),
/// so an example keeping such an `Err` unread would pass on its exit status.
/// The macro picks the check by the value's type: a `Result` ends the run
/// naming the line when it is an `Err`, any other value passes through.
const UNREAD_CHECK: &str = "\
macro_rules! doc_example_unread {
    ($at:expr, $value:expr) => {{
        let value = $value;
        #[allow(unused_imports)]
        use crate::doc_example_kept::{Checked as _, Unchecked as _};
        (&crate::doc_example_kept::Kept(&value)).doc_check($at);
        value
    }};
}
mod doc_example_kept {
    pub struct Kept<'a, T>(pub &'a T);
    pub trait Checked {
        fn doc_check(&self, at: &str);
    }
    impl<T, E: std::fmt::Debug> Checked for Kept<'_, Result<T, E>> {
        fn doc_check(&self, at: &str) {
            if let Err(error) = self.0 {
                panic!(\"the example discards an error at {at}: {error:?}\");
            }
        }
    }
    pub trait Unchecked {
        fn doc_check(&self, at: &str);
    }
    impl<T> Unchecked for &Kept<'_, T> {
        fn doc_check(&self, _: &str) {}
    }
}
";

fn is_word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// The offset of the `;` ending the statement whose text starts at `from`:
/// the first outside brackets, string and character literals and line
/// comments.
fn statement_end(text: &str, from: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0i32;
    let mut i = from;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
            }
            // A character literal, which a lifetime is not: 'x' or '\x'.
            b'\'' if bytes.get(i + 2) == Some(&b'\'') => i += 2,
            b'\'' if bytes.get(i + 1) == Some(&b'\\') && bytes.get(i + 3) == Some(&b'\'') => i += 3,
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                i = text[i..].find('\n').map_or(bytes.len(), |n| i + n);
            }
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b';' if depth == 0 => return Some(i),
            _ => {}
        }
        i += 1;
    }
    None
}

/// The name a line binds and the offset in the line where its value starts:
/// `let [mut] name [: Type] = value`, `name` not the bare underscore.
fn let_binding(line: &str) -> Option<(&str, usize)> {
    let rest = line.trim_start().strip_prefix("let ")?.trim_start();
    let rest = rest.strip_prefix("mut ").unwrap_or(rest).trim_start();
    let name_len = rest.bytes().take_while(|b| is_word(*b)).count();
    let name = &rest[..name_len];
    let after = &rest[name_len..];
    let head = after.trim_start();
    if name.is_empty() || name == "_" || !(head.starts_with('=') || head.starts_with(':')) {
        return None;
    }
    let value = after[after.find('=')? + 1..].trim_start();
    Some((name, line.len() - value.len()))
}

/// Whether `text` names `name` as a word, outside lines that only drop it
/// (`let _ = name;`).
fn reads(text: &str, name: &str) -> bool {
    let dropped = format!("let _ = {name};");
    text.lines()
        .filter(|line| line.trim() != dropped)
        .any(|line| {
            line.match_indices(name).any(|(at, _)| {
                let bytes = line.as_bytes();
                let before = at.checked_sub(1).map(|b| bytes[b]);
                let after = bytes.get(at + name.len()).copied();
                !before.is_some_and(is_word) && !after.is_some_and(is_word)
            })
        })
}

/// The program with each `let name = ...;` whose value calls something
/// without `?` and whose name the rest of the program never reads handed to
/// `doc_example_unread!`, so the value is checked where it is kept, which is
/// where it is last seen. `place[k]` names the document line of line `k`.
fn unread_results(program: &str, place: &[String]) -> String {
    let mut starts = vec![0usize];
    starts.extend(program.match_indices('\n').map(|(at, _)| at + 1));
    let mut out = String::new();
    let mut done = 0usize;
    for (k, &start) in starts.iter().enumerate() {
        if start < done || k >= place.len() {
            continue;
        }
        let line = program[start..].lines().next().unwrap_or("");
        let Some((name, value_at)) = let_binding(line) else {
            continue;
        };
        // The value starts at its first character, on the next line when the
        // binding breaks after its `=`.
        let after_equals = &program[start + value_at..];
        let init = start + value_at + after_equals.len() - after_equals.trim_start().len();
        let Some(end) = statement_end(program, init) else {
            continue;
        };
        let value = &program[init..end];
        let calls = value
            .as_bytes()
            .windows(2)
            .any(|pair| is_word(pair[0]) && pair[1] == b'(');
        if !calls || value.contains('?') || reads(&program[end..], name) {
            continue;
        }
        out.push_str(&program[done..init]);
        out.push_str(&format!("doc_example_unread!({:?}, {value})", place[k]));
        done = end;
    }
    out.push_str(&program[done..]);
    out
}

/// The document line of each line of a fence's content.
fn fence_lines(fence: &RustFence) -> Vec<String> {
    (0..fence.content.lines().count())
        .map(|k| format!("{}:L{}", fence.doc, fence.line + 1 + k))
        .collect()
}

#[test]
fn an_unread_value_is_handed_to_the_check_and_a_read_one_is_not() {
    let place: Vec<String> = (1..=4).map(|k| format!("d.md:L{k}")).collect();
    for (program, want) in [
        (
            "let r = client.end_stream();\n",
            "let r = doc_example_unread!(\"d.md:L1\", client.end_stream());\n",
        ),
        (
            "let r = Dlc::new(\n    8,\n);\nlet _ = r;\n",
            "let r = doc_example_unread!(\"d.md:L1\", Dlc::new(\n    8,\n));\nlet _ = r;\n",
        ),
        (
            "let mut r: Result<Dlc, Error> = Dlc::new(8);\n",
            "let mut r: Result<Dlc, Error> = doc_example_unread!(\"d.md:L1\", Dlc::new(8));\n",
        ),
        (
            "let r =\n    Dlc::new(8);\n",
            "let r =\n    doc_example_unread!(\"d.md:L1\", Dlc::new(8));\n",
        ),
        (
            "let r = Dlc::new(8);\nuse_it(r);\n",
            "let r = Dlc::new(8);\nuse_it(r);\n",
        ),
        ("let r = Dlc::new(8)?;\n", "let r = Dlc::new(8)?;\n"),
        ("let n = 3;\n", "let n = 3;\n"),
    ] {
        assert_eq!(unread_results(program, &place), want, "{program:?}");
    }
}

/// A line binding the result of a call made without `?` to a name starting
/// with an underscore: it keeps a `Result` the fence never looks at, an error
/// in it passing on the program's exit status.
fn ignores_a_result(line: &str) -> bool {
    let Some((name, value)) = line
        .trim_start()
        .strip_prefix("let _")
        .and_then(|rest| rest.split_once('='))
    else {
        return false;
    };
    let calls = value
        .as_bytes()
        .windows(2)
        .any(|pair| (pair[0].is_ascii_alphanumeric() || pair[0] == b'_') && pair[1] == b'(');
    name.trim()
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && calls
        && value.trim_end().ends_with(';')
        && !line.contains('?')
}

#[test]
fn a_line_ignores_a_result_when_it_binds_a_call_without_a_question_mark() {
    for (line, want) in [
        ("    let _ = client.end_stream();", true),
        ("let _kept = Dlc::new(8);", true),
        ("let _ = client.end_stream()?;", false),
        (
            "let _parsed = client.parse_dbc_text(dbc)?; // a comment",
            false,
        ),
        ("let _ = r;", false),
        ("let _ = (&parsed.dbc, &parsed.warnings);", false),
        ("let kept = Dlc::new(8);", false),
    ] {
        assert_eq!(ignores_a_result(line), want, "{line:?}");
    }
}

#[test]
fn no_rust_fence_binds_a_call_s_result_to_ignore_it() {
    let found: Vec<String> = DOC_FILES
        .iter()
        .chain(PATH_DOCS.iter())
        .flat_map(|doc| extract_rust_fences(doc))
        .flat_map(|fence| {
            fence
                .content
                .lines()
                .enumerate()
                .filter(|(_, line)| ignores_a_result(line))
                .map(|(k, line)| format!("{}:L{}: {}", fence.doc, fence.line + 1 + k, line.trim()))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(
        found.is_empty(),
        "a fence keeps a Result it never looks at; propagate it with `?` or read it:\n{}",
        found.join("\n")
    );
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
        return header
            + DENY_DROPPED_RESULTS
            + UNREAD_CHECK
            + &unread_results(&fence.content, &fence_lines(fence));
    }
    let dbc = repo_root().join("python/tests/fixtures/dbc_corpus/minimal.dbc");
    format!(
        "{header}\
         // the fence may leave any predeclared name or import unused\n\
         #![allow(unused)]\n\
         {DENY_DROPPED_RESULTS}\
         {UNREAD_CHECK}\
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
        content = unread_results(&fence.content, &fence_lines(fence)),
    )
}

/// `command` with none of the instrumentation a coverage run sets: the nested
/// build and the programs it makes carry none of it.
fn uninstrumented(mut command: Command) -> Command {
    for key in instrumentation::variables() {
        command.env_remove(key);
    }
    command
}

#[test]
fn every_rust_fence_of_the_listed_documents_builds_and_runs() {
    let lib = env::var_os("ALETHEIA_LIB")
        .expect("ALETHEIA_LIB names the built libaletheia-ffi.so the fences run against");
    let forwarder = stand_in::stand_in("forwarding_kernel");
    // Each program as its name in a failure, the stem of its binary, its
    // source and the refusals its marks name: every fence of a listed
    // document, then every path whole.
    let programs: Vec<(String, String, String, Vec<String>)> = DOC_FILES
        .iter()
        .flat_map(|doc| extract_rust_fences(doc))
        .enumerate()
        .map(|(i, fence)| {
            let source = program(&fence);
            (fence.name(), format!("fence_{i}"), source, fence.refuses)
        })
        .chain(PATH_DOCS.iter().enumerate().map(|(i, doc)| {
            let fences = extract_rust_fences(doc);
            let joined: String = fences.iter().map(|fence| fence.content.as_str()).collect();
            let place: Vec<String> = fences.iter().flat_map(fence_lines).collect();
            let steps = unread_results(&joined, &place);
            (
                format!("{doc} (its Rust path whole)"),
                format!("path_{i}"),
                format!(
                    "// {doc}, its Rust path joined by the doc-example harness\n\
                     {DENY_DROPPED_RESULTS}{UNREAD_CHECK}{steps}"
                ),
                fences.into_iter().flat_map(|fence| fence.refuses).collect(),
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
    for (_, stem, source, _) in &programs {
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
    for (name, stem, _, refuses) in &programs {
        let bin = built.join(stem);
        if !bin.is_file() {
            failures.push(format!("{name} does not build (src/bin/{stem}.rs)"));
            continue;
        }
        let log = built.join(format!("{stem}.refusals"));
        if log.exists() {
            fs::remove_file(&log).expect("remove an earlier run's refusal log");
        }
        let run = uninstrumented(Command::new(&bin))
            .env("ALETHEIA_LIB", &forwarder)
            .env("ALETHEIA_FORWARD_TO", &lib)
            .env("ALETHEIA_REFUSAL_LOG", &log)
            .output()
            .expect("run a program");
        if !run.status.success() {
            failures.push(format!(
                "{name} failed ({}):\n{}{}",
                run.status,
                String::from_utf8_lossy(&run.stdout),
                String::from_utf8_lossy(&run.stderr)
            ));
            continue;
        }
        let refused = refusal_codes(&log);
        if &refused != refuses {
            failures.push(format!(
                "{name}: the kernel refused {refused:?}, the fence states {refuses:?}: an example \
                 that shows a refusal names its codes on a `<!-- refuses: <code> ... -->` line \
                 directly above its fence\n{}",
                fs::read_to_string(&log).unwrap_or_default()
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
