// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Every refusal of a reply place is built by `reply_shape::refusal`, which
//! writes the one form. An `Error::Protocol` the crate builds anywhere else is
//! one the form leaves alone: the binary extraction reply's layout, a library
//! that answered no reply at all, a request of the crate's own its encoder
//! could not write, the mock backend's queue, or the async client's worker.
//! Each such site is listed by function with its count, so a protocol error
//! built by hand anywhere else is red, and so is a listed site that no longer
//! builds one. The Rust counterpart of the Go binding's
//! `reply_refusals_one_form_test.go` and the C++ binding's
//! `unit_tests_reply_refusals_one_form.cpp`.
//!
//! The crate's sources are read from `src/lib.rs` along every module it
//! declares, a module under `#[cfg(test)]` and every item under it left
//! unread, as tokens with comments and literals dropped. A site is a use of
//! the path `Error::Protocol` outside a pattern, or of `response::protocol`,
//! the constructor the binary layout's reader calls, outside its definition
//! and the `use` lines. A function is named as it is declared, a method led
//! by the type or trait its `impl` or `trait` block names; what a closure or a
//! nested item builds is its enclosing function's.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// What each function outside the one form builds by hand, keyed by its file
/// below `src/` and its name, and why the form leaves it alone.
const LEFT_ALONE: [(&str, &str, usize); 11] = [
    // The one form itself.
    ("reply_shape.rs", "refusal", 1),
    // The constructor the binary extraction reply's reader calls.
    ("response.rs", "protocol", 1),
    // The binary extraction reply's layout, which the reply proof does not
    // reach: its header, offsets and reasons, and the buffer the entry hands.
    ("response.rs", "decode_extraction_bin", 6),
    ("backend.rs", "take_extraction_buffer", 2),
    // A library that answered no reply: a refusal without its envelope.
    ("backend.rs", "check_buffer_status", 1),
    ("backend/ffi_backend.rs", "parse_decimal", 1),
    ("backend/ffi_backend.rs", "entry_refusal", 1),
    // A request of the crate's own its encoder could not write.
    ("wire_json.rs", "to_text", 1),
    // The mock backend's queue: no response, or one of the other kind.
    ("mock.rs", "MockBackend::pop_json", 2),
    ("mock.rs", "MockBackend::pop_bytes", 2),
    // The async client closed, or its worker stopped.
    ("async_client.rs", "AsyncClient::run", 3),
];

/// A token of Rust source: an identifier or keyword, a number (read as `0`),
/// a lifetime, or punctuation, the two-character operators kept whole.
fn tokens_of(source: &str) -> Vec<String> {
    let chars: Vec<char> = source.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    let at = |k: usize| chars.get(k).copied().unwrap_or('\0');
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '/' && at(i + 1) == '/' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && at(i + 1) == '*' {
            i = past_block_comment(&chars, i);
        } else if c == '"' {
            i = past_string(&chars, i + 1);
        } else if c == '\'' {
            i = past_quote(&chars, i, &mut out);
        } else if c.is_ascii_digit() {
            while is_word_char(at(i)) || (at(i) == '.' && at(i + 1).is_ascii_digit()) {
                i += 1;
            }
            out.push("0".to_owned());
        } else if is_word_char(c) {
            let start = i;
            while is_word_char(at(i)) {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            match (word.as_str(), at(i)) {
                ("r" | "br" | "cr", '"' | '#') if at(i) == '"' || raw_opens(&chars, i) => {
                    i = past_raw(&chars, i);
                }
                ("b" | "c", '"') => i = past_string(&chars, i + 1),
                ("b", '\'') => i = past_quote(&chars, i, &mut Vec::new()),
                _ => out.push(word),
            }
        } else {
            let pair: String = chars[i..chars.len().min(i + 2)].iter().collect();
            let width = if ["::", "=>", "->", "==", "!=", "<=", ">=", "&&", "||"]
                .contains(&pair.as_str())
            {
                2
            } else {
                1
            };
            out.push(chars[i..i + width].iter().collect());
            i += width;
        }
    }
    out
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The index past the block comment opening at `i`, nested ones included.
fn past_block_comment(chars: &[char], mut i: usize) -> usize {
    let mut depth = 0;
    while i < chars.len() {
        if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
            depth += 1;
            i += 2;
        } else if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return i;
            }
        } else {
            i += 1;
        }
    }
    i
}

/// The index past the string whose first character is at `i`.
fn past_string(chars: &[char], mut i: usize) -> usize {
    while i < chars.len() {
        match chars[i] {
            '\\' => i += 2,
            '"' => return i + 1,
            _ => i += 1,
        }
    }
    i
}

/// Whether the hashes at `i` open a raw string.
fn raw_opens(chars: &[char], mut i: usize) -> bool {
    while chars.get(i) == Some(&'#') {
        i += 1;
    }
    chars.get(i) == Some(&'"')
}

/// The index past the raw string whose hashes, or quote, are at `i`.
fn past_raw(chars: &[char], mut i: usize) -> usize {
    let mut hashes = 0;
    while chars.get(i) == Some(&'#') {
        hashes += 1;
        i += 1;
    }
    i += 1;
    while i < chars.len() {
        if chars[i] == '"' && (1..=hashes).all(|k| chars.get(i + k) == Some(&'#')) {
            return i + 1 + hashes;
        }
        i += 1;
    }
    i
}

/// The index past the character literal or the lifetime at `i`, a lifetime
/// pushed onto `out`.
fn past_quote(chars: &[char], i: usize, out: &mut Vec<String>) -> usize {
    if chars.get(i + 1) == Some(&'\\') {
        let mut k = i + 3;
        while k < chars.len() && chars[k] != '\'' {
            k += 1;
        }
        return k + 1;
    }
    if chars.get(i + 2) == Some(&'\'') {
        return i + 3;
    }
    let mut k = i + 1;
    while chars.get(k).copied().is_some_and(is_word_char) {
        k += 1;
    }
    out.push(chars[i..k].iter().collect());
    k
}

/// What a brace opens: a type's or a trait's block, whose methods are named
/// by it; a function's body; or anything else, read for its braces alone.
enum Scope {
    Type(String),
    Function(String),
    Other,
}

/// The index past the item that opens at `i`: through its `;`, or through the
/// block its first brace opens.
fn past_item(tokens: &[String], mut i: usize) -> usize {
    let mut depth = 0;
    while i < tokens.len() {
        match tokens[i].as_str() {
            ";" if depth == 0 => return i + 1,
            "{" => depth += 1,
            "}" => {
                depth -= 1;
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    i
}

/// Whether the tokens at `i` are the attribute `#[cfg(test)]`.
fn is_cfg_test(tokens: &[String], i: usize) -> bool {
    let want = ["#", "[", "cfg", "(", "test", ")", "]"];
    tokens.len() >= i + want.len() && want.iter().zip(&tokens[i..]).all(|(w, t)| w == t)
}

/// The name an `impl` or `trait` header beginning at `i` gives its block: the
/// last identifier outside angle brackets, after `for` when there is one,
/// before the block or a `where`; and the index of the block's brace.
fn block_name(tokens: &[String], i: usize) -> (String, usize) {
    let mut angles = 0;
    let mut name = String::new();
    let mut k = i + 1;
    while k < tokens.len() && tokens[k] != "{" {
        match tokens[k].as_str() {
            "<" => angles += 1,
            ">" => angles -= 1,
            "for" if angles == 0 => name.clear(),
            "where" if angles == 0 => {
                while k < tokens.len() && tokens[k] != "{" {
                    k += 1;
                }
                break;
            }
            word if angles == 0
                && word.chars().next().is_some_and(char::is_alphabetic)
                && !["dyn", "impl", "mut", "unsafe"].contains(&word) =>
            {
                name = word.to_owned();
            }
            _ => {}
        }
        k += 1;
    }
    (name, k)
}

/// Whether the `Error::Protocol` path ending at `end` (its `Protocol` token)
/// stands in a pattern: a match arm, a `let` or `if let`, an or-pattern, a
/// guard, or the pattern of `matches!`.
fn in_pattern(tokens: &[String], end: usize) -> bool {
    let mut k = end + 1;
    if tokens.get(k).map(String::as_str) == Some("(") {
        let mut depth = 0;
        while k < tokens.len() {
            match tokens[k].as_str() {
                "(" => depth += 1,
                ")" => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            k += 1;
        }
        k += 1;
    }
    while tokens.get(k).map(String::as_str) == Some(")") {
        k += 1;
    }
    let after = matches!(
        tokens.get(k).map(String::as_str),
        Some("=>" | "=" | "|" | "if")
    );
    // `matches!(value, <pattern>)`: the path follows the macro's first comma.
    let mut depth = 0;
    let mut back = end.saturating_sub(2);
    let in_matches = loop {
        if back < 3 {
            break false;
        }
        back -= 1;
        match tokens[back].as_str() {
            ")" => depth += 1,
            "(" if depth == 0 => {
                break back >= 2 && tokens[back - 1] == "!" && tokens[back - 2] == "matches";
            }
            "(" => depth -= 1,
            ";" | "{" | "}" => break false,
            _ => {}
        }
    };
    after || in_matches
}

/// Adds each site's count in one file's tokens to `built`, keyed by `file`,
/// and answers the modules the file declares outside `#[cfg(test)]`.
fn count_sites(
    file: &str,
    tokens: &[String],
    built: &mut BTreeMap<(String, String), usize>,
) -> Vec<String> {
    let mut modules = Vec::new();
    let mut scopes: Vec<Scope> = Vec::new();
    let mut pending: Option<(Scope, usize)> = None;
    let mut parens = 0usize;
    let mut i = 0;
    while i < tokens.len() {
        let in_body = scopes.iter().any(|s| matches!(s, Scope::Function(_)));
        if !in_body && is_cfg_test(tokens, i) {
            i = past_item(tokens, i + 7);
            continue;
        }
        let token = tokens[i].as_str();
        if token == "use" {
            while i < tokens.len() && tokens[i] != ";" {
                i += 1;
            }
            continue;
        }
        let site = || match scopes.iter().find(|s| matches!(s, Scope::Function(_))) {
            Some(Scope::Function(name)) => name.clone(),
            _ => "<item level>".to_owned(),
        };
        let builds = match token {
            "Protocol" => {
                i >= 2
                    && tokens[i - 1] == "::"
                    && (tokens[i - 2] == "Error"
                        || (tokens[i - 2] == "Self"
                            && scopes
                                .iter()
                                .any(|s| matches!(s, Scope::Type(t) if t == "Error"))))
                    && !in_pattern(tokens, i)
            }
            "protocol" => i == 0 || tokens[i - 1] != "fn",
            _ => false,
        };
        if builds {
            *built.entry((file.to_owned(), site())).or_default() += 1;
        }
        match token {
            "mod" if !in_body && tokens.get(i + 2).map(String::as_str) == Some(";") => {
                modules.push(tokens[i + 1].clone());
            }
            "impl" | "trait" if !in_body && parens == 0 && pending.is_none() => {
                let (name, brace) = block_name(tokens, i);
                pending = Some((Scope::Type(name), brace));
            }
            "fn" if !in_body && tokens.get(i + 1).is_some() => {
                let qualified = match scopes.iter().rev().find(|s| matches!(s, Scope::Type(_))) {
                    Some(Scope::Type(t)) => format!("{t}::{}", tokens[i + 1]),
                    _ => tokens[i + 1].clone(),
                };
                pending = Some((Scope::Function(qualified), usize::MAX));
                parens = 0;
            }
            "(" | "[" => parens += 1,
            ")" | "]" => parens = parens.saturating_sub(1),
            ";" if parens == 0 && matches!(pending, Some((Scope::Function(_), _))) => {
                pending = None;
            }
            "{" => {
                let opens = match pending.take() {
                    Some((Scope::Type(name), brace)) if brace == i => Scope::Type(name),
                    Some((Scope::Function(name), _)) if parens == 0 => Scope::Function(name),
                    other => {
                        pending = other;
                        Scope::Other
                    }
                };
                scopes.push(opens);
            }
            "}" => {
                scopes.pop();
            }
            _ => {}
        }
        i += 1;
    }
    modules
}

/// The file a module `name` declared in `file` lives in.
fn module_file(file: &Path, name: &str) -> PathBuf {
    let stem = file.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    let dir = file.parent().expect("a source file sits in a directory");
    let base = if stem == "lib" || stem == "mod" {
        dir.to_path_buf()
    } else {
        dir.join(stem)
    };
    let flat = base.join(format!("{name}.rs"));
    if flat.exists() {
        flat
    } else {
        base.join(name).join("mod.rs")
    }
}

/// What each function of the crate builds, every module reached from
/// `src/lib.rs` read.
fn built_by_hand() -> BTreeMap<(String, String), usize> {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut built = BTreeMap::new();
    let mut pending = vec![src.join("lib.rs")];
    while let Some(path) = pending.pop() {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        let file = path
            .strip_prefix(&src)
            .expect("a module below src/")
            .to_string_lossy()
            .replace('\\', "/");
        for name in count_sites(&file, &tokens_of(&source), &mut built) {
            pending.push(module_file(&path, &name));
        }
    }
    built
}

/// No function builds a protocol error itself but those the form leaves
/// alone.
#[test]
fn every_refusal_of_a_reply_place_is_built_by_the_one_form() {
    let built = built_by_hand();
    let listed: BTreeMap<(String, String), usize> = LEFT_ALONE
        .iter()
        .map(|&(file, function, count)| ((file.to_owned(), function.to_owned()), count))
        .collect();
    let unlisted: Vec<String> = built
        .iter()
        .filter(|(site, _)| !listed.contains_key(*site))
        .map(|((file, function), count)| format!("{file}:{function} x{count}"))
        .collect();
    let moved: Vec<String> = listed
        .iter()
        .filter(|(site, count)| built.get(*site) != Some(count))
        .map(|((file, function), count)| {
            let now = built
                .get(&(file.clone(), function.clone()))
                .copied()
                .unwrap_or(0);
            format!("{file}:{function} lists {count}, builds {now}")
        })
        .collect();
    assert!(
        unlisted.is_empty() && moved.is_empty(),
        "protocol errors built outside the one form:\nunlisted: {unlisted:#?}\nmoved: {moved:#?}"
    );
}

/// The reader of the source finds what each kind of site builds, and leaves
/// a pattern, a definition, an import and a test module unread.
#[test]
fn the_source_reader_counts_builds_and_skips_patterns_imports_and_tests() {
    let source = r##"
use crate::response::protocol;
/// Error::Protocol(String) in a comment builds nothing.
impl Error {
    fn show(&self) -> &str {
        match self {
            Error::Protocol(text) => text,
            _ => "",
        }
    }
}
pub(crate) fn protocol(msg: &str) -> Error {
    Error::Protocol(msg.to_owned())
}
fn reader(raw: &str) -> Result<(), Error> {
    let quoted = "Error::Protocol(\"x\")";
    let lifetime: &'static str = r#"Error::Protocol"#;
    if matches!(raw, Error::Protocol(_)) {}
    let _ = |e| Err::<(), Error>(Error::Protocol(e));
    Err(protocol("short")).map_err(Error::Protocol)
}
#[cfg(test)]
mod tests {
    fn planted() -> Error { Error::Protocol(String::new()) }
}
mod declared;
"##;
    let mut built = BTreeMap::new();
    let modules = count_sites("f.rs", &tokens_of(source), &mut built);
    let site = |function: &str| ("f.rs".to_owned(), function.to_owned());
    assert_eq!(
        built,
        BTreeMap::from([(site("protocol"), 1), (site("reader"), 3)])
    );
    assert_eq!(modules, vec!["declared".to_owned()]);
}
