#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the documents the C++, Go and Python doc-example harnesses run.
# Claim: no example discards the answer of a call that failed. Each harness
# judges an example by its exit status, so an example that keeps a result it
# never reads passes whatever the call answered, and demonstrates nothing past
# that line. Every such example is run the way its harness runs it (the same
# prologue, template or globals, the same fixture paths), with one line added
# that reports the discarded answer when it is an error: a C++ result without a
# value, a Go error that is not nil, a Python answer whose status is error. A
# Rust example propagates with `?`, so its arm is static: a `let` binding of a
# call made without `?`.
# Non-zero exit: an example discards a call that failed, or a harness file
# could not be read. A half whose toolchain or built library is missing is
# reported and skipped, the claim being untestable for it.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
"$py" - "$work" <<'PY'
import ast
import contextlib
import io
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path.cwd()
WORK = Path(sys.argv[1])
KERNEL = ROOT / "build/libaletheia-ffi.so"
EXCEL = ROOT / "examples/demo/demo_workbook.xlsx"
failed = []


def fences(doc, lang):
    """The harnesses' rule: leading blanks stripped, the info word exactly the language."""
    out, body, start = [], None, 0
    for n, line in enumerate((ROOT / doc).read_text(encoding="utf-8").splitlines(), 1):
        if body is None:
            t = line.lstrip(" \t")
            if t.startswith("```" + lang) and t[3 + len(lang):][:1] in ("", " ", "\t"):
                body, start = [], n
        elif line.strip() == "```":
            out.append((start, body))
            body = None
        else:
            body.append(line)
    return out


def listed(source, pattern):
    block = re.search(pattern, (ROOT / source).read_text(encoding="utf-8"), re.S)
    if block is None:
        print(f"the document list of {source} could not be read")
        raise SystemExit(2)
    return re.findall(r'"([^"]+)"', block.group(1))


def substitute(body, yaml_fixture):
    for literal, path in (("/opt/aletheia/lib/libaletheia-ffi.so", KERNEL), ("checks.yaml", yaml_fixture),
                          ("checks.xlsx", EXCEL), ("tests.xlsx", EXCEL)):
        body = body.replace(f'"{literal}"', f'"{path}"')
    return body


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, check=False, **kw)


# C++: every body fragment keeping a result it never reads, inside the harness's own prologue.
libcpp = ROOT / "cpp/build/libaletheia-cpp.so"
if shutil.which("clang++-23") and libcpp.is_file() and KERNEL.is_file():
    harness = (ROOT / "cpp/tests/doc_example_tests.cpp").read_text(encoding="utf-8")
    prologue = re.search(r'k_prologue\s*=\s*R"CPP\((.*?)\)CPP"', harness, re.S)
    epilogue = re.search(r'k_epilogue\s*=\s*R"CPP\((.*?)\)CPP"', harness, re.S)
    if prologue is None or epilogue is None:
        print("the C++ harness's wrapper could not be read")
        raise SystemExit(2)
    decl = re.compile(r"\s*(?:\[\[maybe_unused\]\]\s*)?auto\s+(?:const\s+)?(\w+)\s*=\s*.*\w\(")
    for i, (doc, (start, body)) in enumerate(
        (d, f) for d in listed("cpp/tests/doc_example_tests.cpp", r"k_doc_files\s*=\s*\{(.*?)\};")
        for f in fences(d, "cpp")
    ):
        text = "\n".join(body)
        if re.search(r"(^|\n)\s*int\s+main\s*\(|(^|\n)\s*#\s*include\b", text):
            continue
        kept = [(start + k + 1, m.group(1)) for k, line in enumerate(body) if (m := decl.match(line))
                and not re.search(rf"\b{m.group(1)}\b", "\n".join(body[k + 1:]))]
        if not kept:
            continue
        # A generic lambda, so the branch a non-result type discards is never instantiated.
        report = "".join(
            f"[](auto const& kept) {{ if constexpr (requires {{ kept.has_value(); kept.error().message(); }}) "
            f'if (!kept.has_value()) std::cout << "{doc}:{line}: " << kept.error().message() << "\\n"; }}'
            f"({name});\n"
            for line, name in kept)
        src = WORK / f"cpp{i}.cpp"
        src.write_text(prologue.group(1) + substitute(text, ROOT / "cpp/tests/testdata/doc_examples/checks.yaml")
                       + "\n" + report + epilogue.group(1), encoding="utf-8")
        built = run(["clang++-23", "-std=c++23", f"-I{ROOT}/cpp/include", "-o", str(WORK / f"cpp{i}"), str(src),
                     str(libcpp), f"-Wl,-rpath,{libcpp.parent}", "-ldl", "-lpthread"])
        if built.returncode:
            failed.append(f"C++ {doc}:{start}: does not compile\n{built.stderr[-600:]}")
            continue
        ran = run([str(WORK / f"cpp{i}")], env={**os.environ, "ALETHEIA_LIB": str(KERNEL)})
        failed += [f"C++ {line}" for line in ran.stdout.splitlines() if line.startswith(doc)]
else:
    print("no clang++-23, built binding or kernel: the C++ half is untestable")

# Go: every line discarding an error, inside the harness's own template.
if shutil.which("go") and KERNEL.is_file():
    harness = (ROOT / "go/aletheia/doc_examples_test.go").read_text(encoding="utf-8")
    template = re.search(r"const tmpl = `(.*?)`\n", harness, re.S)
    if template is None:
        print("the Go harness's template could not be read")
        raise SystemExit(2)
    go = ROOT / "go"
    (WORK / "go").mkdir()
    (WORK / "go/go.mod").write_text(
        "module probe\n\ngo 1.24.0\n\nrequire (\n\tgithub.com/Jaetan/aletheia/go/v5 v5.0.0\n"
        "\tgithub.com/Jaetan/aletheia/go/excel v0.0.0\n)\n\n"
        f"replace github.com/Jaetan/aletheia/go/v5 => {go}\n\n"
        f"replace github.com/Jaetan/aletheia/go/excel => {go / 'excel'}\n", encoding="utf-8")
    docs = listed("go/aletheia/doc_files_test.go", r"var docFiles = \[\]string\{(.*?)\n\}")
    discard = re.compile(r"(\s*)_(?:\s*,\s*_)*\s*=\s*(.+)$")
    for i, (doc, (start, body)) in enumerate((d, f) for d in docs for f in fences(d, "go")):
        text = "\n".join(body)
        if re.search(r"(^|\n)\s*(package |import[ (])", text):
            continue
        rewritten, hits = [], 0
        for k, line in enumerate(body):
            m = discard.fullmatch(line)
            if m is None or not (re.search(r"\berr\s*$", m.group(2)) or re.match(r"[\w.]+\(", m.group(2))):
                rewritten.append(line)
                continue
            hits += 1
            where = f"{doc}:{start + k + 1}"
            if re.search(r"\berr\s*$", m.group(2)):
                rewritten.append(line)
                probe_err = "err"
            else:
                probe_err = f"probeErr{hits}"
                rewritten.append(f"{m.group(1)}_, {probe_err} := {m.group(2)}")
            rewritten.append(f'{m.group(1)}if e, ok := any({probe_err}).(error); ok && e != nil '
                             f'{{ fmt.Printf("{where}: %v\\n", e) }}')
        if not hits:
            continue
        body_src = substitute("\n".join(rewritten), ROOT / "go/aletheia/testdata/doc_examples/checks.yaml")
        (WORK / f"go/g{i}").mkdir()
        (WORK / f"go/g{i}/main.go").write_text(template.group(1).replace("%s", body_src, 1).replace("%s", "", 1),
                                               encoding="utf-8")
        ran = run(["go", "run", f"./g{i}"], cwd=WORK / "go",
                  env={**os.environ, "GOFLAGS": "-mod=mod", "GOWORK": "off", "ALETHEIA_LIB": str(KERNEL)})
        if ran.returncode:
            failed.append(f"Go {doc}:{start}: does not run\n{(ran.stdout + ran.stderr)[-600:]}")
        failed += [f"Go {line}" for line in ran.stdout.splitlines() if line.startswith(doc)]
else:
    print("no go toolchain or kernel: the Go half is untestable")

# Python: every fence the plugin extracts, run in the repo-root conftest's globals; a top-level call
# made as a statement, or assigned to a name the fence never reads, is reported when it answers an error.
if KERNEL.is_file():
    sys.path[:0] = [str(ROOT), str(ROOT / "python/tests")]
    import conftest
    from pytest_markdown_docs.plugin import extract_fence_tests
    from tools._ci_steps import DOC_EXAMPLE_DOCS
    from tools.check_fence_marks import harness_markdown_it

    conftest.pytest_sessionstart()

    class Keep(ast.NodeTransformer):
        def __init__(self, first):
            self.first, self.kept = first, []

        def visit_Module(self, node):
            read = {n.id for n in ast.walk(node) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
            body = []
            for st in node.body:
                if st.lineno > self.first and isinstance(st, ast.Expr) and isinstance(st.value, ast.Call):
                    name = f"_probe_{st.lineno}"
                    self.kept.append((st.lineno, name))
                    st = ast.copy_location(ast.Assign([ast.Name(name, ast.Store())], st.value), st)
                elif (st.lineno > self.first and isinstance(st, ast.Assign) and isinstance(st.value, ast.Call)
                      and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name)
                      and st.targets[0].id not in read):
                    self.kept.append((st.lineno, st.targets[0].id))
                body.append(st)
            node.body = body
            return node

    for doc in DOC_EXAMPLE_DOCS:
        markdown = (ROOT / doc).read_text(encoding="utf-8")
        for fence in extract_fence_tests(harness_markdown_it(), markdown, 0, ROOT / doc,
                                         markdown_type=doc.suffix.removeprefix(".")):
            keep = Keep(fence.start_line)
            tree = ast.fix_missing_locations(keep.visit(ast.parse(fence.source)))
            scope = dict(conftest._make_globals())
            cwd = WORK / f"py{doc.stem}{fence.start_line}"
            cwd.mkdir()
            try:
                with contextlib.chdir(cwd), contextlib.redirect_stdout(io.StringIO()):
                    exec(compile(tree, str(doc), "exec"), scope)
            except Exception as error:  # the harness fails this fence on its own
                print(f"{doc}:{fence.start_line} raised {type(error).__name__}; the harness reports it")
                continue
            finally:
                scope["client"].__exit__(None, None, None)
            for line, name in keep.kept:
                answer = scope.get(name)
                if isinstance(answer, dict) and answer.get("status") == "error":
                    failed.append(f"Python {doc}:{line}: {answer.get('message')}")
else:
    print("no built kernel: the Python half is untestable")

# Rust: a binding of a call made without `?` keeps a Result nobody reads.
rust_call = re.compile(r"\s*let\s+_\w*\s*=\s*[^;]*\w\([^;]*;")
for doc in listed("rust/tests/doc_examples.rs", r"DOC_FILES: \[&str; \d+\] = \[(.*?)\];"):
    for start, body in fences(doc, "rust"):
        failed += [f"Rust {doc}:{start + k + 1}: {line.strip()}" for k, line in enumerate(body)
                   if rust_call.match(line) and "?" not in line]

for line in failed:
    print(line)
raise SystemExit(1 if failed else 0)
PY
