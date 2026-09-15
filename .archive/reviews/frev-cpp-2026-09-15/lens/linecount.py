"""Comment/code/blank line counts per tracked file under a directory.

C-family files: // and /* */ comments. Hash-comment files (cmake, yaml, txt,
sh, py, clang config): # comments. Markdown and other files: every non-blank
line is code. A line holding both code and a comment counts as code.
Usage: python linecount.py <dir> [file...]
"""
import subprocess
import sys
from pathlib import Path

C_EXT = {".cpp", ".hpp", ".h", ".cc", ".in"}
HASH_EXT = {".txt", ".yaml", ".yml", ".py", ".sh", ".cmake"}
HASH_NAMES = {".clang-format", ".clang-tidy", "CMakeLists.txt"}


def count(path: Path) -> tuple[int, int, int]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return (0, 0, 0)
    lines = text.splitlines()
    code = comment = blank = 0
    in_block = False
    c_style = path.suffix in C_EXT
    hash_style = path.suffix in HASH_EXT or path.name in HASH_NAMES
    for raw in lines:
        s = raw.strip()
        if not s:
            blank += 1
            continue
        if c_style:
            if in_block:
                comment += 1
                if "*/" in s:
                    in_block = False
                continue
            if s.startswith("//"):
                comment += 1
            elif s.startswith("/*"):
                comment += 1
                if "*/" not in s[2:]:
                    in_block = True
            else:
                code += 1
                if "/*" in s and "*/" not in s.split("/*", 1)[1]:
                    in_block = True
        elif hash_style:
            if s.startswith("#") and not s.startswith("#!"):
                comment += 1
            else:
                code += 1
        else:
            code += 1
    return (code, comment, blank)


def main() -> None:
    root = Path(sys.argv[1])
    files = sys.argv[2:] or subprocess.run(
        ["git", "ls-files", str(root)], capture_output=True, text=True, check=True
    ).stdout.split()
    tc = tm = tb = 0
    print("code\tcomment\tblank\tratio\tfile")
    for f in files:
        c, m, b = count(Path(f))
        tc += c
        tm += m
        tb += b
        ratio = f"{m / c:.2f}" if c else "-"
        print(f"{c}\t{m}\t{b}\t{ratio}\t{f}")
    print(f"{tc}\t{tm}\t{tb}\t{tm / tc:.2f}\tTOTAL")


main()
