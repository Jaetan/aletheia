# Decision-point accumulator for the file review of `cpp/`

- status: pending (collated for the user when the task list is empty)
- round base: 726198bb (2026-09-15)

Each point: the question and its alternatives in prose, each alternative named by what it proposes. A point that only gates a fix is worked to the ruling it gates before it is written here.

(none yet)

## `cpp/.clang-format`: 40 of its 61 option keys restate the LLVM base style's default

Measured with `clang-format-22 --dump-config` against `--style=LLVM --dump-config` at the task: 17 keys change the base default (IndentWidth, TabWidth, AccessModifierOffset, ColumnLimit, PointerAlignment, ReferenceAlignment, AlignConsecutiveAssignments, AlignConsecutiveDeclarations, AllowShortBlocksOnASingleLine, AllowShortFunctionsOnASingleLine, BreakConstructorInitializers, PackConstructorInitializers, SpaceAfterTemplateKeyword, SpacesInContainerLiterals, SortUsingDeclarations, InsertNewlineAtEOF, RemoveSemicolon); the other 40 set the value LLVM already has. The question: keep the restated defaults as an explicit statement of the style, or cut them so the file lists only what the project decides. Cutting is behaviour-neutral, provable by the same dump-config equality used for the alias fix, and would shrink the file from 84 lines to about 45. Keeping means a reader sees every choice in one place without knowing the LLVM defaults, at the cost of 40 lines that a later LLVM default change could silently diverge from (a restated value pins it; a cut value follows LLVM). Ruling needed: pin every value explicitly, or list only the project's own decisions.

## `cpp/.clang-tidy`: five disables are inert for the surface the gate lints

Measured at the task by re-enabling them over `cpp/src` only (base/tidy_reenable_test_justified.txt): cert-err58-cpp, google-build-using-namespace, cppcoreguidelines-avoid-do-while, hicpp-no-array-decay and cppcoreguidelines-pro-bounds-array-to-pointer-decay produce zero findings in library code; their stated reasons all name test code (Catch2 macros, fixtures, `using namespace` in tests), and neither the CI gate (`run-clang-tidy-22 -p build cpp/src/`) nor the CMake integration (library target only) lints tests. The informational tidy lens over cpp/tests and cpp/benchmarks at base reports 1435 unique diagnostics, so tests are not close to lint-clean under the current check set either way. The question: keep the five disables so the file already describes a configuration under which tests could one day be linted, or drop them as dead configuration and re-add them the day tests enter the gate. A third shape is to give tests their own `.clang-tidy` under cpp/tests with the test-specific disables and start linting them, which is a directory-level change beyond one file's task. Ruling needed: keep, drop, or open the test-lint question as its own task.
