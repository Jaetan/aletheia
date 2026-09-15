# Decision-point accumulator for the file review of `cpp/`

- status: pending (collated for the user when the task list is empty)
- round base: 726198bb (2026-09-15)

Each point: the question and its alternatives in prose, each alternative named by what it proposes. A point that only gates a fix is worked to the ruling it gates before it is written here.

(none yet)

## `cpp/.clang-format`: 40 of its 61 option keys restate the LLVM base style's default

Measured with `clang-format-22 --dump-config` against `--style=LLVM --dump-config` at the task: 17 keys change the base default (IndentWidth, TabWidth, AccessModifierOffset, ColumnLimit, PointerAlignment, ReferenceAlignment, AlignConsecutiveAssignments, AlignConsecutiveDeclarations, AllowShortBlocksOnASingleLine, AllowShortFunctionsOnASingleLine, BreakConstructorInitializers, PackConstructorInitializers, SpaceAfterTemplateKeyword, SpacesInContainerLiterals, SortUsingDeclarations, InsertNewlineAtEOF, RemoveSemicolon); the other 40 set the value LLVM already has. The question: keep the restated defaults as an explicit statement of the style, or cut them so the file lists only what the project decides. Cutting is behaviour-neutral, provable by the same dump-config equality used for the alias fix, and would shrink the file from 84 lines to about 45. Keeping means a reader sees every choice in one place without knowing the LLVM defaults, at the cost of 40 lines that a later LLVM default change could silently diverge from (a restated value pins it; a cut value follows LLVM). Ruling needed: pin every value explicitly, or list only the project's own decisions.
