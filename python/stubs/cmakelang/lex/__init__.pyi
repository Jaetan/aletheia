# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Subset of ``cmakelang.lex``: a listfile's tokens, as CMake's language manual defines them."""

from typing import ClassVar

class TokenType:
    """A token's kind; each kind is one instance, compared by identity."""

    QUOTED_LITERAL: ClassVar[TokenType]
    # What fits no other kind, an opened and never closed literal among it.
    UNQUOTED_LITERAL: ClassVar[TokenType]
    LEFT_PAREN: ClassVar[TokenType]
    RIGHT_PAREN: ClassVar[TokenType]
    # A bare identifier, as a command's name is spelled.
    WORD: ClassVar[TokenType]
    WHITESPACE: ClassVar[TokenType]
    NEWLINE: ClassVar[TokenType]
    COMMENT: ClassVar[TokenType]
    # The comment lines that switch cmake-format off and on, comments to CMake.
    FORMAT_OFF: ClassVar[TokenType]
    FORMAT_ON: ClassVar[TokenType]
    BRACKET_ARGUMENT: ClassVar[TokenType]
    BRACKET_COMMENT: ClassVar[TokenType]
    BYTEORDER_MARK: ClassVar[TokenType]

class Token:
    """One lexical unit of a listfile."""

    type: TokenType
    # The token's text as the file spells it, a quoted argument's quotes included.
    spelling: str

def tokenize(contents: str) -> list[Token]: ...

# A bracket argument's opening, content and closing.
def parse_bracket_argument(text: str) -> tuple[str, str, str]: ...
