# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads a Python DBC place from its reader's ``field_word`` call.

``normalize_signal`` reads a byte order with ``field_word`` and keeps the word
it returns; ``_check_presence`` compares the presence where it reads it, in an
``if`` of its body that ends in ``return``, the code after it the last arm;
``_normalize_comment_target`` and ``_normalize_attribute`` assign the kind to a
name they map in a chain of such ``if``s, the second reading another field
before the chain; ``_normalize_attr_target`` hands the kind its chain does not
map to ``_normalize_attr_target_at_id``, whose chain of tests of it maps on past
an assignment.  A word dropped from a call or added to it, a key or a word that
is not a literal, a call compared other than as an ``if``'s whole ``==`` to one
literal, a name mapped in no chain or used outside it, a hand-off missing or to
another function or argument, a helper not defined or taking no positional
parameter, an arm falling into the code after it and a last arm reading another
word or several are named at the place, as is a ``StrEnum`` member whose value
is not a string constant.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    PYTHON_DBC_NORMALIZE,
    PYTHON_ISSUE_CODES,
    AgdaText,
    PyText,
    ReplyPlace,
    ReplyTables,
    check_reply_places,
    python_reader,
    read_reply_tables,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_BYTE_ORDER = ReplyPlace("dbc/messages/signals/byteOrder")
_PRESENCE = ReplyPlace("dbc/messages/signals/presence")
_IN_SIGNAL = "python/aletheia/client/_helpers/dbc_normalize.py:normalize_signal: "
_IN_PRESENCE = "python/aletheia/client/_helpers/dbc_normalize.py:_check_presence: "
_ORDER_CALL = PyText('field_word(raw_sig, path, "byteOrder", "little_endian", "big_endian")')
_ORDER_WORDS = '"little_endian", "big_endian"'
_PRESENCE_CALL = 'field_word(raw, path, "presence", "always", "multiplexed")'
_PRESENCE_TEST = PyText(f'{_PRESENCE_CALL} == "always"')
_ALWAYS_ARM = PyText('        return\n    _ = _string(raw, path, "multiplexor")')
_TEST_OF = "the test of the word at 'presence'"
_NO_IF = "compares the word field_word reads at 'presence' in no if of its body"
_NOT_EQ = f"{_TEST_OF} is not == to one literal"
_NO_RETURN = f"{_TEST_OF} has an else or an arm not ending in return"
_NO_KEY = "names no string literal key or no word"
_COMMENT = ReplyPlace("dbc/comments/target/kind")
_IN_COMMENT = "python/aletheia/client/_helpers/dbc_normalize.py:_normalize_comment_target: "
_KIND_CALL = '"message", "signal", "envVar")'
_NETWORK_TEST = PyText(f'{_KIND_CALL}\n    if kind == "network":')
_NETWORK_ARM = PyText(f'{_NETWORK_TEST}\n        return {{"kind": "network"}}')
_MESSAGE_TEST = PyText('"node")}\n    if kind == "message":')
_COMMENT_READ = ' = field_word(raw, path, "kind", "network"'
_ATTRIBUTE = ReplyPlace("dbc/attributes/kind")
_IN_ATTRIBUTE = "python/aletheia/client/_helpers/dbc_normalize.py:_normalize_attribute: "
_ATTRIBUTE_NAME = PyText('    name = _string(raw, path, "name")\n    if kind == "definition":')
_VALUE = ReplyPlace("dbc/attributes/value/kind")
_IN_VALUE = "python/aletheia/client/_helpers/dbc_normalize.py:_normalize_attr_value: "
_VALUE_HEAD = "-> DBCAttrValue:\n    kind = "
_VALUE_WORDS = 'field_word(raw, path, "kind", "int", "float", "string", "enum"'
_VALUE_CALL = PyText(f'{_VALUE_HEAD}{_VALUE_WORDS}, "hex")')
_ENUM_ARM = '\n        return {"kind": "enum", "value"'
_ENUM_VALUE = PyText(f'    if kind == "enum":{_ENUM_ARM}')
_TARGET = ReplyPlace("dbc/attributes/target/kind")
_IN_TARGET = "python/aletheia/client/_helpers/dbc_normalize.py:_normalize_attr_target: "
_HELPER = "_normalize_attr_target_at_id"
_HAND_OFF = PyText(f"    return {_HELPER}(kind, raw, path)")
_NOT_HANDED = f"hands kind to {_HELPER} nowhere after its tests, as its first argument"
_HELPER_USE = f"{_HELPER} uses kind other than to map it"
_TARGET_WORDS = '"network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig"'
_TARGET_ARGUMENTS = f'(\n        raw, path, "kind", {_TARGET_WORDS}\n    )'
_TARGET_READ = PyText(f"    kind = field_word{_TARGET_ARGUMENTS}")
_TARGET_NETWORK = PyText(f'{_TARGET_READ}\n    if kind == "network":')
_HELPER_PARAMETERS = PyText(f"def {_HELPER}(kind: str, raw: ReplyFields, path: ReplyPath)")
_MESSAGE_ARM = '\n        return {"kind": "message", "id"'
_HELPER_MESSAGE = PyText(f'    if kind == "message":{_MESSAGE_ARM}')
_HELPER_NODE = '    node = _string(raw, path, "node")\n    if kind == '
_HELPER_NODE_MSG = PyText(f'{_HELPER_NODE}"nodeMsg":')
_ENV_VAR_ARM = PyText(
    f'        return {{"kind": "envVar", "envVar": _string(raw, path, "envVar")}}\n{_HAND_OFF}'
)


def _named_at(
    monkeypatch: pytest.MonkeyPatch,
    plant: tuple[PyText, PyText],
    place: ReplyPlace,
    module: Path = PYTHON_DBC_NORMALIZE,
) -> list[Prose]:
    """Return, sorted, what the gate names at ``place`` with ``plant`` planted in ``module``.

    ``plant`` is a text standing once in the module and what it is planted as.
    """
    written, planted = plant
    source = module.read_text(encoding="utf-8")
    assert source.count(written) == 1
    text = PyText(source.replace(written, planted))

    def source_of(read: Path) -> PyText:
        return text if read == module else PyText(read.read_text(encoding="utf-8"))

    monkeypatch.setattr("tools._reply_places._py_source", source_of)
    tables = read_reply_tables(
        AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8")), (python_reader(frozenset()),)
    )
    found = tables if isinstance(tables, list) else check_reply_places(tables, frozenset())
    lead = f"reply place {place}: "
    return sorted(Prose(each.removeprefix(lead)) for each in found if each.startswith(lead))


def test_reads_every_python_place_from_the_modules_on_disk() -> None:
    """Every Python reader set is read from its module as the tree holds it, none refused."""
    tables = read_reply_tables(
        AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8")), (python_reader(frozenset()),)
    )
    assert isinstance(tables, ReplyTables), tables


@pytest.mark.parametrize(
    ("plant", "place", "named"),
    [
        pytest.param(
            (_ORDER_CALL, PyText(_ORDER_CALL)),
            _BYTE_ORDER,
            [],
            id="byteOrder as written",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(_PRESENCE_TEST)),
            _PRESENCE,
            [],
            id="presence as written",
        ),
        pytest.param(
            (_ORDER_CALL, PyText('field_word(raw_sig, path, "byteOrder", "little_endian")')),
            _BYTE_ORDER,
            ["'big_endian' is in replyText only"],
            id="a word dropped",
        ),
        pytest.param(
            (
                _ORDER_CALL,
                PyText(f'field_word(raw_sig, path, "byteOrder", {_ORDER_WORDS}, "middle")'),
            ),
            _BYTE_ORDER,
            ["'middle' is in the Python reader only"],
            id="a word added",
        ),
        pytest.param(
            (
                _ORDER_CALL,
                PyText(
                    'field_word(raw_sig, path, "byteOrder", "little_endian")'
                    + ' or field_word(raw_sig, path, "byteOrder", "big_endian")'
                ),
            ),
            _BYTE_ORDER,
            [],
            id="the words of every call at the key",
        ),
        pytest.param(
            (
                _ORDER_CALL,
                PyText('field_word(raw_sig, path, "byteorder", "little_endian", "big_endian")'),
            ),
            _BYTE_ORDER,
            [_IN_SIGNAL + "no field_word call at 'byteOrder'"],
            id="no call at the key",
        ),
        pytest.param(
            (_ORDER_CALL, PyText('field_word(raw_sig, path, "byteOrder", "little_endian", BIG)')),
            _BYTE_ORDER,
            [
                _IN_SIGNAL
                + "field_word(raw_sig, path, 'byteOrder', 'little_endian', BIG)"
                + " awaits a word that is not a string literal"
            ],
            id="a word not a literal",
        ),
        pytest.param(
            (_ORDER_CALL, PyText('field_word(raw_sig, path, "byteOrder", "little_endian", 0)')),
            _BYTE_ORDER,
            [
                _IN_SIGNAL
                + "field_word(raw_sig, path, 'byteOrder', 'little_endian', 0)"
                + " awaits a word that is not a string literal"
            ],
            id="a word a number",
        ),
        pytest.param(
            (_ORDER_CALL, PyText('field_word(raw_sig, path, KEY, "little_endian", "big_endian")')),
            _BYTE_ORDER,
            [
                _IN_SIGNAL
                + "field_word(raw_sig, path, KEY, 'little_endian', 'big_endian') "
                + _NO_KEY
            ],
            id="a key not a literal",
        ),
        pytest.param(
            (_ORDER_CALL, PyText('field_word(raw_sig, path, "byteOrder")')),
            _BYTE_ORDER,
            [_IN_SIGNAL + "field_word(raw_sig, path, 'byteOrder') " + _NO_KEY],
            id="no word",
        ),
        pytest.param(
            (
                _ORDER_CALL,
                PyText(f'field_word(raw_sig, path, "byteOrder", {_ORDER_WORDS}, strict=1)'),
            ),
            _BYTE_ORDER,
            [
                _IN_SIGNAL
                + "field_word(raw_sig, path, 'byteOrder', 'little_endian', 'big_endian', strict=1) "
                + _NO_KEY
            ],
            id="a keyword",
        ),
        pytest.param(
            (PyText("def normalize_signal("), PyText("def normalise_signal(")),
            _BYTE_ORDER,
            ["python/aletheia/client/_helpers/dbc_normalize.py:normalize_signal is not defined"],
            id="no function",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'{_PRESENCE_CALL} == "sometimes"')),
            _PRESENCE,
            [
                _IN_PRESENCE
                + f"{_TEST_OF} names 'sometimes', which no field_word call at 'presence' awaits"
            ],
            id="a test of no awaited word",
        ),
        pytest.param(
            (
                _PRESENCE_TEST,
                PyText(
                    'field_word(raw, path, "presence", "always", "multiplexed", "x") == "always"'
                ),
            ),
            _PRESENCE,
            [_IN_PRESENCE + f"the code after {_TEST_OF} reads 'multiplexed', 'x' alike"],
            id="a last arm reading two words",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'{_PRESENCE_CALL} == "multiplexed"')),
            _PRESENCE,
            ["the Python reader's last arm names 'always', not 'multiplexed'"],
            id="a last arm reading the first word",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'{_PRESENCE_CALL} != "always"')),
            _PRESENCE,
            [_IN_PRESENCE + _NOT_EQ],
            id="a test other than ==",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f"{_PRESENCE_CALL} == ALWAYS")),
            _PRESENCE,
            [_IN_PRESENCE + _NOT_EQ],
            id="a test of no literal",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'{_PRESENCE_CALL} == "always" == raw')),
            _PRESENCE,
            [_IN_PRESENCE + _NOT_EQ],
            id="a test of two comparisons",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'"always" == {_PRESENCE_CALL}')),
            _PRESENCE,
            [_IN_PRESENCE + _NO_IF],
            id="the call compared on the right",
        ),
        pytest.param(
            (_PRESENCE_TEST, PyText(f'{_PRESENCE_CALL} == "always" and raw')),
            _PRESENCE,
            [_IN_PRESENCE + _NO_IF],
            id="the comparison part of a test",
        ),
        pytest.param(
            (_ALWAYS_ARM, PyText('        pass\n    _ = _string(raw, path, "multiplexor")')),
            _PRESENCE,
            [_IN_PRESENCE + _NO_RETURN],
            id="an arm falling into the last",
        ),
        pytest.param(
            (
                _ALWAYS_ARM,
                PyText(
                    "        return\n    else:\n        pass\n"
                    + '    _ = _string(raw, path, "multiplexor")'
                ),
            ),
            _PRESENCE,
            [_IN_PRESENCE + _NO_RETURN],
            id="an else",
        ),
        pytest.param(
            (
                _PRESENCE_TEST,
                PyText(f'{_PRESENCE_CALL} == field_word(raw, path, "presence", "always")'),
            ),
            _PRESENCE,
            [_IN_PRESENCE + "reads 'presence' with field_word 2 times, not once"],
            id="two calls at the key",
        ),
        pytest.param(
            (
                _PRESENCE_TEST,
                PyText('field_word(raw, path, "presense", "always", "multiplexed") == "always"'),
            ),
            _PRESENCE,
            [_IN_PRESENCE + "no field_word call at 'presence'"],
            id="no call at the mapped key",
        ),
        pytest.param(
            (_NETWORK_TEST, _NETWORK_TEST),
            _COMMENT,
            [],
            id="comment target kind as written",
        ),
        pytest.param(
            (PyText(_KIND_CALL), PyText('"message", "signal")')),
            _COMMENT,
            ["'envVar' is in replyText only"],
            id="a word dropped from a mapped call",
        ),
        pytest.param(
            (
                PyText('if kind == "signal":\n        return {'),
                PyText('if kind == "envVar":\n        return {'),
            ),
            _COMMENT,
            ["the Python reader's last arm names 'signal', not 'envVar'"],
            id="a chain's last arm reading another word",
        ),
        pytest.param(
            (_NETWORK_TEST, PyText(f'{_KIND_CALL}\n    if kind == "node":')),
            _COMMENT,
            [_IN_COMMENT + "the code after the tests of kind reads 'envVar', 'network' alike"],
            id="a chain's last arm reading two words",
        ),
        pytest.param(
            (_NETWORK_TEST, PyText(f'{_KIND_CALL}\n    if kind == "net":')),
            _COMMENT,
            [
                _IN_COMMENT
                + "the tests of kind names 'net', which no field_word call at 'kind' awaits"
            ],
            id="a chain's test of no awaited word",
        ),
        pytest.param(
            (_NETWORK_TEST, PyText(f'{_KIND_CALL}\n    if kind != "network":')),
            _COMMENT,
            [_IN_COMMENT + "a test of kind is not == to one literal"],
            id="a chain's test other than ==",
        ),
        pytest.param(
            (_NETWORK_ARM, PyText(f'{_NETWORK_TEST}\n        _ = {{"kind": "network"}}')),
            _COMMENT,
            [_IN_COMMENT + "a test of kind has an else or an arm not ending in return"],
            id="a chain's arm falling into the next",
        ),
        pytest.param(
            (_NETWORK_ARM, PyText(f'{_NETWORK_TEST}\n        return {{"kind": kind}}')),
            _COMMENT,
            [_IN_COMMENT + "uses kind other than to map it"],
            id="the name used in an arm",
        ),
        pytest.param(
            (
                _MESSAGE_TEST,
                PyText('"node")}\n    if not raw:\n        return {}\n    if kind == "message":'),
            ),
            _COMMENT,
            [_IN_COMMENT + "uses kind other than to map it"],
            id="a test after the chain ends",
        ),
        pytest.param(
            (_MESSAGE_TEST, PyText('"node")}\n    _ = raw\n    if kind == "message":')),
            _COMMENT,
            [],
            id="an assignment between two tests",
        ),
        pytest.param(
            (PyText(f"kind{_COMMENT_READ}"), PyText(f"word{_COMMENT_READ}")),
            _COMMENT,
            [_IN_COMMENT + "maps word in no chain of tests of it"],
            id="the name tested in no chain",
        ),
        pytest.param(
            (PyText(f"kind{_COMMENT_READ}"), PyText(f"kind: str{_COMMENT_READ}")),
            _COMMENT,
            [_IN_COMMENT + "compares the word field_word reads at 'kind' in no if of its body"],
            id="the call assigned with an annotation",
        ),
        pytest.param(
            (_ATTRIBUTE_NAME, _ATTRIBUTE_NAME),
            _ATTRIBUTE,
            [],
            id="a statement between the call and its chain",
        ),
        pytest.param(
            (
                _ATTRIBUTE_NAME,
                PyText('    name = _string(raw, path, kind)\n    if kind == "definition":'),
            ),
            _ATTRIBUTE,
            [_IN_ATTRIBUTE + "uses kind other than to map it"],
            id="the name used before its chain",
        ),
        pytest.param(
            (_VALUE_CALL, PyText(_VALUE_HEAD + '_string(raw, path, "kind")')),
            _VALUE,
            [_IN_VALUE + "no field_word call at 'kind'"],
            id="an attribute value's kind read as any string",
        ),
        pytest.param(
            (_VALUE_CALL, PyText(f"{_VALUE_HEAD}{_VALUE_WORDS})")),
            _VALUE,
            ["'hex' is in replyText only"],
            id="a word dropped from an attribute value's call",
        ),
        pytest.param(
            (_ENUM_VALUE, PyText(f'    if kind == "hex":{_ENUM_ARM}')),
            _VALUE,
            ["the Python reader's last arm names 'enum', not 'hex'"],
            id="an attribute value's last arm reading another word",
        ),
        pytest.param(
            (_HAND_OFF, _HAND_OFF),
            _TARGET,
            [],
            id="attribute target kind as written",
        ),
        pytest.param(
            (_TARGET_READ, PyText('    kind = _string(raw, path, "kind")')),
            _TARGET,
            [_IN_TARGET + "no field_word call at 'kind'"],
            id="the old reader planted back: the target kind read as any string",
        ),
        pytest.param(
            (_HAND_OFF, PyText(f'    return {_HELPER}("nodeSig", raw, path)')),
            _TARGET,
            [_IN_TARGET + _NOT_HANDED],
            id="a literal handed in place of the word",
        ),
        pytest.param(
            (_HAND_OFF, PyText(f"    return {_HELPER}(raw, kind, path)")),
            _TARGET,
            [_IN_TARGET + _NOT_HANDED],
            id="the word handed as a second argument",
        ),
        pytest.param(
            (_HAND_OFF, PyText("    return _normalize_attr_target_by_id(kind, raw, path)")),
            _TARGET,
            [_IN_TARGET + _NOT_HANDED],
            id="the word handed to another function",
        ),
        pytest.param(
            (
                _ENV_VAR_ARM,
                PyText(
                    f'        return {_HELPER}(kind, raw, path)\n    return {{"kind": "envVar"}}'
                ),
            ),
            _TARGET,
            [_IN_TARGET + _NOT_HANDED],
            id="the word handed in an arm, not after the tests",
        ),
        pytest.param(
            (
                PyText(f'{_TARGET_NETWORK}\n        return {{"kind": "network"}}'),
                PyText(f'{_TARGET_NETWORK}\n        return {{"kind": kind}}'),
            ),
            _TARGET,
            [_IN_TARGET + "uses kind other than to map it"],
            id="the handed word used in an arm too",
        ),
        pytest.param(
            (
                _TARGET_NETWORK,
                PyText(f'    if field_word{_TARGET_ARGUMENTS} == "network":'),
            ),
            _TARGET,
            [
                _IN_TARGET
                + f"hands the word at 'kind' to {_HELPER} nowhere, testing it where it reads it"
            ],
            id="the word tested where it is read, so handed nowhere",
        ),
        pytest.param(
            (PyText(f"def {_HELPER}("), PyText("def _normalize_attr_target_by_id(")),
            _TARGET,
            [_IN_TARGET + f"{_HELPER} is not defined"],
            id="no helper",
        ),
        pytest.param(
            (
                _HELPER_PARAMETERS,
                PyText(f"def {_HELPER}(*, kind: str, raw: ReplyFields, path: ReplyPath)"),
            ),
            _TARGET,
            [_IN_TARGET + f"{_HELPER} takes no positional parameter"],
            id="a helper taking no positional parameter",
        ),
        pytest.param(
            (
                _HELPER_PARAMETERS,
                PyText(f"def {_HELPER}(kind: str, /, raw: ReplyFields, path: ReplyPath)"),
            ),
            _TARGET,
            [],
            id="the word a helper's positional-only parameter",
        ),
        pytest.param(
            (
                _HELPER_PARAMETERS,
                PyText(f"def {_HELPER}(raw: ReplyFields, kind: str, path: ReplyPath)"),
            ),
            _TARGET,
            [_IN_TARGET + f"{_HELPER} uses raw other than to map it"],
            id="the word the helper's second parameter",
        ),
        pytest.param(
            (
                _HELPER_MESSAGE,
                PyText('    if kind == "message":\n        return {"kind": kind, "id"'),
            ),
            _TARGET,
            [_IN_TARGET + _HELPER_USE],
            id="the word used in a helper's arm",
        ),
        pytest.param(
            (
                _HELPER_NODE_MSG,
                PyText(f"    if not raw:\n        return {{}}\n{_HELPER_NODE_MSG}"),
            ),
            _TARGET,
            [_IN_TARGET + _HELPER_USE],
            id="a helper's test after its chain ends",
        ),
        pytest.param(
            (
                PyText('    if kind == "signal":\n        signal ='),
                PyText('    if kind != "signal":\n        signal ='),
            ),
            _TARGET,
            [_IN_TARGET + f"a test of kind in {_HELPER} is not == to one literal"],
            id="a helper's test other than ==",
        ),
        pytest.param(
            (
                _HELPER_MESSAGE,
                PyText(f'    if kind == "msg":{_MESSAGE_ARM}'),
            ),
            _TARGET,
            [
                _IN_TARGET
                + f"the tests of kind and the tests of kind in {_HELPER} names 'msg',"
                + " which no field_word call at 'kind' awaits"
            ],
            id="a helper's test of no awaited word",
        ),
        pytest.param(
            (_HELPER_NODE_MSG, PyText(f'{_HELPER_NODE}"message":')),
            _TARGET,
            [
                _IN_TARGET
                + f"the code after the tests of kind in {_HELPER} reads 'nodeMsg', 'nodeSig' alike"
            ],
            id="a helper's last arm reading two words",
        ),
        pytest.param(
            (_HELPER_NODE_MSG, PyText(f'{_HELPER_NODE}"nodeSig":')),
            _TARGET,
            ["the Python reader's last arm names 'nodeMsg', not 'nodeSig'"],
            id="a helper's last arm reading another word",
        ),
    ],
)
def test_names_a_python_word_call_at_its_place(
    monkeypatch: pytest.MonkeyPatch,
    plant: tuple[PyText, PyText],
    place: ReplyPlace,
    named: list[Prose],
) -> None:
    """The gate names at ``place`` what ``plant`` breaks of the reader's call, and nothing else."""
    assert _named_at(monkeypatch, plant, place) == named


@pytest.mark.parametrize("place", [ReplyPlace("issues/severity"), ReplyPlace("warnings/severity")])
@pytest.mark.parametrize(
    ("member", "named"),
    [
        pytest.param('    ERROR: Final = "error"', [], id="annotated"),
        pytest.param(
            "    ERROR = 0",
            [Prose("python/aletheia/codes/_issue.py:IssueSeverity.ERROR is not a string constant")],
            id="a number",
        ),
    ],
)
def test_reads_an_enum_member_by_its_string_constant(
    monkeypatch: pytest.MonkeyPatch, place: ReplyPlace, member: PyText, named: list[Prose]
) -> None:
    """A ``StrEnum`` member is read by its string constant, annotated or not, or named."""
    plant = (PyText('    ERROR = "error"'), member)
    assert _named_at(monkeypatch, plant, place, PYTHON_ISSUE_CODES) == named
