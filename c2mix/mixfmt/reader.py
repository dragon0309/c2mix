"""Reader for five-section mix files (CryptoLine `cv -save-mix` format, spec §7.3).

S-expressions are plain Python values: an atom is a `str` (string literals keep
their quotes, quoted symbols keep their bars), a list is a `list`. Parsing and
all traversals are iterative, because algebraic terms nest hundreds of levels.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

SECTION_COMMENTS = (
    "; variable declaration",
    "; range precondition and program ",   # trailing space is part of the format (M10)
    "; algebraic precondition and program",
    "; postcondition",
    "; check",
)
SECTION_NAMES = ("decl", "range", "alg", "post", "check")

_TOKEN = re.compile(
    r'(?P<ws>[ \t\r\n]+)'
    r'|(?P<comment>;[^\n]*)'
    r'|(?P<lp>\()'
    r'|(?P<rp>\))'
    r'|(?P<str>"(?:[^"]|"")*")'
    r'|(?P<qsym>\|[^|]*\|)'
    r'|(?P<atom>[^ \t\r\n()";|]+)'
)


class ParseError(Exception):
    def __init__(self, message: str, line: int):
        super().__init__(f"line {line}: {message}")
        self.line = line


@dataclass
class Command:
    sexpr: list | str
    line: int

    @property
    def head(self) -> str | None:
        s = self.sexpr
        return s[0] if isinstance(s, list) and s and isinstance(s[0], str) else None


@dataclass
class Comment:
    text: str       # verbatim, starting with ';', without the newline
    line: int


@dataclass
class MixFile:
    items: list[Command | Comment]
    path: str | None = None
    inner_comments: list[Comment] = field(default_factory=list)  # comments inside a command

    def commands(self) -> list[Command]:
        return [it for it in self.items if isinstance(it, Command)]

    def sections(self) -> dict[str, list[Command | Comment]] | None:
        """Split items at the five section comments. None if the comments are not
        exactly the five expected lines in order (see lint rule SECTIONS)."""
        marks = [i for i, it in enumerate(self.items)
                 if isinstance(it, Comment) and it.text in SECTION_COMMENTS]
        if [self.items[i].text for i in marks] != list(SECTION_COMMENTS):
            return None
        out = {"header": self.items[:marks[0]]}
        bounds = marks + [len(self.items)]
        for k, name in enumerate(SECTION_NAMES):
            out[name] = self.items[bounds[k] + 1:bounds[k + 1]]
        return out


def tokenize(text: str):
    """Yield (kind, value, line). Whitespace is dropped."""
    line = 1
    pos = 0
    n = len(text)
    match = _TOKEN.match
    while pos < n:
        m = match(text, pos)
        if m is None:
            raise ParseError(f"unexpected character {text[pos]!r}", line)
        kind = m.lastgroup
        value = m.group()
        if kind != "ws":
            yield kind, value, line
        if kind in ("ws", "str", "qsym"):
            line += value.count("\n")
        pos = m.end()


def parse(text: str, path: str | None = None) -> MixFile:
    items: list[Command | Comment] = []
    inner: list[Comment] = []
    stack: list[list] = []
    start_line = 0
    for kind, value, line in tokenize(text):
        if kind == "comment":
            (inner if stack else items).append(Comment(value, line))
        elif kind == "lp":
            if not stack:
                start_line = line
            stack.append([])
        elif kind == "rp":
            if not stack:
                raise ParseError("unbalanced ')'", line)
            done = stack.pop()
            if stack:
                stack[-1].append(done)
            else:
                items.append(Command(done, start_line))
        else:
            if stack:
                stack[-1].append(value)
            else:
                items.append(Command(value, line))
    if stack:
        raise ParseError("unbalanced '(' (command not closed)", start_line)
    return MixFile(items, path, inner)


def read(path: str | Path) -> MixFile:
    path = Path(path)
    return parse(path.read_text(encoding="utf-8"), str(path))


def iter_nodes(sexpr):
    """Pre-order traversal without recursion."""
    stack = [sexpr]
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, list):
            stack.extend(reversed(node))


def atoms(sexpr):
    for node in iter_nodes(sexpr):
        if isinstance(node, str):
            yield node


def rewrite(sexpr, fn):
    """Bottom-up rewrite without recursion: fn(node) returns a replacement or None.
    Children are rewritten before their parent is offered to fn."""
    if isinstance(sexpr, str):
        r = fn(sexpr)
        return sexpr if r is None else r
    root = [sexpr]
    stack = [(root, 0, sexpr, 0, [])]   # (parent, slot, node, next child, rebuilt children)
    while stack:
        parent, slot, node, i, kids = stack[-1]
        if i < len(node):
            stack[-1] = (parent, slot, node, i + 1, kids)
            child = node[i]
            if isinstance(child, list):
                stack.append((kids, len(kids), child, 0, []))
                kids.append(None)
            else:
                r = fn(child)
                kids.append(child if r is None else r)
        else:
            stack.pop()
            r = fn(kids)
            parent[slot] = kids if r is None else r
    return root[0]
