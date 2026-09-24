"""Writer for mix files: one top-level command per line, single spaces, comments
verbatim on their own line, trailing newline (the layout of the golden files)."""
from __future__ import annotations

from pathlib import Path

from .reader import Comment, MixFile, tokenize


def to_str(sexpr) -> str:
    if isinstance(sexpr, str):
        return sexpr
    out: list[str] = []
    # Each stack entry is an iterator position into a list being printed.
    stack = [(sexpr, 0)]
    out.append("(")
    while stack:
        node, i = stack.pop()
        if i < len(node):
            stack.append((node, i + 1))
            if i > 0:
                out.append(" ")
            child = node[i]
            if isinstance(child, list):
                out.append("(")
                stack.append((child, 0))
            else:
                out.append(child)
        else:
            out.append(")")
    return "".join(out)


def write(mix: MixFile) -> str:
    lines = []
    for it in mix.items:
        lines.append(it.text if isinstance(it, Comment) else to_str(it.sexpr))
    return "\n".join(lines) + "\n"


def write_file(mix: MixFile, path: str | Path) -> None:
    Path(path).write_text(write(mix), encoding="utf-8")


def normalize(text: str) -> list[tuple[str, str]]:
    """Normal form used by round-trip checks: the token stream with whitespace
    removed. Comments are kept verbatim, so section comments (M10) must survive."""
    return [(kind, value) for kind, value, _ in tokenize(text)]
