"""G9 — the cut chain has no unproved premise (spec §8.1, §7.2).

Every fact a VC carries must be the conclusion of an earlier VC (or the precondition),
and every VC must itself have passed G5 and G6. Checked from the manifest, which
records where each carried fact came from.
"""
from __future__ import annotations

from ..ir.trace import ENTRY


def check(manifest: dict, g5_passed: set[int] | None = None,
          g6_passed: set[int] | None = None) -> list[str]:
    bad: list[str] = []
    cuts = manifest["cuts"]
    proved: set[str] = {ENTRY}                   # the precondition is assumed, not proved
    for cut in cuts:
        for fact in cut.get("carried", []):
            if fact["from"] not in proved:
                bad.append(f"cut{cut['index']} carries a fact from {fact['from']}, "
                           f"which no earlier VC concludes: {fact['fact']}")
        proved.add(cut["to"])                    # this VC's goal, once it passes
    for cut in cuts:
        i = cut["index"]
        if g5_passed is not None and i not in g5_passed:
            bad.append(f"cut{i} did not pass G5, so its conclusion cannot be used")
        if g6_passed is not None and i not in g6_passed:
            bad.append(f"cut{i} did not pass G6, so its conclusion cannot be used")
    return bad
