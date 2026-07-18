"""Classify strong-gcd components in `census cb` residual output.

The exhaustive enumeration remains in the Rust `census` crate. This script only
parses its emitted residual duals and computes the deterministic graph statistics
used in quintuple_density_notes.md.
"""

from __future__ import annotations

import math
import re
import sys
from collections import Counter
from pathlib import Path


def read_input() -> str:
    if len(sys.argv) != 2:
        raise SystemExit("usage: python audit_cb_components.py <census-output-file|->")
    if sys.argv[1] == "-":
        return sys.stdin.read()
    return Path(sys.argv[1]).read_text(encoding="utf-8")


def component_count(values: tuple[int, ...]) -> tuple[int, int, int]:
    parent = list(range(len(values)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def union(i: int, j: int) -> None:
        left, right = find(i), find(j)
        if left != right:
            parent[right] = left

    max_r = 0
    max_s = 0
    for i in range(len(values)):
        for j in range(i + 1, len(values)):
            x, y = sorted((values[i], values[j]))
            g = math.gcd(x, y)
            if 4 * g >= x:
                r, s = x // g, y // g
                assert 2 <= r <= 4
                assert 2 <= s <= 632
                assert math.gcd(r, s) == 1
                max_r = max(max_r, r)
                max_s = max(max_s, s)
                union(i, j)
    return len({find(i) for i in range(len(values))}), max_r, max_s


def self_bad_count(values: tuple[int, ...]) -> int:
    return sum(
        value
        <= sum(math.gcd(value, other) for j, other in enumerate(values) if i != j)
        for i, value in enumerate(values)
    )


def main() -> None:
    text = read_input()
    residuals = {
        tuple(map(int, match.group(1).split(",")))
        for match in re.finditer(r"D=\[([0-9, ]+)\]", text)
    }
    if not residuals:
        raise SystemExit("no residual D=[...] rows found")

    components: Counter[int] = Counter()
    bad_counts: Counter[int] = Counter()
    max_r = 0
    max_s = 0
    for values in residuals:
        count, row_r, row_s = component_count(values)
        components[count] += 1
        bad_counts[self_bad_count(values)] += 1
        max_r = max(max_r, row_r)
        max_s = max(max_s, row_s)

    print(f"unique residuals: {len(residuals)}")
    print(f"component counts: {dict(sorted(components.items()))}")
    print(f"self-bad counts: {dict(sorted(bad_counts.items()))}")
    print(f"largest strong-edge label: r={max_r}, s={max_s}")


if __name__ == "__main__":
    main()
