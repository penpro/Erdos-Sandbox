#!/usr/bin/env python3
"""Exact audit for the finite kernels in the size-6 density note.

This is a lightweight independent checker for the constants used in
`sextuple_density_notes.md`:

  W0 = min E[1/(1+X)] over five moduli >= 2
  W1 = the same minimum with no modulus equal to 2
  W2 = the same minimum with at most one modulus equal to 2

It also brute-checks the elementary 2-friend lemma and the peel inequality over
small finite ranges. This is not a proof of the retirement-to-finite-box step;
it is an exact backstop for the boxed minima and algebra.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import gcd, lcm


EXPECTED_W0 = Fraction(49, 100)
EXPECTED_W1 = Fraction(7423, 12600)
EXPECTED_W2 = Fraction(1087, 2100)


def expectation(moduli: tuple[int, ...]) -> Fraction:
    """Return E[1/(1+X)] for divisibility events with the given moduli."""
    total = Fraction(1, 1)
    n = len(moduli)
    for k in range(1, n + 1):
        sign = -1 if k % 2 else 1
        for idxs in combinations(range(n), k):
            period = 1
            for idx in idxs:
                period = lcm(period, moduli[idx])
            total += sign * Fraction(1, (k + 1) * period)
    return total


def update_best(best: tuple[Fraction | None, tuple[int, ...] | None], value: Fraction, tup: tuple[int, ...]):
    current, witness = best
    if current is None or value < current:
        return value, tup
    if value == current and witness is not None and tup < witness:
        return value, tup
    return best


def audit_minima(bound: int) -> None:
    best_all: tuple[Fraction | None, tuple[int, ...] | None] = (None, None)
    best_no_two: tuple[Fraction | None, tuple[int, ...] | None] = (None, None)
    best_at_most_one_two: tuple[Fraction | None, tuple[int, ...] | None] = (None, None)
    checked = 0

    for tup in combinations_with_replacement(range(2, bound + 1), 5):
        checked += 1
        value = expectation(tup)
        best_all = update_best(best_all, value, tup)
        twos = tup.count(2)
        if twos == 0:
            best_no_two = update_best(best_no_two, value, tup)
        if twos <= 1:
            best_at_most_one_two = update_best(best_at_most_one_two, value, tup)

    print(f"five-moduli minima audit up to {bound}: checked={checked}")
    for label, best, expected, witness in [
        ("W0 all", best_all, EXPECTED_W0, (2, 2, 2, 3, 5)),
        ("W1 no 2", best_no_two, EXPECTED_W1, (3, 3, 4, 5, 7)),
        ("W2 <= one 2", best_at_most_one_two, EXPECTED_W2, (2, 3, 3, 5, 7)),
    ]:
        value, tup = best
        print(f"  {label:<12} best={value} at {tup}")
        assert value == expected, f"{label}: expected {expected}, got {value}"
        assert tup == witness, f"{label}: expected witness {witness}, got {tup}"


def audit_two_friend(limit: int) -> None:
    checked = 0
    for a in range(2, limit + 1):
        for f in range(2, limit + 1):
            if f % a == 0:
                continue
            g = gcd(a, f)
            if f // g == 2:
                checked += 1
                assert 3 * f <= 2 * a, (a, f, g)
    print(f"2-friend lemma audit up to {limit}: checked={checked}, PASS")


def audit_peel(bound: int) -> None:
    checked = 0
    for arity in range(0, 5):
        for tup in combinations_with_replacement(range(2, bound + 1), arity):
            base = expectation(tup)
            for m in range(2, bound + 1):
                extended = tuple(sorted(tup + (m,)))
                lower = base - Fraction(1, 2 * m)
                checked += 1
                assert expectation(extended) >= lower, (tup, m)
    print(f"peel inequality audit up to {bound}: checked={checked}, PASS")


def audit_algebra() -> None:
    eps1 = EXPECTED_W1 - Fraction(1, 2)
    eps2 = EXPECTED_W2 - Fraction(1, 2)
    assembly = eps1 + eps2 - Fraction(2, 75)
    print("assembly constants")
    print(f"  eps1 = {eps1}")
    print(f"  eps2 = {eps2}")
    print(f"  eps1 + eps2 - 2/75 = {assembly}")
    assert eps1 == Fraction(1123, 12600)
    assert eps2 == Fraction(37, 2100)
    assert assembly == Fraction(1009, 12600)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=25)
    parser.add_argument("--friend-limit", type=int, default=3000)
    parser.add_argument("--peel-bound", type=int, default=16)
    args = parser.parse_args()

    audit_minima(args.bound)
    audit_two_friend(args.friend_limit)
    audit_peel(args.peel_bound)
    audit_algebra()
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
