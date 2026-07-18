"""Exact audit checks for the primitive-quadruple charge note.

This is not the proof. It is a small adversarial backstop for the proof in
quadruple_charge_notes.md:

1. Recomputes the pointwise weight table in the two-good-charge proposition.
2. Enumerates the five possible (c/b, d/b) shapes under "b bad".
3. Checks the five c-charge estimates in the text.
4. Exhaustively checks primitive quadruples up to a user-supplied bound.

All comparisons use exact integer / Fraction arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb, gcd
import sys


ONE = Fraction(1, 1)

SHAPES = {
    (Fraction(3, 2), Fraction(5, 3)),
    (Fraction(3, 2), Fraction(5, 2)),
    (Fraction(4, 3), Fraction(3, 2)),
    (Fraction(5, 4), Fraction(3, 2)),
    (Fraction(6, 5), Fraction(3, 2)),
}

A_TERM_BOUNDS = {
    (Fraction(3, 2), Fraction(5, 3)): Fraction(1, 4),
    (Fraction(3, 2), Fraction(5, 2)): Fraction(1, 4),
    (Fraction(4, 3), Fraction(3, 2)): Fraction(1, 3),
    (Fraction(5, 4), Fraction(3, 2)): Fraction(1, 8),
    (Fraction(6, 5), Fraction(3, 2)): Fraction(1, 5),
}


def is_primitive(p: tuple[int, ...]) -> bool:
    return all(y % x != 0 for i, x in enumerate(p) for j, y in enumerate(p) if i != j)


def charge_sum(p: tuple[int, ...], e: int) -> Fraction:
    return sum(Fraction(gcd(e, f), f) for f in p if f != e)


def good_count(p: tuple[int, ...]) -> int:
    return sum(charge_sum(p, e) < ONE for e in p)


def weight_y(p_count: int, q_count: int) -> int:
    """Pointwise contribution to Y for p grouped and q good divisors."""
    return (
        p_count
        - (p_count * q_count + 2 * comb(p_count, 2))
        + 2 * comb(p_count + q_count, 3)
        - 2 * comb(p_count + q_count, 4)
    )


def audit_weight_table() -> None:
    expected = {
        (1, 0): 1,
        (1, 1): 0,
        (1, 2): 1,
        (2, 0): 0,
        (2, 1): 0,
        (2, 2): 2,
    }
    got = {(p, q): weight_y(p, q) for p in (1, 2) for q in (0, 1, 2)}
    if got != expected:
        raise AssertionError(f"weight table mismatch: got {got}, expected {expected}")
    if any(v < 0 for v in got.values()):
        raise AssertionError(f"negative pointwise Y weight: {got}")
    print("pointwise Y weight table: PASS")


def enumerate_bad_b_shapes(limit: int = 50) -> set[tuple[Fraction, Fraction]]:
    shapes: set[tuple[Fraction, Fraction]] = set()
    for u in range(3, limit + 1):
        for v in range(3, limit + 1):
            if Fraction(1, u) + Fraction(1, v) < Fraction(1, 2):
                continue
            for r in range(2, u):
                if gcd(u, r) != 1:
                    continue
                for s in range(2, v):
                    if gcd(v, s) != 1:
                        continue
                    cb = Fraction(u, r)
                    db = Fraction(v, s)
                    if ONE < cb < db:
                        shapes.add((cb, db))
    return shapes


def audit_shape_enumeration() -> None:
    shapes = enumerate_bad_b_shapes()
    if shapes != SHAPES:
        raise AssertionError(f"shape list mismatch: got {sorted(shapes)}, expected {sorted(SHAPES)}")
    print("five-shape enumeration under b bad: PASS")


def audit_c_charge_estimates(w_limit: int = 2001) -> None:
    """Check the five displayed charge(c) estimates.

    Under q=2 we have b/a = w/2 with w odd. For each allowed shape, c/a is
    (w/2)(c/b). The term gcd(c,a)/a is 1 / denominator(c/a), unless the
    denominator is 1; denominator 1 is exactly the forbidden a|c case.
    """
    for shape, a_bound in A_TERM_BOUNDS.items():
        cb, db = shape
        worst_a_term = Fraction(0, 1)
        for w in range(3, w_limit + 1, 2):
            ca = Fraction(w, 2) * cb
            if ca.denominator == 1:
                continue
            term = Fraction(1, ca.denominator)
            worst_a_term = max(worst_a_term, term)
            if term > a_bound:
                raise AssertionError((shape, w, term, a_bound))

        b_term = Fraction(1, cb.denominator)
        dc = db / cb
        d_term = Fraction(1, dc.numerator)
        total = a_bound + b_term + d_term
        if not total < ONE:
            raise AssertionError(f"c-charge estimate not strict for {shape}: {total}")
        if worst_a_term > a_bound:
            raise AssertionError(f"a-term bound failed for {shape}: {worst_a_term}>{a_bound}")
    print("five c-charge estimates: PASS")


def audit_exhaustive(max_entry: int) -> None:
    primitive = 0
    b_bad = 0
    exactly_two_good = 0
    first_exact_two: tuple[int, int, int, int] | None = None

    for p in combinations(range(2, max_entry + 1), 4):
        if not is_primitive(p):
            continue
        primitive += 1
        a, b, c, d = p

        if not charge_sum(p, a) < ONE:
            raise AssertionError(f"least element not good: {p}, charge={charge_sum(p, a)}")

        gcount = good_count(p)
        if gcount < 2:
            raise AssertionError(f"fewer than two good charges: {p}")
        if gcount == 2 and first_exact_two is None:
            first_exact_two = p
        exactly_two_good += int(gcount == 2)

        if charge_sum(p, b) >= ONE:
            b_bad += 1
            q = a // gcd(a, b)
            u = c // gcd(b, c)
            v = d // gcd(b, d)
            shape = (Fraction(c, b), Fraction(d, b))
            if q != 2:
                raise AssertionError(f"b bad but q != 2: {p}, q={q}, u={u}, v={v}")
            if Fraction(1, u) + Fraction(1, v) < Fraction(1, 2):
                raise AssertionError(f"b bad but u/v inequality failed: {p}, u={u}, v={v}")
            if shape not in SHAPES:
                raise AssertionError(f"b bad shape outside list: {p}, shape={shape}")
            if not charge_sum(p, c) < ONE:
                raise AssertionError(f"b bad but c not good: {p}, charge(c)={charge_sum(p, c)}")

    print(f"primitive quadruples up to {max_entry}: {primitive}")
    print(f"  b bad cases: {b_bad}")
    print(f"  exactly two good charges: {exactly_two_good}")
    if first_exact_two is not None:
        print(f"  first exactly-two-good example: {first_exact_two}")
    print("bounded quadruple audit: PASS")


def main() -> None:
    max_entry = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    audit_weight_table()
    audit_shape_enumeration()
    audit_c_charge_estimates()
    audit_exhaustive(max_entry)


if __name__ == "__main__":
    main()
