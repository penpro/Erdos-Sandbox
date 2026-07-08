"""
Exact finite certificates for Erdos #488, primitive 3-element cores with min 3.

Run:
    python verify_min3_triples.py

The reciprocal-sparse primitive-core theorem proves every triple {3,b,c} except
the five reciprocal-heavy primitive triples listed below. For each exceptional
triple, this script proves exact global bounds

    alpha <= B(x)/x <= beta       for all x >= max(A)

using only periodicity modulo L = lcm(A) and exact rational arithmetic. Since
beta < 2 alpha in every case, #488 follows for that triple.
"""

from fractions import Fraction
from functools import reduce
from math import gcd


CASES = {
    (3, 4, 5): (Fraction(13, 23), Fraction(7, 10)),
    (3, 4, 7): (Fraction(7, 13), Fraction(2, 3)),
    (3, 4, 10): (Fraction(1, 2), Fraction(3, 5)),
    (3, 4, 11): (Fraction(1, 2), Fraction(13, 22)),
    (3, 5, 7): (Fraction(1, 2), Fraction(3, 5)),
}


def lcm(a, b):
    return a * b // gcd(a, b)


def prefix_one_period(A, L):
    f = [0] * L
    count = 0
    for r in range(1, L):
        if any(r % a == 0 for a in A):
            count += 1
        f[r] = count
    period_count = count + (1 if any(L % a == 0 for a in A) else 0)
    return f, period_count


def verify_case(A, alpha, beta):
    A = tuple(A)
    L = reduce(lcm, A, 1)
    f, D = prefix_one_period(A, L)
    assert D == sum(1 for x in range(1, L + 1) if any(x % a == 0 for a in A))

    witnesses = {"min": None, "max": None}
    for r in range(L):
        q_min = 0 if r >= max(A) else 1
        if r == 0:
            q_min = 1
        fr = f[r] if r != 0 else 0

        # B(Lq+r) = Dq + f(r), for r=0 interpreted as B(Lq)=Dq.
        low_slope = D - alpha * L
        low_at_start = low_slope * q_min + fr - alpha * r
        high_slope = D - beta * L
        high_at_start = high_slope * q_min + fr - beta * r

        assert low_slope >= 0, (A, "lower slope", r, low_slope)
        assert low_at_start >= 0, (A, "lower start", r, low_at_start)
        assert high_slope <= 0, (A, "upper slope", r, high_slope)
        assert high_at_start <= 0, (A, "upper start", r, high_at_start)

        x = L * q_min + r
        val = Fraction(D * q_min + fr, x)
        if val == alpha:
            witnesses["min"] = (x, D * q_min + fr)
        if val == beta:
            witnesses["max"] = (x, D * q_min + fr)

    assert beta < 2 * alpha, (A, alpha, beta)
    return L, D, witnesses


def main():
    print("A L D alpha beta beta/alpha min_witness max_witness")
    for A, (alpha, beta) in CASES.items():
        L, D, witnesses = verify_case(A, alpha, beta)
        print(
            A,
            L,
            D,
            f"{alpha.numerator}/{alpha.denominator}",
            f"{beta.numerator}/{beta.denominator}",
            f"{(beta / alpha).numerator}/{(beta / alpha).denominator}",
            witnesses["min"],
            witnesses["max"],
        )
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
