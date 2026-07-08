"""
Exact finite certificates for Erdos #488, primitive 3-element cores with
least element at most a chosen bound.

Run:
    python verify_triples_min_leq.py          # default MAX_A=20
    python verify_triples_min_leq.py 10

Mathematical scope:
  Let P={a,b,c} be primitive with a<b<c. The reciprocal-sparse theorem in
  proof_attempt.md proves #488 whenever 1/b + 1/c <= 1/a. This script only
  enumerates the reciprocal-heavy triples

      1/b + 1/c > 1/a,

  which are finite for each fixed a. For every such triple with a<=MAX_A, it
  computes exact global bounds

      alpha <= B_P(x)/x <= beta,       x >= c,

  using periodicity modulo L=lcm(a,b,c). If beta < 2 alpha, #488 follows for
  that triple.

The script uses exact integer and rational arithmetic. It is a finite
certificate, not a heuristic search.
"""

from fractions import Fraction
from functools import reduce
from math import gcd
import sys


def lcm(a, b):
    return a * b // gcd(a, b)


def is_primitive(A):
    return all(A[j] % A[i] != 0 for i in range(len(A)) for j in range(i + 1, len(A)))


def reciprocal_heavy_triples(a):
    for b in range(a + 1, 2 * a):
        if b % a == 0:
            continue
        # 1/b + 1/c > 1/a is equivalent to c < ab/(b-a).
        c_max = (a * b - 1) // (b - a)
        for c in range(b + 1, c_max + 1):
            A = (a, b, c)
            if is_primitive(A):
                yield A


def exact_bounds(A):
    L = reduce(lcm, A, 1)
    c = max(A)
    marked = bytearray(L + 1)
    for d in A:
        for x in range(d, L + 1, d):
            marked[x] = 1

    D = sum(marked[1:])
    prefix = [0] * L
    count = 0
    alpha = None
    alpha_witness = None
    beta = None
    beta_witness = None

    # Check residues with q=0, i.e. c <= x <= L.
    for x in range(1, L + 1):
        count += marked[x]
        if x < L:
            prefix[x] = count
        if x >= c:
            value = Fraction(count, x)
            if alpha is None or value < alpha:
                alpha = value
                alpha_witness = (x, count)
            if beta is None or value > beta:
                beta = value
                beta_witness = (x, count)

    # For residues 1 <= r < c, q=0 is below the allowed range. The ratio
    # (Dq+f(r))/(Lq+r) is monotone in q, so checking q=1 plus the q=0 residues
    # above and the common limit D/L gives the exact global bounds.
    for r in range(1, c):
        value = Fraction(D + prefix[r], L + r)
        if value < alpha:
            alpha = value
            alpha_witness = (L + r, D + prefix[r])
        if value > beta:
            beta = value
            beta_witness = (L + r, D + prefix[r])

    density = Fraction(D, L)
    if density < alpha:
        alpha = density
        alpha_witness = ("limit", D, L)
    if density > beta:
        beta = density
        beta_witness = ("limit", D, L)

    return L, D, alpha, alpha_witness, beta, beta_witness


def verify(max_a):
    checked = 0
    worst_ratio = Fraction(0, 1)
    worst = None
    per_a = {}

    for a in range(3, max_a + 1):
        per_a[a] = 0
        for A in reciprocal_heavy_triples(a):
            checked += 1
            per_a[a] += 1
            L, D, alpha, alpha_witness, beta, beta_witness = exact_bounds(A)
            ratio = beta / alpha
            if ratio > worst_ratio:
                worst_ratio = ratio
                worst = (A, L, D, alpha, alpha_witness, beta, beta_witness, ratio)
            if not beta < 2 * alpha:
                raise AssertionError((A, L, D, alpha, alpha_witness, beta, beta_witness, ratio))

    return checked, per_a, worst


def main():
    max_a = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    checked, per_a, worst = verify(max_a)
    print(f"MAX_A={max_a}")
    print(f"reciprocal-heavy primitive triples checked: {checked}")
    print("count by least element:")
    for a, count in per_a.items():
        print(f"  a={a}: {count}")
    A, L, D, alpha, alpha_witness, beta, beta_witness, ratio = worst
    print("worst certified ratio beta/alpha:")
    print(f"  A={A}")
    print(f"  L={L} D={D}")
    print(f"  alpha={alpha} at {alpha_witness}")
    print(f"  beta={beta} at {beta_witness}")
    print(f"  beta/alpha={ratio} ({float(ratio):.12f})")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
