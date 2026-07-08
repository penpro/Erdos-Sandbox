"""
Erdos #488 -- COMPLETE proof verification for primitive triples {a,b,c}.

THE PROOF (see triples_writeup.md for full statements):

Let {a,b,c} be primitive (pairwise non-dividing), 2 <= a < b < c,
S = 1/a + 1/b + 1/c, B(n) = #{k <= n : a|k or b|k or c|k},
s(n) = fl(n/a)+fl(n/b)+fl(n/c),  P(n) = fl(n/Lab)+fl(n/Lac)+fl(n/Lbc)
where Lxy = lcm(x,y).

Covered zone (1/b + 1/c <= 1/a): Theorem 6 (reciprocal-sparse), proved earlier.

Uncovered zone (1/b + 1/c > 1/a): NEW.
  Lemma R (ratios; primitivity only):
      R1: Lab/a = b/gcd(a,b) >= 3      R4: Lab/b = a/gcd(a,b) >= 2
      R2: Lac/a = c/gcd(a,c) >= 3      R5: Lac/c = a/gcd(a,c) >= 2
      R3: Lbc/b = c/gcd(b,c) >= 3      R6: Lbc/c = b/gcd(b,c) >= 2
  Lemma R7 (uses 1/b+1/c > 1/a): NOT both Lac/c = 2 and Lbc/c = 2.
  Lemma X: for n >= c, with t_d = fl(n/d),
      X_a = t_a - fl(n/Lab) - fl(n/Lac) >= 1
      X_b = t_b - fl(n/Lab) - fl(n/Lbc) >= 1
      X_c = t_c - fl(n/Lac) - fl(n/Lbc) >= 1
    via fl(n/(q d)) = fl(t_d/q) and: an integer t - fl(t/q) - fl(t/q')
    with t>=1 and (q>=3,q'>=3) or (q>=2,q'>=3) is >= t/3 resp. t/6 > 0,
    hence >= 1.
  Lemma S2P: s(n) - 2 P(n) = X_a + X_b + X_c >= 3  for n >= c.
  THEOREM (per-n criterion): for n >= c,
      2 B(n) - n S >= 2 s(n) - 2 P(n) - n S            [Bonferroni]
                    > (s(n) - 3) - 2 P(n)              [{n/d} < 1 each]
                    >= 0.                              [Lemma S2P]
  COROLLARY (#488 for the triple): for all m > n >= c,
      B(m)/m <= S < 2 B(n)/n.
  (Ordering-free: in the uncovered zone  sup_m B(m)/m <= S < 2 inf_{n>=c} B(n)/n.)

This script verifies, with exact integer arithmetic:
  PART A: Lemmas R1-R7, X, S2P and the per-n criterion for ALL uncovered
          primitive triples with 2 <= a <= A_MAX_FULL (default 25),
          for EVERY n in a full period [c, c + lcm(a,b,c)).
  PART B: Ratio lemmas R1-R6 for all primitive triples (both zones),
          a <= 25, c <= 2000.
  PART C: End-to-end direct check of (#488) B(m)/m < 2 B(n)/n for small
          triples, all c <= n < c + L, n < m <= c + 3L.
  PART D: (discovery sweep, historical) window check 2B(n) > nS for
          n in [c, 6ac/(c-a)) for uncovered triples a <= A_MAX_SWEEP.
  PART E: brute-force unit tests of the abstract lemmas L1(i), L1(ii), L4,
          independent of the triple enumeration.

Run:  python attack_triples.py [A_MAX_FULL] [A_MAX_SWEEP]
"""

import sys
from math import gcd
from fractions import Fraction

def lcm(x, y):
    return x * y // gcd(x, y)

def primitive_triples(a_min, a_max, c_cap=None, uncovered_only=True):
    """Primitive triples a<b<c. If uncovered_only: 1/b+1/c > 1/a
    (forces b < 2a and c < ab/(b-a)); else c up to c_cap."""
    for a in range(a_min, a_max + 1):
        b_hi = 2 * a - 1 if uncovered_only else (c_cap or 2 * a) - 1
        for b in range(a + 1, b_hi + 1):
            if b % a == 0:
                continue
            if uncovered_only:
                c_hi = (a * b - 1) // (b - a)   # largest c with c(b-a) < ab
            else:
                c_hi = c_cap
            for c in range(b + 1, c_hi + 1):
                if c % a == 0 or c % b == 0:
                    continue
                if uncovered_only:
                    # exact check 1/b + 1/c > 1/a  <=>  a(b+c)... bc? :
                    # 1/b+1/c>1/a <=> a(c+b) > bc  <=> ac+ab > bc
                    assert a * c + a * b > b * c
                yield a, b, c

def part_A(a_max):
    n_triples = 0
    n_checks = 0
    for a, b, c in primitive_triples(2, a_max, uncovered_only=True):
        n_triples += 1
        Lab, Lac, Lbc = lcm(a, b), lcm(a, c), lcm(b, c)
        L = lcm(Lab, c)
        # --- Lemma R (integer ratio identities and bounds) ---
        assert Lab % a == 0 and Lab % b == 0
        r1, r4 = Lab // a, Lab // b
        r2, r5 = Lac // a, Lac // c
        r3, r6 = Lbc // b, Lbc // c
        assert r1 == b // gcd(a, b) and r1 >= 3, (a, b, c, "R1")
        assert r2 == c // gcd(a, c) and r2 >= 3, (a, b, c, "R2")
        assert r3 == c // gcd(b, c) and r3 >= 3, (a, b, c, "R3")
        assert r4 == a // gcd(a, b) and r4 >= 2, (a, b, c, "R4")
        assert r5 == a // gcd(a, c) and r5 >= 2, (a, b, c, "R5")
        assert r6 == b // gcd(b, c) and r6 >= 2, (a, b, c, "R6")
        # --- Lemma R7 ---
        assert not (r5 == 2 and r6 == 2), (a, b, c, "R7")

        W = a * b * c                     # common denominator
        SW = b * c + a * c + a * b        # S * W
        B = 0
        for n in range(1, c + L):
            if n % a == 0 or n % b == 0 or n % c == 0:
                B += 1
            if n < c:
                continue
            n_checks += 1
            ta, tb, tc = n // a, n // b, n // c
            pab, pac, pbc = n // Lab, n // Lac, n // Lbc
            # floor-collapse identity fl(n/(q d)) = fl(fl(n/d)/q)
            assert pab == ta // r1 == tb // r4
            assert pac == ta // r2 == tc // r5
            assert pbc == tb // r3 == tc // r6
            # --- Lemma X ---
            Xa = ta - pab - pac
            Xb = tb - pab - pbc
            Xc = tc - pac - pbc
            assert Xa >= 1, (a, b, c, n, "Xa")
            assert Xb >= 1, (a, b, c, n, "Xb")
            assert Xc >= 1, (a, b, c, n, "Xc")
            # --- Lemma S2P ---
            s = ta + tb + tc
            P = pab + pac + pbc
            assert s - 2 * P == Xa + Xb + Xc >= 3, (a, b, c, n, "S2P")
            # --- Bonferroni lower bound (sanity) ---
            assert B >= s - P, (a, b, c, n, "bonferroni")
            # --- THEOREM: per-n criterion, exact integers ---
            assert 2 * B * W > n * SW, (a, b, c, n, B, "PER-N CRITERION")
        # --- Corollary machinery: B(m) <= m S for ALL m (one period + slope) ---
        # B(m) <= s(m) <= mS is immediate; verify on one period anyway:
        Bm = 0
        for m in range(1, L + 1):
            if m % a == 0 or m % b == 0 or m % c == 0:
                Bm += 1
            assert Bm * W <= m * SW, (a, b, c, m, "union bound")
    print(f"PART A: {n_triples} uncovered primitive triples with 2<=a<={a_max}; "
          f"{n_checks} values of n over full periods. ALL LEMMAS + CRITERION PASS.")

def part_B(a_max=25, c_cap=2000):
    n = 0
    for a, b, c in primitive_triples(2, a_max, c_cap=c_cap, uncovered_only=False):
        n += 1
        Lab, Lac, Lbc = lcm(a, b), lcm(a, c), lcm(b, c)
        assert Lab // a >= 3 and Lac // a >= 3 and Lbc // b >= 3
        assert Lab // b >= 2 and Lac // c >= 2 and Lbc // c >= 2
        if a * c + a * b > b * c:  # uncovered zone: R7 must hold
            assert not (Lac // c == 2 and Lbc // c == 2), (a, b, c, "R7")
    print(f"PART B: ratio lemmas R1-R6 (and R7 where applicable) verified on "
          f"{n} primitive triples, a<={a_max}, c<={c_cap}. PASS.")

def part_C(a_max=8):
    n_pairs = 0
    for a, b, c in primitive_triples(2, a_max, uncovered_only=True):
        L = lcm(lcm(a, b), c)
        hi = c + 3 * L
        Bs = [0] * (hi + 1)
        B = 0
        for k in range(1, hi + 1):
            if k % a == 0 or k % b == 0 or k % c == 0:
                B += 1
            Bs[k] = B
        for n in range(c, c + L):
            for m in range(n + 1, hi + 1):
                n_pairs += 1
                assert Bs[m] * n < 2 * Bs[n] * m, (a, b, c, n, m, "#488")
    print(f"PART C: end-to-end #488 check, uncovered triples a<={a_max}, "
          f"{n_pairs} (n,m) pairs. PASS.")

def part_D(a_max):
    fails = 0
    trip = 0
    for a, b, c in primitive_triples(4, a_max, uncovered_only=True):
        if c >= 7 * a:
            continue
        trip += 1
        n_hi = (6 * a * c + (c - a) - 1) // (c - a)
        W = a * b * c
        SW = b * c + a * c + a * b
        B = 0
        for n in range(1, n_hi):
            if n % a == 0 or n % b == 0 or n % c == 0:
                B += 1
            if n >= c and 2 * B * W <= n * SW:
                fails += 1
                print("  WINDOW FAILURE:", a, b, c, n, B)
    print(f"PART D: window sweep a<={a_max}: {trip} triples, {fails} failures.")

def part_E():
    """Brute-force unit tests of the abstract lemmas, independent of any
    triple enumeration."""
    # Lemma 1(i): nested floor identity floor(n/(qd)) = floor(floor(n/d)/q)
    for n in range(0, 3001):
        for d in range(1, 25):
            for q in range(1, 25):
                assert n // (q * d) == (n // d) // q
    # Lemma 1(ii): t - fl(t/q) - fl(t/q') >= 1 for t>=1, q>=2, q'>=3
    for t in range(1, 1001):
        for q in range(2, 40):
            for qp in range(3, 40):
                assert t - t // q - t // qp >= 1
    # Lemma 4 (abstract): a<b<c, a/gcd(a,c)=2, b/gcd(b,c)=2 => 1/b+1/c <= 1/a
    cnt = 0
    for c in range(3, 2001):
        for a in range(2, c):
            if a % 2 == 0 and gcd(a, c) == a // 2:
                for b in range(a + 1, c):
                    if b % 2 == 0 and gcd(b, c) == b // 2:
                        cnt += 1
                        assert a * c + a * b <= b * c, (a, b, c)
    print(f"PART E: abstract lemma unit tests (L1(i), L1(ii), L4 on {cnt} "
          f"configurations). PASS.")

if __name__ == "__main__":
    a_full = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    a_sweep = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    part_E()
    part_B()
    part_C()
    part_D(a_sweep)
    part_A(a_full)
    print("RESULT: PASS")
