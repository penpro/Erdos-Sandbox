"""
Fast integer-arithmetic sweep of the per-A finite-check criterion for Erdos #488:
  criterion(A): delta >= S/2  AND  B(n) > n*S/2 for all n in [max(A), max(A)+L).
(If both hold, #488 holds for A — see proof_attempt.md union-bound + periodicity.)

Sweeps: (1) all reciprocal-heavy primitive triples 4 <= a <= AMAX_TRIPLE,
        (2) all primitive 4-sets from {3..N4} with small lcm,
looking for ANY set where the criterion fails (delta < S/2, or a period fail).
All comparisons are exact integer arithmetic (no floats).
"""
import sys
from math import gcd
from functools import reduce
from itertools import combinations

def lcm2(a, b): return a * b // gcd(a, b)

def primitive(A):
    return not any(x != y and y % x == 0 for x in A for y in A)

def check_A(A, L_cap=2_000_000):
    """Return (delta_ok, period_fail_ns) or None if lcm too large."""
    A = sorted(A); amax = A[-1]
    L = reduce(lcm2, A, 1)
    if L > L_cap: return None
    # S = num/den exactly
    den = reduce(lcm2, A, 1)
    num = sum(den // a for a in A)          # S = num/den
    # sieve B membership up to amax+L
    X = amax + L
    inB = bytearray(X + 1)
    for a in A:
        inB[a::a] = b'\x01' * ((X) // a)
    # prefix counts
    pref = [0] * (X + 1); c = 0
    for x in range(1, X + 1):
        c += inB[x]; pref[x] = c
    D = pref[L]
    delta_ok = 2 * D * den >= L * num            # delta >= S/2
    fails = [n for n in range(amax, amax + L)
             if not (2 * den * pref[n] > n * num)]  # B(n) > nS/2
    return delta_ok, fails

def sweep_triples(amax_lo=4, amax_hi=40, c_cap=2000, L_cap=2_000_000):
    bad_dc, bad_per, count, skipped = [], [], 0, 0
    for a in range(amax_lo, amax_hi + 1):
        for b in range(a + 1, 2 * a):
            # reciprocal-heavy: 1/b + 1/c > 1/a  <=>  c < ab/(b-a)
            cmax = (a * b) // (b - a) + 1
            for c in range(b + 1, min(cmax + 1, c_cap)):
                if b * c + a * c + a * b <= 0: continue
                # exact reciprocal-heavy test: 1/b+1/c > 1/a <=> a(c+b) > bc
                if a * (b + c) <= b * c: continue
                A = (a, b, c)
                if not primitive(A): continue
                r = check_A(A, L_cap)
                if r is None: skipped += 1; continue
                count += 1
                dc, fails = r
                if not dc: bad_dc.append(A)
                if fails: bad_per.append((A, fails[:4]))
    return count, skipped, bad_dc, bad_per

def sweep_4sets(n4=40, L_cap=400_000):
    bad_dc, bad_per, count, skipped = [], [], 0, 0
    for A in combinations(range(3, n4 + 1), 4):
        if not primitive(A): continue
        r = check_A(A, L_cap)
        if r is None: skipped += 1; continue
        count += 1
        dc, fails = r
        if not dc: bad_dc.append(A)
        if fails: bad_per.append((A, fails[:4]))
    return count, skipped, bad_dc, bad_per

if __name__ == "__main__":
    amax_hi = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    n4 = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    c, s, bdc, bper = sweep_triples(4, amax_hi)
    print(f"[triples a<={amax_hi}] tested={c} skipped(lcm-cap)={s}")
    print(f"  delta<S/2 failures : {len(bdc)}  {bdc[:10]}")
    print(f"  period-check fails : {len(bper)}  {bper[:10]}")
    c, s, bdc, bper = sweep_4sets(n4)
    print(f"[4-sets from 3..{n4}] tested={c} skipped(lcm-cap)={s}")
    print(f"  delta<S/2 failures : {len(bdc)}  {bdc[:10]}")
    print(f"  period-check fails : {len(bper)}  {bper[:10]}")
