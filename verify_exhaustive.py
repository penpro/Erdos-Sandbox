"""
Erdos #488 — EXHAUSTIVE finite verification of the intended (multiples) theorem
    (star)  n*B(m) < 2*m*B(n)   for all  m>n>=max(A).
and of the proven 'dense-half' lemma (B(n)>=n/2 => star), on a fully described
finite search space. Deterministic; no randomness.

Search space (exhaustive):
  * every nonempty A subset of {2,...,AMAX} with |A|<=KMAX and max(A)=amax,
    for amax=2..AMAX;
  * every pair (n,m) with max(A) <= n < m <= M.
Prints total triples checked, theorem violations (must be 0), and how many
triples fall under the dense-half lemma (all of which must also satisfy star).

Defaults (AMAX=15,KMAX=3,M=200) cover 8.3M triples in ~1 min.
"""
from itertools import combinations
import sys

def multiples_prefix(A, X):
    inB = bytearray(X + 1)
    for a in A:
        for x in range(a, X + 1, a):
            inB[x] = 1
    pref = [0] * (X + 1); c = 0
    for x in range(1, X + 1):
        c += inB[x]; pref[x] = c
    return pref

def run(AMAX=15, KMAX=3, M=200):
    checked = viol = dense = dense_ok = 0
    for amax in range(2, AMAX + 1):
        for r in range(1, KMAX + 1):
            for A in combinations(range(2, amax + 1), r):
                if max(A) != amax:
                    continue
                pref = multiples_prefix(A, M)
                a = amax
                for n in range(a, M):
                    Bn = pref[n]
                    twoN_dense = (2 * Bn >= n)
                    for m in range(n + 1, M + 1):
                        checked += 1
                        star = n * pref[m] < 2 * m * Bn
                        if not star:
                            viol += 1
                            if viol <= 5:
                                print("VIOLATION:", A, "n=", n, "m=", m,
                                      "B(n)=", Bn, "B(m)=", pref[m])
                        if twoN_dense:
                            dense += 1
                            if star:
                                dense_ok += 1
    print(f"AMAX={AMAX} KMAX={KMAX} M={M}")
    print(f"triples checked      : {checked}")
    print(f"theorem violations   : {viol}    (must be 0)")
    print(f"dense-half triples   : {dense}    (all must satisfy star: {dense_ok} do)")
    print("RESULT:", "PASS" if (viol == 0 and dense == dense_ok) else "FAIL")

if __name__ == "__main__":
    AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    M = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    run(AMAX, KMAX, M)
