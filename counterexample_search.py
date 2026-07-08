"""
Erdos Problem #488 — reproducible verification and disproof driver.
Run:  python counterexample_search.py
Deterministic (fixed seed). Only dependency: sympy (for prime lists).

(NOTE: a pre-existing, unrelated script previously occupied this filename; it was
 preserved as codex_leftover_counterexample_search.py before this file was written.)

Three jobs:
  (I)   VERIFY the intended MULTIPLES version (star) is true & tight on a large,
        explicitly described search space  -> no counterexample expected/found.
  (II)  Confirm the single-element extremal family gives ratio 2 - 1/a (-> 2).
  (III) DISPROVE the literal NON-MULTIPLES ("typo") version with an explicit
        infinite family; print a clean small witness.
"""
from sympy import primerange
import random
random.seed(20260707)

# ---------- shared counting ----------
def multiples_prefix(A, X):
    """B(x)=|{k<=x : some a in A divides k}| for x=0..X."""
    inB = bytearray(X + 1)
    for a in A:
        for x in range(a, X + 1, a):
            inB[x] = 1
    pref = [0] * (X + 1); c = 0
    for x in range(1, X + 1):
        c += inB[x]; pref[x] = c
    return pref

def nonmultiples_prefix(A, X):
    """B'(x)=|{k<=x : no a in A divides k}| = x - B(x)."""
    Bp = multiples_prefix(A, X)
    return [x - Bp[x] for x in range(X + 1)]

def max_ratio(pref, maxA, M):
    """max over M>=m>n>=maxA of (pref[m]/m)/(pref[n]/n), via suffix-max. O(M)."""
    d = [pref[x] / x if x >= 1 else 0.0 for x in range(M + 1)]
    suf = [0.0] * (M + 2)
    for x in range(M, 0, -1):
        suf[x] = d[x] if d[x] > suf[x + 1] else suf[x + 1]
    best = 0.0; arg = None
    for n in range(maxA, M):
        if d[n] == 0: continue
        r = suf[n + 1] / d[n]
        if r > best: best = r; arg = n
    return best, arg

# ---------- (I) verify multiples version ----------
def verify_multiples():
    print("=" * 70)
    print("(I) VERIFY intended MULTIPLES version:  B(m)/m < 2 B(n)/n,  m>n>=max(A)")
    print("    Search space: families below; report the single largest ratio seen.")
    worst = 0.0; worst_desc = ""
    def upd(desc, A, M):
        nonlocal worst, worst_desc
        pref = multiples_prefix(sorted(set(A)), M)
        r, n = max_ratio(pref, max(A), M)
        if r >= 2.0:
            print(f"    *** COUNTEREXAMPLE: {desc}  ratio={r} at n={n} ***")
        if r > worst: worst, worst_desc = r, f"{desc} (ratio={r:.6f}, n={n})"
        return r
    for a in [2, 3, 5, 10, 32, 100, 500, 1000]:
        upd(f"A={{{a}}}", [a], a * 4)
    for _ in range(2000):
        amax = random.randint(3, 120)
        k = random.randint(1, 8)
        A = random.sample(range(2, amax + 1), min(k, amax - 1))
        upd(f"rand {A}", A, max(4000, max(A) * 25))
    for N in [10, 25, 60, 150, 400]:
        for c in (1.2, 1.5, 2.0):
            A = list(range(N, int(c * N) + 1)); upd(f"int[{N},{int(c*N)}]", A, N * 40)
        A = list(primerange(N + 1, 2 * N + 1))
        if A: upd(f"primes({N},{2*N}]", A, max(A) * 30)
    print(f"    WORST RATIO over all families: {worst:.6f}  <- {worst_desc}")
    print(f"    => {'NO counterexample (<2): consistent with the theorem.' if worst < 2 else 'COUNTEREXAMPLE FOUND!'}")
    return worst

# ---------- (II) single-element extremal ----------
def show_extremal():
    print("=" * 70)
    print("(II) Single-element extremal family A={a}, n=2a-1, m=2a  ->  ratio 2-1/a")
    for a in [2, 5, 50, 1000]:
        pref = multiples_prefix([a], 2 * a)
        n, m = 2 * a - 1, 2 * a
        ratio = (pref[m] / m) / (pref[n] / n)
        print(f"    a={a:5d}:  B(n)={pref[n]}, B(m)={pref[m]},  ratio={ratio:.6f}  (2-1/a={2-1/a:.6f})")

# ---------- (III) disprove non-multiples (typo) version ----------
def disprove_nonmultiples():
    print("=" * 70)
    print("(III) DISPROVE literal NON-MULTIPLES version  B'(m)/m < 2 B'(n)/n")
    print("      Family: A = primes <= n, m = 2n. Ratio = (1 + pi(2n)-pi(n))/2 -> inf.")
    for n in [10, 20, 50, 100, 300]:
        A = list(primerange(2, n + 1))            # primes <= n ; max(A) <= n
        pref = nonmultiples_prefix(A, 2 * n)
        Bn, Bm = pref[n], pref[2 * n]
        lhs = Bm / (2 * n); rhs = 2 * Bn / n
        viol = lhs >= rhs
        print(f"    n={n:4d}  m={2*n:4d}: B'(n)={Bn}, B'(2n)={Bm}, "
              f"B'(m)/m={lhs:.4f} vs 2B'(n)/n={rhs:.4f}  ratio={(lhs/rhs)*2:.3f}x  "
              f"{'VIOLATES (<2 false)' if viol else 'ok'}")
    print("      => explicit counterexample already at n=10, m=20 (ratio 2.5x).")
    print("         Confirms the literal [Er61] text is disproved; the WITNESS in")
    print("         [Er61] only fits the multiples reading, so 'multiples' is intended.")

if __name__ == "__main__":
    verify_multiples()
    show_extremal()
    disprove_nonmultiples()
