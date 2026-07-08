# Computational results — Erdős #488

Computation is **evidence, not proof** (except where an exhaustive search space is
written down). All scripts are deterministic (fixed seed `20260707`; no wall-clock
or unseeded randomness). Python 3.13, `sympy` for prime lists only.

(A previous, unrelated `computational_results.md` was preserved as
`codex_leftover_computational_results.md`.)

## R1. Exhaustive finite verification of the theorem (★)

`python verify_exhaustive.py 15 3 200`

- Search space (fully enumerated): every `A ⊆ {2,…,15}` with `|A| ≤ 3`; every pair
  `max(A) ≤ n < m ≤ 200`.
- Result: **8,343,328 triples checked, 0 violations** of `n·B(m) < 2·m·B(n)`.
- Also: all **1,737,355** triples with `B(n) ≥ n/2` satisfy (★) — an independent
  check of the *dense-half* lemma (Theorem 3), which is separately proven.
- `RESULT: PASS`.

This exhaustively certifies (★) on the stated finite domain. It is not a proof of
the infinite statement, but it rules out any small counterexample.

## R2. Large / structured / adversarial search (`counterexample_search.py`, job I)

`python counterexample_search.py`

Families searched (with `max_ratio` = `max_{m>n≥max A} (B(m)/m)/(B(n)/n)`):
single elements up to `a=1000`; 2000 random sets (elements ≤120, `|A|≤8`,
`m` up to `25·max(A)`); intervals `[N, cN]` (Besicovitch-flavoured); prime shells
`primes(N,2N]` (Cambie-flavoured), `m` up to `≈3·10⁴`.

- **Worst ratio over everything: 1.999000**, attained by the single-element family
  `A={1000}` at `n=1999` (`= 2 − 1/1000`).
- No family reaches `2`. Structured multi-element sets stay well below (intervals
  ≲1.71, prime shells ≲1.55). **The supremum is the trivial single-element family.**

## R3. Sharpness (`counterexample_search.py`, job II)

Single-element extremal `A={a}, n=2a−1, m=2a`:

| a | B(n) | B(m) | ratio | 2−1/a |
|---|---|---|---|---|
| 2 | 1 | 2 | 1.500000 | 1.500000 |
| 5 | 1 | 2 | 1.800000 | 1.800000 |
| 50 | 1 | 2 | 1.980000 | 1.980000 |
| 1000 | 1 | 2 | 1.999000 | 1.999000 |

Confirms the constant `2` is best possible and approached only in the limit.

## R4. Disproof of the literal NON-MULTIPLES (typo) version (`job III`)

Family `A = primes ≤ n`, `m = 2n` (so `max(A) ≤ n`). Here `B'` = non-multiples.
`B'(n)=1` (only `1`); `B'(2n)=1+(π(2n)−π(n))` (`1` and the primes in `(n,2n]`).

| n | m | B'(n) | B'(2n) | B'(m)/m | 2·B'(n)/n | violates `<2`? |
|---|---|---|---|---|---|---|
| 10 | 20 | 1 | 5 | 0.2500 | 0.2000 | **yes (2.5×)** |
| 50 | 100 | 1 | 11 | 0.1100 | 0.0400 | **yes (5.5×)** |
| 100 | 200 | 1 | 22 | 0.1100 | 0.0200 | **yes (11×)** |
| 300 | 600 | 1 | 48 | 0.0800 | 0.0067 | **yes (24×)** |

Ratio `= (1+π(2n)−π(n))/2 → ∞` (Bertrand + PNT). Explicit smallest witness:
`A={2,3,5,7}, n=10, m=20`. This disproves the literal [Er61] statement and, since
Erdős's tightness witness fits only the multiples reading, pins the intended
problem as the multiples version.

## R5. Reconnaissance that led to selection (`scratch_probe*.py`)

Earlier probes (kept for provenance) found **no** small counterexamples to #287,
#375, #458, #699 (Erdős conjectures survive small searches, as expected), and
established the #488 max-ratio profile above. See `candidate_scan.md`.

## R6. Coverage of the reciprocal-sparse primitive-core theorem

The theorem in `proof_attempt.md` Section 3A proves #488 whenever the primitive
core `P` of `A`, with `a=min(P)`, satisfies

```text
sum_{d in P} 1/d <= 2/a.
```

Coverage sweep:

| domain | sets checked | covered | percent |
|---|---:|---:|---:|
| `A subset {2,...,20}`, `|A|<=4` | 5035 | 2898 | 57.557% |
| `A subset {2,...,40}`, `|A|<=4` | 92170 | 49065 | 53.233% |
| `A subset {2,...,60}`, `|A|<=5` | 5495791 | 2476171 | 45.056% |

First uncovered primitive examples:

```text
{2,3,5}, {3,4,5}, {3,4,7}
```

These are the next natural targets for a stronger publishable-track theorem.

## R7. Exact certificate for primitive triples with least element 3

Command:

```text
python verify_min3_triples.py
```

Output:

```text
A L D alpha beta beta/alpha min_witness max_witness
(3, 4, 5) 60 36 13/23 7/10 161/130 (23, 13) (10, 7)
(3, 4, 7) 84 48 7/13 2/3 26/21 (26, 14) (9, 6)
(3, 4, 10) 60 32 1/2 3/5 6/5 (38, 19) (10, 6)
(3, 4, 11) 132 72 1/2 13/22 13/11 (14, 7) (22, 13)
(3, 5, 7) 105 57 1/2 3/5 6/5 (8, 4) (15, 9)
RESULT: PASS
```

Together with the reciprocal-sparse theorem, this proves #488 for every
primitive three-element core `{3,b,c}`.

## R8. Exact certificate for primitive triples with least element at most 20

Command:

```text
python verify_triples_min_leq.py 20
```

Output summary:

```text
MAX_A=20
reciprocal-heavy primitive triples checked: 6944
count by least element:
  a=3: 5
  a=4: 14
  a=5: 28
  a=6: 48
  a=7: 74
  a=8: 108
  a=9: 148
  a=10: 195
  a=11: 252
  a=12: 313
  a=13: 383
  a=14: 463
  a=15: 551
  a=16: 646
  a=17: 751
  a=18: 863
  a=19: 986
  a=20: 1116
worst certified ratio beta/alpha:
  A=(19, 20, 21)
  L=7980 D=1140
  alpha=3/37 at (37, 3)
  beta=54/361 at (361, 54)
  beta/alpha=666/361 (1.844875346260)
RESULT: PASS
```

Together with the reciprocal-sparse theorem, this proves #488 for every
primitive three-element core `{a,b,c}` with `a<=20`.

## R9. Verification of the COMPLETE triple theorem (Theorem 9)

The general proof (`triples_writeup.md`) makes R7/R8 redundant as *proof*
components; the runs below verify every lemma of the new proof at scale.

Command (agent run at defaults, then independent re-run):

```text
python attack_triples.py            # A_MAX_FULL=25, A_MAX_SWEEP=60
python attack_triples.py 14 30      # independent re-run
```

Agent run (defaults): Part A — all 14,802 uncovered primitive triples with
`2<=a<=25`, every `n` over a full period `[c, c+lcm)` = 516,987,874 values
(ratio lemmas, X_a/X_b/X_c >= 1, s-2P >= 3, Bonferroni, strict `2B(n) > nS`,
union bound). Part B — ratio lemmas on 37,253,817 primitive triples. Part C —
end-to-end (★) on 1,209,671,136 `(n,m)` pairs (`a<=8`). Part D — window sweep,
156,263 triples `4<=a<=60`, 0 failures. Part E — abstract lemma unit tests
(13,336 configurations). ALL PASS. Independent re-run (`14 30`): PASS
(10,379,646 per-n values).

## R10. Independent criterion sweep and the |P|>=4 counterexample

```text
python sweep_criterion.py 40 40
```

Result: 71,003 reciprocal-heavy primitive triples (`a<=40`) and 42,769
primitive 4-sets (elements in `{3..40}`): **zero** failures of `delta >= S/2`
or of the per-period criterion `B(n) > nS/2`.

**But the universal per-n criterion is FALSE for large primitive families**
(adversarial finding): for `A = {2p : p prime <= 300}` (62 elements,
`max A = 586`), exact check over `n in [586, 2*10^6]` shows `2B(n) <= nS` at
**every** n (S = 1.0064 > 2*delta = 0.9025; already S > 2*delta at
`{2p : p <= 100}`, 25 elements). (★) itself still holds there since all
multiples are even (`sup g <= 1/2 < 2*delta`). Recorded in
`triples_writeup.md` §7 and `adversary_collab_chat.md`.

## Reproduce everything

```bash
python verify_exhaustive.py 15 3 200      # R1 exhaustive (PASS, 0 violations)
python counterexample_search.py           # R2–R4 (worst 1.999; disproof of typo version)
python verify_min3_triples.py             # R7 exact min-3 certificate (superseded by R9)
python verify_triples_min_leq.py 20       # R8 bounded-triple certificate (superseded by R9)
python attack_triples.py                  # R9 full verification of Theorem 9 (PASS)
python sweep_criterion.py 40 40           # R10 criterion sweep (PASS)
```
