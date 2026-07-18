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

## R11. Fast Rust workbench and size-4 charge rescue

Claude started `fastcheck/` as a Rust bounded-window checker; Codex added exact
periodic-certificate commands and a symbolic classifier for the new quadruple
charge lemma in `quadruple_charge_notes.md`.

Sanity checks matched the older Python certificates exactly:

```text
{3,4,5}: alpha=13/23 at x=23, beta=7/10 at x=10, beta/alpha=161/130
{19,20,21}: alpha=3/37 at x=37, beta=54/361 at x=361, beta/alpha=666/361
```

Local size-4 proof: for a primitive quadruple, at least two generator charges
satisfy

```text
sum_{f != e} gcd(e,f)/f < 1,
```

and exact four-set inclusion-exclusion then gives `2B(n)>nS` for all
`n>=max(P)`, hence the ordering-free #488 inequality. This is a proof claim in
`quadruple_charge_notes.md`; the computation below is only a backstop.

Quadruple sweep:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quad-cert 150 3000000

primitive quadruples with entries <= 150: 15,591,140
reciprocal-sparse theorem applies: 6,090,059
charge-positivity theorem applies: 15,577,302
two-good-charge rescue condition applies: 15,591,140
symbolically done by sparse or two-good-charge rescue: 15,591,140
residual after those regimes: 0
```

Thus every primitive quadruple with entries `<=150` has at least two good
charges, matching the proof. Examples with exactly two good charges exist, e.g.
`{12,20,30,45}`, so the theorem is genuinely stronger than full
charge-positivity.

## R12. Independent audit of the size-4 proof skeleton

Command:

```text
python audit_quadruple_charge.py 80
```

Output:

```text
pointwise Y weight table: PASS
five-shape enumeration under b bad: PASS
five c-charge estimates: PASS
primitive quadruples up to 80: 1037468
  b bad cases: 41
  exactly two good charges: 74
  first exactly-two-good example: (3, 4, 10, 25)
bounded quadruple audit: PASS
```

This script is not the proof; it is a referee backstop for the three delicate
steps in `quadruple_charge_notes.md`.

## R13. First size-5 reconnaissance

Command:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- quints 35 80 --uncovered
```

Output summary:

```text
primitive uncovered 5-sets tested: 88,603
worst ratio = 8784/4805 = 1.828095734 at {31,32,33,34,35}
counterexamples: none in window
```

The worst set is charge-positive, hence covered by the general charge-positive
criterion. Two primitive shared-factor stress examples with bad charges also
stayed well below 2 in bounded windows:

```text
{6,10,15,25,49}: worst = 1.114423077 in [49,5880]
{10,14,15,21,35}: worst = 1.191666667 in [35,4200]
```

This is only reconnaissance. It suggests the next tool upgrade should classify
quintuples by symbolic regimes rather than just window-search them.

The requested tool upgrade now exists:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quint-cert 100 3000000 60
```

Output summary:

```text
primitive quintuples with entries <= 100: 43,291,981
2-in-A theorem applies: 162,293
scaled Q-family audit applies: 6
scaled R-family audit applies: 8
scaled T-family audit applies: 1
scaled U-family audit applies: 2
scaled V-family audit applies: 7
scaled W-family audit applies: 7
scaled X-family audit applies: 2
scaled Y-family audit applies: 6
scaled Z-family audit applies: 6
scaled AA-family audit applies: 6
scaled AB-family audit applies: 6
scaled AC-family audit applies: 6
scaled AD-family audit applies: 6
scaled AE-family audit applies: 6
scaled AF-family audit applies: 6
scaled AG-family audit applies: 6
scaled AH-family audit applies: 5
scaled AI-family audit applies: 5
scaled AJ-family audit applies: 5
scaled AK-family audit applies: 5
scaled AL-family audit applies: 5
scaled AM-family audit applies: 4
scaled AN-family audit applies: 4
scaled AO-family audit applies: 4
scaled AP-family audit applies: 4
scaled AQ-family audit applies: 4
scaled AR-family audit applies: 4
scaled AS-family audit applies: 4
scaled AT-family audit applies: 4
scaled AU-family audit applies: 4
scaled AV-family audit applies: 4
scaled AW-family audit applies: 4
scaled AX-family audit applies: 4
reciprocal-sparse theorem applies: 10,438,657
charge-positivity theorem applies: 43,007,879
three-good-charge rescue condition applies: 43,290,285
handled by 2-in-A, scaled-family audits, sparse, or three-good-charge rescue: 43,291,031
residual after those regimes: 950
ordering-free PASS: 950
ordering-free FAIL: 0
union-bound separator PASS: 950
union-bound separator FAIL: 0
```

Worst residual after peeling the scaled-family audits:

```text
{40,48,60,72,90}
alpha = 15/269 at x=269
beta  = 7/96 at x=96
beta/alpha = 1883/1440 = 1.307638888889
```

The formerly worst layer is a scaled copy of `{4,6,10,14,15}`. For
`t*{4,6,10,14,15}`, observed
certificates have `alpha = 15/(40t-1)`, `beta = 1/(2t)`, and
`beta/alpha = (40t-1)/(30t) -> 4/3`. The formula is now derived in
`quintuple_charge_notes.md` from the exact base certificate plus a finite table
for `15<=q<39`.

Windowed search was also extended:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- quints 70 80 --uncovered
primitive uncovered 5-sets tested: 4,707,003
worst ratio = 35574/18605 = 1.912066649 at {61,62,63,64,65}
counterexamples: none in window
```

Failed naive generalization: "every primitive quintuple has at least three good
charges" is false. Small witnesses:

```text
{2,3,5,7,11}: only two good charges
{3,4,10,14,22}: only two good charges
```

For the primitive no-`2` witness `{3,4,10,14,22}`, exact certification is safe:

```text
alpha = 53/97 at x=97
beta  = 7/11 at x=22
beta/alpha = 679/583 = 1.164665523156
union-bound separator S < 2B(n)/n for all n>=max(A) = true
```

So this breaks only the naive charge-count route, not the inequality.

## R14. Exact scaled-family audit for thirty-three quintuple residual classes

Command:

```text
python audit_scaled_quint_families.py
```

Output excerpt:

```text
Q = {4,6,10,14,15}: PASS
  base=[4, 6, 10, 14, 15], t_min=1, lcm=420, period_count=176
  alpha=15/(40t-1), witness q=39
  beta=1/(2t), equality q=[16, 18, 20]
  beta/alpha limit=40/30
  increments: alpha_slope=740, alpha_tmin=564, beta_gap=68
R = {2,3,5,7,11}: PASS
  base=[2, 3, 5, 7, 11], t_min=2, lcm=2310, period_count=1830
  alpha=36/(48t-1), witness q=47
  beta=11/(12t), equality q=[12]
  beta/alpha limit=528/432
  increments: alpha_slope=4680, alpha_tmin=7530, beta_gap=3450
T = {32,45,48,72,80}: PASS
  base=[32, 45, 48, 72, 80], t_min=1, lcm=1440, period_count=104
  alpha=8/(128t-1), witness q=127
  beta=1/(12t), equality q=[96]
  beta/alpha limit=128/96
  increments: alpha_slope=1792, alpha_tmin=1688, beta_gap=192
U = {16,24,36,40,45}: PASS
  base=[16, 24, 36, 40, 45], t_min=1, lcm=720, period_count=88
  alpha=7/(64t-1), witness q=63
  beta=7/(48t), equality q=[48]
  beta/alpha limit=448/336
  increments: alpha_slope=592, alpha_tmin=504, beta_gap=816
V = {4,5,6,9,14}: PASS
  base=[4, 5, 6, 9, 14], t_min=1, lcm=1260, period_count=668
  alpha=31/(63t-1), witness q=62
  beta=5/(8t), equality q=[16]
  beta/alpha limit=315/248
  increments: alpha_slope=3024, alpha_tmin=2356, beta_gap=956
W = {4,6,9,10,14}: PASS
  base=[4, 6, 9, 10, 14], t_min=1, lcm=1260, period_count=556
  alpha=16/(40t-1), witness q=39
  beta=1/(2t), equality q=[14, 16, 18, 20]
  beta/alpha limit=40/32
  increments: alpha_slope=2080, alpha_tmin=1524, beta_gap=148
X = {12,20,30,45,50}: PASS
  base=[12, 20, 30, 45, 50], t_min=1, lcm=900, period_count=136
  alpha=18/(132t-1), witness q=131
  beta=9/(50t), equality q=[50]
  beta/alpha limit=1188/900
  increments: alpha_slope=1752, alpha_tmin=1616, beta_gap=1300
Y = {2,3,5,7,13}: PASS
  base=[2, 3, 5, 7, 13], t_min=2, lcm=2730, period_count=2154
  alpha=36/(48t-1), witness q=47
  beta=7/(8t), equality q=[16]
  beta/alpha limit=336/288
  increments: alpha_slope=5112, alpha_tmin=8070, beta_gap=1878
Z = {2,3,5,11,13}: PASS
  base=[2, 3, 5, 11, 13], t_min=2, lcm=4290, period_count=3330
  alpha=37/(50t-1), witness q=49
  beta=7/(8t), equality q=[16]
  beta/alpha limit=350/296
  increments: alpha_slope=7770, alpha_tmin=12210, beta_gap=3390
AA = {2,3,7,11,13}: PASS
  base=[2, 3, 7, 11, 13], t_min=2, lcm=6006, period_count=4566
  alpha=23/(32t-1), witness q=31
  beta=7/(8t), equality q=[16]
  beta/alpha limit=224/184
  increments: alpha_slope=7974, alpha_tmin=11382, beta_gap=5514
AB = {4,6,7,9,15}: PASS
  base=[4, 6, 7, 9, 15], t_min=1, lcm=1260, period_count=624
  alpha=29/(63t-1), witness q=62
  beta=4/(7t), equality q=[21]
  beta/alpha limit=252/203
  increments: alpha_slope=2772, alpha_tmin=2148, beta_gap=672
AC = {4,6,7,10,15}: PASS
  base=[4, 6, 7, 10, 15], t_min=1, lcm=420, period_count=204
  alpha=18/(40t-1), witness q=39
  beta=4/(7t), equality q=[21]
  beta/alpha limit=160/126
  increments: alpha_slope=600, alpha_tmin=396, beta_gap=252
AD = {4,6,9,10,15}: PASS
  base=[4, 6, 9, 10, 15], t_min=1, lcm=180, period_count=80
  alpha=16/(40t-1), witness q=39
  beta=1/(2t), equality q=[16, 18, 20]
  beta/alpha limit=40/32
  increments: alpha_slope=320, alpha_tmin=240, beta_gap=20
AE = {4,6,9,11,15}, small scales: PASS
  base=[4, 6, 9, 11, 15], t_values=[1, 2, 3, 4, 5, 6, 7, 8], lcm=1980, period_count=920
  alpha=33/(75t-1), witness q=74
  beta=17/(33t), equality q=[33]
  beta_gap_increment=3300
AE = {4,6,9,11,15}, large scales: PASS
  base=[4, 6, 9, 11, 15], t_min=9, lcm=1980, period_count=920
  alpha=7/(16t-1), witness q=15
  beta=17/(33t), equality q=[33]
  beta/alpha limit=272/231
  increments: alpha_slope=860, alpha_tmin=6820, beta_gap=3300
AF = {4,6,9,13,15}: PASS
  base=[4, 6, 9, 13, 15], t_min=1, lcm=2340, period_count=1068
  alpha=10/(24t-1), witness q=23
  beta=1/(2t), equality q=[16, 18, 20, 28, 30, 32]
  beta/alpha limit=24/20
  increments: alpha_slope=2232, alpha_tmin=1164, beta_gap=204
AG = {4,6,9,14,15}: PASS
  base=[4, 6, 9, 14, 15], t_min=1, lcm=1260, period_count=548
  alpha=25/(63t-1), witness q=62
  beta=1/(2t), equality q=[16, 18, 20]
  beta/alpha limit=63/50
  increments: alpha_slope=3024, alpha_tmin=2476, beta_gap=164
AH = {4,6,9,15,17}: PASS
  base=[4, 6, 9, 15, 17], t_min=1, lcm=3060, period_count=1364
  alpha=11/(27t-1), witness q=26
  beta=1/(2t), equality q=[18, 20]
  beta/alpha limit=27/22
  increments: alpha_slope=3168, alpha_tmin=1804, beta_gap=332
AI = {4,6,9,15,19}: PASS
  base=[4, 6, 9, 15, 19], t_min=1, lcm=3420, period_count=1512
  alpha=11/(27t-1), witness q=26
  beta=1/(2t), equality q=[20]
  beta/alpha limit=27/22
  increments: alpha_slope=3204, alpha_tmin=1692, beta_gap=396
AJ = {4,7,10,15,18}, small scales: PASS
  base=[4, 7, 10, 15, 18], t_values=[1, 2], lcm=1260, period_count=564
  alpha=53/(124t-1), witness q=123
  beta=11/(21t), equality q=[21]
  beta_gap_increment=2016
AJ = {4,7,10,15,18}, large scales: PASS
  base=[4, 7, 10, 15, 18], t_min=3, lcm=1260, period_count=564
  alpha=17/(40t-1), witness q=39
  beta=11/(21t), equality q=[21]
  beta/alpha limit=440/357
  increments: alpha_slope=1140, alpha_tmin=2856, beta_gap=2016
AK = {8,10,12,15,18}, t=1: PASS
  base=[8, 10, 12, 15, 18], t_values=[1], lcm=360, period_count=104
  alpha=28/(104t-1), witness q=103
  beta=7/(20t), equality q=[20]
  beta_gap_increment=440
AK = {8,10,12,15,18}, t>=2: PASS
  base=[8, 10, 12, 15, 18], t_min=2, lcm=360, period_count=104
  alpha=12/(45t-1), witness q=44
  beta=7/(20t), equality q=[20]
  beta/alpha limit=315/240
  increments: alpha_slope=360, alpha_tmin=616, beta_gap=440
AL = {8,12,15,18,20}, t=1: PASS
  base=[8, 12, 15, 18, 20], t_values=[1], lcm=360, period_count=92
  alpha=17/(72t-1), witness q=71
  beta=3/(10t), equality q=[20]
  beta_gap_increment=160
AL = {8,12,15,18,20}, t>=2: PASS
  base=[8, 12, 15, 18, 20], t_min=2, lcm=360, period_count=92
  alpha=7/(30t-1), witness q=29
  beta=3/(10t), equality q=[20]
  beta/alpha limit=90/70
  increments: alpha_slope=240, alpha_tmin=388, beta_gap=160
```

The same script also exact-audits AM through AX:

```text
AM={2,3,5,7,17}:      alpha=36/(48t-1), beta=5/(6t),    t>=2, PASS
AN={2,3,5,7,19}:      alpha=36/(48t-1), beta=23/(28t),  t>=2, PASS
AO={3,4,10,14,22}:    three-piece alpha, beta=7/(11t),  PASS
AP={3,4,10,14,25}:    three-piece alpha, beta=17/(28t), PASS
AQ={3,4,10,22,25}:    alpha=53/(99t-1), beta=17/(28t), t>=1, PASS
AR={4,5,6,9,21}:      alpha=31/(63t-1), beta=4/(7t),   t>=1, PASS
AS={4,6,9,10,22}:     alpha=16/(40t-1), beta=15/(32t), t>=1, PASS
AT={4,6,9,10,25}:     alpha=16/(40t-1), beta=15/(32t), t>=1, PASS
AU={4,6,9,14,21}:     alpha=25/(63t-1), beta=10/(21t), t>=1, PASS
AV={4,6,9,14,22}:     alpha=25/(63t-1), beta=15/(32t), t>=1, PASS
AW={4,6,9,15,21}:     alpha=25/(63t-1), beta=10/(21t), t>=1, PASS
AX={4,6,9,15,22}:     alpha=25/(63t-1), beta=15/(32t), t>=1, PASS
```

For AO and AP, the three alpha pieces are:

```text
t=1:     alpha=53/(98t-1)
2<=t<=4: alpha=47/(87t-1)
t>=5:    alpha=21/(39t-1)
```

Interpretation: thirty-three high-ratio scaled residual classes now have exact
infinite-family certificates. This is useful structure, not a claim that size 5
is solved.

Resolved near-miss: `{4,6,9,11,15}` fits `alpha=33/(75t-1)` only through
`t=8`; the all-`t` audit correctly rejected that single formula because the
alpha slope is negative at `q=15`. A two-piece audit now proves it with
`alpha=33/(75t-1)` for `1<=t<=8`, `alpha=7/(16t-1)` for `t>=9`, and
`beta=17/(33t)` throughout.

## Size-5 density diagnostics (2026-07-09)

`fastcheck` now has exact density diagnostics:

```text
quint-density <amax> [--gcd1] [--uncovered] [--hard] [--residual] [--top K]
density <a,b,c,d,e>
```

All-gcd1 density sweep:

```text
quint-density 120 --gcd1 --top 15
tested = 114,647,427
failures (2*delta <= S): NONE
smallest positive 2*delta-S = 2509/99360
at {72,96,108,115,120}
```

The all-quintuple near-misses are explained by the good-charge family

```text
F(q,h) = {6q,8q,9q,10q-h,10q},
2*delta-S = 37/(120q) + O(1/q^2).
```

These sets have five good charges in the checked examples, so they stress a
universal density proof but are not the present <=2-good residual obstruction.

Residual-only exact density sweep:

```text
quint-density 150 --gcd1 --residual --top 20
tested = 1,185
failures (2*delta <= S): NONE
smallest positive 2*delta-S = 7/240
at {54,80,90,120,135}

cert 54,80,90,120,135 3000000
beta/alpha = 319/240
union-bound separator = true
```

Finite lemma audit for Claude's second-order density proof:

```text
python audit_quint_density_lemma.py --brute 50
prime-pattern minimum = 157/300 at (2,2,3,5)
Route B {2,3,5,7} multiset check: 35 checked, best = 157/300
Route B primes <= 13 multiset check: 126 checked, best = 157/300
collision warnings verified:
  E(2,2,3,3) = 8/15 > E(2,2,3,5) = 157/300
  E(2,3,11,11) = 799/1320 > E(2,3,11,13) = 2359/3960
brute arbitrary moduli <= 50: best = 157/300 at (2,2,3,5)
RESULT: PASS
```

Consequence of the density gap `2delta-S >= (7/150)S`: since five-set
inclusion-exclusion gives `B(n) >= delta*n - 16`, every primitive quintuple
satisfies the raw separator `2B(n)>nS` for `n >= 138 max(P)`. The remaining
separator work is the fixed relative window `max(P) <= n < 138 max(P)`.

The first part of that window is also proved directly: if
`max(P) <= n < 2 min(P)`, then `B(n)=5` and `nS<10=2B(n)`.

Full crude-window separator census through the previous range:

```text
quint-separator 80 138 --uncovered
tested = 9,799,967
failures = NONE
worst = 3491573453/3606002400 at {76,77,78,79,80}, n=151
```

After skipping the proved first window:

```text
quint-separator 80 138 --uncovered --middle
tested = 9,799,967
failures = NONE
worst = 4097649/4564560 at {50,75,76,77,78}, n=149
```

This matches the family `P_t={2t,3t,3t+1,3t+2,3t+3}`, `n=6t-1`; at `t=25`
the ratio is exactly `4097649/4564560`, and the family tends to `11/12`.

Cover-class census for the current remaining size-5 bridge:

```text
quint-separator 200 33 --cover
filter = gcd(P)=1, good_charge_count(P)<=2, max(P)*sum(1/a)<=1135/7
tested = 4,347
skipped(filter) = 2,568
pruned(partial) = 1,101,443,697
failures = NONE
worst = 34359/40320 at {4,6,9,10,14}, n=39
```

G3-oriented stats from the same broad cover class, using the cheap one-point
window only for counting:

```text
quint-separator 200 1 --cover
tested = 4,347
max min(A) = 56
min(A)>54 count = 2
fourth(A)>120 count = 606

first min(A)>54 cover candidates:
  {56,72,84,126,189}
  {56,84,108,126,189}
```

These two `min(A)>54` candidates do not look like a G3-inventory break: both are
C3-style continuations, `{72} union 7*{8,12,18,27}` and
`{108} union 7*{8,12,18,27}`, and the tower inequality passes with comfortable
margins.

Claude's later G3 correction found larger rider-junk witnesses; independent
`classify` and `tower` checks confirm they are genuine min-bound counterexamples
but not separator failures:

```text
{108,140,210,315,378}: primitive, gcd 1, exactly 2 good, max*S=51/5
  tower min margin = 14/3 at m=419, PASS
{116,117,174,261,435}: primitive, gcd 1, exactly 2 good, max*S=657/52
  tower min margin = 294/65 at m=463, PASS
{216,232,348,522,783}: primitive, gcd 1, exactly 2 good, max*S=47/4
  tower min margin = 146/29 at m=863, PASS
{2376,2392,39468,59202,88803}: primitive, gcd 1, exactly 2 good, max*S=317/4
  tower min margin = 21954/299 at m=90287, PASS
```

Top cover-class separator witnesses through `amax=150`:

```text
quint-separator 150 33 --cover --top 20
1.  34359/40320  at {4,6,9,10,14}, n=39
2.  2145/2520    at {4,6,10,14,15}, n=39
3.  975/1152     at {4,6,9,10,15}, n=39
4.  4183/5040    at {4,6,10,14,21}, n=47
5.  9559/11520   at {8,12,18,20,45}, n=79
6.  137569/166320 at {2,3,5,7,11}, n=47
7.  8927/10800   at {8,12,20,30,45}, n=79
8.  52018/63000  at {4,6,9,14,15}, n=62
9.  28519/34560  at {8,12,18,27,30}, n=79
10. 51987/63360  at {4,6,9,10,22}, n=39
11. 2067/2520    at {4,6,10,15,21}, n=39
12. 160787/196560 at {2,3,5,7,13}, n=47
13. 3237/3960    at {4,6,10,15,22}, n=39
14. 5293/6480    at {12,18,20,27,45}, n=79
15. 184917/226800 at {40,60,81,90,150}, n=159
16. 23439/28800  at {4,6,9,10,25}, n=39
17. 3515/4320    at {4,6,10,14,35}, n=95
18. 272283/335160 at {28,42,57,63,105}, n=111
19. 82532/101640 at {28,42,63,99,105}, n=188
20. 60801/74880  at {4,6,9,10,26}, n=39
```

Full-period spot checks for Claude's infinite two-good family:

```text
cert 12,20,30,45,105 3000000:  beta/alpha = 2227/1944, separator true
cert 12,20,30,45,735 3000000:  beta/alpha = 96163/93696, separator true
cert 12,20,30,45,1515 3000000: beta/alpha = 127251/125656, separator true
```

Independent tower-margin spot checks for Claude's quoted C1 bank witnesses:

```text
tower 76,114,153,171,285:
  min margin = 638/255 at m=303, PASS
tower 40,60,81,90,150:
  min margin = 1018/405 at m=159, PASS
tower 28,42,57,63,105:
  min margin = 2158/855 at m=111, PASS
```

## Size-6 density kernel audit (2026-07-10)

Command:

```text
python audit_sext_density_lemma.py --bound 25 --friend-limit 3000 --peel-bound 16
```

Output:

```text
five-moduli minima audit up to 25: checked=98280
  W0 all       best=49/100 at (2, 2, 2, 3, 5)
  W1 no 2      best=7423/12600 at (3, 3, 4, 5, 7)
  W2 <= one 2  best=1087/2100 at (2, 3, 3, 5, 7)
2-friend lemma audit up to 3000: checked=10282, PASS
peel inequality audit up to 16: checked=58140, PASS
assembly constants:
  eps1 = 1123/12600
  eps2 = 37/2100
  eps1 + eps2 - 2/75 = 1009/12600
RESULT: PASS
```

This is an exact audit of the boxed finite kernels and algebra in
`sextuple_density_notes.md`; it is not a proof of the retirement argument that
reduces the minima to the finite box.

## Reproduce everything

```bash
python verify_exhaustive.py 15 3 200      # R1 exhaustive (PASS, 0 violations)
python counterexample_search.py           # R2–R4 (worst 1.999; disproof of typo version)
python verify_min3_triples.py             # R7 exact min-3 certificate (superseded by R9)
python verify_triples_min_leq.py 20       # R8 bounded-triple certificate (superseded by R9)
python attack_triples.py                  # R9 full verification of Theorem 9 (PASS)
python sweep_criterion.py 40 40           # R10 criterion sweep (PASS)
cargo run --release --manifest-path fastcheck/Cargo.toml -- selftest
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quad-cert 150 3000000
python audit_quadruple_charge.py 80
cargo run --release --manifest-path fastcheck/Cargo.toml -- quints 35 80 --uncovered
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quint-cert 100 3000000 60
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-density 120 --gcd1 --top 15
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-density 150 --gcd1 --residual --top 20
cargo run --release --manifest-path fastcheck/Cargo.toml -- density 300,400,450,499,500
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-separator 80 138 --uncovered
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-separator 80 138 --uncovered --middle
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-separator 200 33 --cover
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-separator 200 1 --cover
cargo run --release --manifest-path fastcheck/Cargo.toml -- quint-separator 150 33 --cover --top 20
cargo run --release --manifest-path fastcheck/Cargo.toml -- tower 76,114,153,171,285
cargo run --release --manifest-path fastcheck/Cargo.toml -- tower 40,60,81,90,150
cargo run --release --manifest-path fastcheck/Cargo.toml -- tower 28,42,57,63,105
python audit_sext_density_lemma.py --bound 25 --friend-limit 3000 --peel-bound 16
python audit_quint_density_lemma.py --brute 50
python audit_scaled_quint_families.py
```
