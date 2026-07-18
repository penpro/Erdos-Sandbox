# Quintuple charge notes for Erdos #488

Status: `CONDITIONAL-LEMMA` / `BROKEN-CLOSING-CONDITION` / `LEAD`.

This note records the first size-5 lesson after the primitive-quadruple audit.
It does not prove #488 for primitive quintuples. It isolates one symbolic regime
and records the first obstruction to extending the size-4 proof naively.

## Setup

Let

```text
P = {a,b,c,d,e},        a < b < c < d < e,
S = sum_{p in P} 1/p.
```

For `x in P`, use the same charge as before:

```text
X_x(n) = floor(n/x) - sum_{y in P, y != x} floor(n/lcm(x,y)).
```

Call `x` good if

```text
sum_{y != x} gcd(x,y)/y < 1.
```

Then `X_x(n) >= 1` for every good `x` and every `n >= max(P)`.

For five sets, exact inclusion-exclusion gives

```text
B = s - P2 + T3 - T4 + T5.
```

As usual,

```text
2s > nS + s - 5.
```

Thus it is enough to prove

```text
H5 := s - 2P2 + 2T3 - 2T4 + 2T5 >= 5.
```

## Proposition: three good charges suffice

If a primitive quintuple has at least three good elements, then

```text
2B(n) > nS        for all n >= max(P),
```

and hence #488 holds for that primitive quintuple by the union bound.

Proof sketch. Let `G` be three good elements and `H0=P\G` the remaining two.
The good charges contribute at least `3`. Group the other two:

```text
Y = sum_{h in H0} X_h + 2T3 - 2T4 + 2T5.
```

For a number `k`, let `p` be the number of grouped elements dividing `k`, and
`q` the number of good elements dividing `k`. The pointwise weight in `Y` is

```text
p - (p*q + 2*C(p,2)) + 2*C(p+q,3) - 2*C(p+q,4) + 2*C(p+q,5).
```

For `p=1,2` and `q=0,1,2,3`, the table is:

```text
p=1: 1, 0, 1, 4
p=2: 0, 0, 4, 6
```

All entries are nonnegative. The two grouped generators themselves contribute
`1` each by primitivity and `n>=max(P)`, so `Y>=2`. Therefore `H5>=3+2=5`,
which gives `2B(n)>nS`.

## The naive closing condition is false

The size-4 theorem closed because every primitive quadruple has at least two
good charges. The analogous size-5 statement is false.

Small witnesses with only two good charges:

```text
{2,3,5,7,11}
{3,4,10,14,22}
```

The second witness is primitive, has no `2`, and is not reciprocal-sparse:

```text
charge sums:
3  -> 719/1540
4  -> 886/1155
10 -> 493/462
14 -> 371/330
22 -> 247/210
```

It is nevertheless safe for #488 by exact certificate:

```text
alpha = 53/97 at x=97
beta  = 7/11 at x=22
beta/alpha = 679/583
union-bound separator S < 2B(n)/n: true
```

## Reconnaissance

Exact symbolic/certificate sweep:

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
union-bound separator PASS: 950
```

After peeling the scaled-family audits, the worst remaining residual certificate
is

```text
{40,48,60,72,90}
alpha = 15/269 at x=269
beta  = 7/96 at x=96
beta/alpha = 1883/1440
```

The formerly worst residual layer is a scaled copy of the base residual

```text
Q = {4,6,10,14,15}.
```

For `tQ`, the observed certificate has

```text
alpha = 15/(40t-1),   beta = 1/(2t),
beta/alpha = (40t-1)/(30t) -> 4/3.
```

This family is far from sharp for #488, but it is a good model for why the
naive good-charge count fails: `Q` and its scalings have only one good charge.

### Scaled residual family certificate

Let

```text
Q = {4,6,10,14,15},       Q_t = tQ.
```

For every integer `t>=1`, the ordering-free ratio for `Q_t` is certified by

```text
alpha_t = 15/(40t-1),     beta_t = 1/(2t),
beta_t/alpha_t = (40t-1)/(30t) < 4/3.
```

Reason. Since `B_{Q_t}(x)=B_Q(floor(x/t))`, write `x=tq+r` with
`0<=r<t`. The range `x>=15t` is exactly `q>=15`. The upper bound follows from
the base certificate for `Q`,

```text
B_Q(q)/q <= 1/2        for all q>=15,
```

because

```text
B_{Q_t}(x)/x = B_Q(q)/(tq+r) <= B_Q(q)/(tq) <= 1/(2t).
```

For the lower bound, the exact base certificate gives `B_Q(q)/q >= 5/13` for
`q>=39`, hence

```text
B_Q(q)/(tq+r) >= B_Q(q)/(tq+t-1) >= 15/(40t-1).
```

The remaining finite range `15<=q<39` is checked by the table condition

```text
B_Q(q)*(40t-1) >= 15*(tq+t-1).
```

Equivalently,

```text
t*(40B_Q(q)-15q-15) + (15-B_Q(q)) >= 0,
```

and the two coefficients are nonnegative for every `15<=q<39`; direct
enumeration gives

```text
B_Q(15..38) =
7,8,8,9,9,10,10,10,10,11,11,11,11,12,12,13,13,14,14,14,14,15,15,15.
```

Thus the displayed `alpha_t,beta_t` prove #488 for the whole scaled residual
family `tQ`. The companion script `audit_scaled_quint_families.py` rechecks the
same claim by one-period integer inequalities:

```text
Q = {4,6,10,14,15}: PASS
  alpha=15/(40t-1), witness q=39
  beta=1/(2t), equality q=[16, 18, 20]
```

This is an internal structural lemma, not a novelty claim.

### Scaled `2,3,5,7,11` residual family

After separating the literal `2 in A` theorem, the most frequent residual class
through entries `<=100` is not an actual `2 in A` case. It is the scaled family

```text
R = {2,3,5,7,11},       R_t = tR,       t>=2.
```

For every integer `t>=2`, the same block argument gives the exact certificate

```text
alpha_t = 36/(48t-1),     beta_t = 11/(12t),
beta_t/alpha_t = 11(48t-1)/(432t) -> 11/9.
```

Here `B_{R_t}(x)=B_R(floor(x/t))`, and `x>=11t` means `q=floor(x/t)>=11`.
The beta bound is the finite-period inequality

```text
12 B_R(q) <= 11q        for all q>=11,
```

with equality at `q=12`. The alpha bound is

```text
B_R(q) / (t(q+1)-1) >= 36/(48t-1),
```

equivalently

```text
t*(48B_R(q)-36q-36) + (36-B_R(q)) >= 0.
```

The audit script checks these inequalities over one lcm period
(`lcm(R)=2310`, `B_R(2310)=1830`) and verifies the period increments are
positive:

```text
R = {2,3,5,7,11}: PASS
  alpha=36/(48t-1), witness q=47
  beta=11/(12t), equality q=[12]
  increments: alpha_slope=4680, alpha_tmin=7530, beta_gap=3450
```

### Generic scaled-family audit lemma

For a base set `A`, write `A_t=tA`. Suppose we propose

```text
alpha_t = a/(ct-1),      beta_t = b/(dt),      t>=t0.
```

Since `B_{A_t}(x)=B_A(floor(x/t))`, write `x=tq+r` with `0<=r<t`. The beta
bound follows from `d B_A(q) <= b q`. The alpha bound is equivalent to

```text
t*(c B_A(q) - a(q+1)) >= B_A(q)-a.
```

Both inequalities only need one lcm period once the corresponding period
increments are nonnegative. The script `audit_scaled_quint_families.py` checks:

- witness equalities for alpha and beta;
- the alpha slope and alpha-at-`t0` inequalities over one period;
- the beta inequality over one period;
- nonnegative period increments;
- the ordering-free limit condition `b c < 2 a d`.

For piecewise families, the same script also has a finite-`t` checker. It uses
the fixed-`t` period increment directly, so it can certify a small range even
when the all-`t` alpha slope would eventually fail.

### Additional scaled residual families

The following high-ratio residual layers are now exact-audited by that generic
one-period method, except AE, whose alpha witness changes after `t=8` and is
therefore audited in two pieces:

```text
T = {32,45,48,72,80}: PASS
  alpha=8/(128t-1), witness q=127
  beta=1/(12t), equality q=[96]
  increments: alpha_slope=1792, alpha_tmin=1688, beta_gap=192
U = {16,24,36,40,45}: PASS
  alpha=7/(64t-1), witness q=63
  beta=7/(48t), equality q=[48]
  increments: alpha_slope=592, alpha_tmin=504, beta_gap=816
V = {4,5,6,9,14}: PASS
  alpha=31/(63t-1), witness q=62
  beta=5/(8t), equality q=[16]
  increments: alpha_slope=3024, alpha_tmin=2356, beta_gap=956
W = {4,6,9,10,14}: PASS
  alpha=16/(40t-1), witness q=39
  beta=1/(2t), equality q=[14, 16, 18, 20]
  increments: alpha_slope=2080, alpha_tmin=1524, beta_gap=148
X = {12,20,30,45,50}: PASS
  alpha=18/(132t-1), witness q=131
  beta=9/(50t), equality q=[50]
  increments: alpha_slope=1752, alpha_tmin=1616, beta_gap=1300
Y = {2,3,5,7,13}: PASS
  alpha=36/(48t-1), witness q=47
  beta=7/(8t), equality q=[16]
  increments: alpha_slope=5112, alpha_tmin=8070, beta_gap=1878
Z = {2,3,5,11,13}: PASS
  alpha=37/(50t-1), witness q=49
  beta=7/(8t), equality q=[16]
  increments: alpha_slope=7770, alpha_tmin=12210, beta_gap=3390
AA = {2,3,7,11,13}: PASS
  alpha=23/(32t-1), witness q=31
  beta=7/(8t), equality q=[16]
  increments: alpha_slope=7974, alpha_tmin=11382, beta_gap=5514
AB = {4,6,7,9,15}: PASS
  alpha=29/(63t-1), witness q=62
  beta=4/(7t), equality q=[21]
  increments: alpha_slope=2772, alpha_tmin=2148, beta_gap=672
AC = {4,6,7,10,15}: PASS
  alpha=18/(40t-1), witness q=39
  beta=4/(7t), equality q=[21]
  increments: alpha_slope=600, alpha_tmin=396, beta_gap=252
AD = {4,6,9,10,15}: PASS
  alpha=16/(40t-1), witness q=39
  beta=1/(2t), equality q=[16, 18, 20]
  increments: alpha_slope=320, alpha_tmin=240, beta_gap=20
AE = {4,6,9,11,15}, small scales: PASS
  t=1..8
  alpha=33/(75t-1), witness q=74
  beta=17/(33t), equality q=[33]
  beta_gap_increment=3300
AE = {4,6,9,11,15}, large scales: PASS
  t>=9
  alpha=7/(16t-1), witness q=15
  beta=17/(33t), equality q=[33]
  increments: alpha_slope=860, alpha_tmin=6820, beta_gap=3300
AF = {4,6,9,13,15}: PASS
  alpha=10/(24t-1), witness q=23
  beta=1/(2t), equality q=[16, 18, 20, 28, 30, 32]
  increments: alpha_slope=2232, alpha_tmin=1164, beta_gap=204
AG = {4,6,9,14,15}: PASS
  alpha=25/(63t-1), witness q=62
  beta=1/(2t), equality q=[16, 18, 20]
  increments: alpha_slope=3024, alpha_tmin=2476, beta_gap=164
AH = {4,6,9,15,17}: PASS
  alpha=11/(27t-1), witness q=26
  beta=1/(2t), equality q=[18, 20]
  increments: alpha_slope=3168, alpha_tmin=1804, beta_gap=332
AI = {4,6,9,15,19}: PASS
  alpha=11/(27t-1), witness q=26
  beta=1/(2t), equality q=[20]
  increments: alpha_slope=3204, alpha_tmin=1692, beta_gap=396
AJ = {4,7,10,15,18}, small scales: PASS
  t=1..2
  alpha=53/(124t-1), witness q=123
  beta=11/(21t), equality q=[21]
  beta_gap_increment=2016
AJ = {4,7,10,15,18}, large scales: PASS
  t>=3
  alpha=17/(40t-1), witness q=39
  beta=11/(21t), equality q=[21]
  increments: alpha_slope=1140, alpha_tmin=2856, beta_gap=2016
AK = {8,10,12,15,18}, t=1: PASS
  alpha=28/(104t-1), witness q=103
  beta=7/(20t), equality q=[20]
  beta_gap_increment=440
AK = {8,10,12,15,18}, t>=2: PASS
  alpha=12/(45t-1), witness q=44
  beta=7/(20t), equality q=[20]
  increments: alpha_slope=360, alpha_tmin=616, beta_gap=440
AL = {8,12,15,18,20}, t=1: PASS
  alpha=17/(72t-1), witness q=71
  beta=3/(10t), equality q=[20]
  beta_gap_increment=160
AL = {8,12,15,18,20}, t>=2: PASS
  alpha=7/(30t-1), witness q=29
  beta=3/(10t), equality q=[20]
  increments: alpha_slope=240, alpha_tmin=388, beta_gap=160
AM = {2,3,5,7,17}: PASS
  alpha=36/(48t-1), beta=5/(6t), t>=2
AN = {2,3,5,7,19}: PASS
  alpha=36/(48t-1), beta=23/(28t), t>=2
AO = {3,4,10,14,22}: PASS
  alpha=53/(98t-1) for t=1; alpha=47/(87t-1) for 2<=t<=4;
  alpha=21/(39t-1) for t>=5; beta=7/(11t)
AP = {3,4,10,14,25}: PASS
  alpha=53/(98t-1) for t=1; alpha=47/(87t-1) for 2<=t<=4;
  alpha=21/(39t-1) for t>=5; beta=17/(28t)
AQ = {3,4,10,22,25}: PASS
  alpha=53/(99t-1), beta=17/(28t), t>=1
AR = {4,5,6,9,21}: PASS
  alpha=31/(63t-1), beta=4/(7t), t>=1
AS = {4,6,9,10,22}: PASS
  alpha=16/(40t-1), beta=15/(32t), t>=1
AT = {4,6,9,10,25}: PASS
  alpha=16/(40t-1), beta=15/(32t), t>=1
AU = {4,6,9,14,21}: PASS
  alpha=25/(63t-1), beta=10/(21t), t>=1
AV = {4,6,9,14,22}: PASS
  alpha=25/(63t-1), beta=15/(32t), t>=1
AW = {4,6,9,15,21}: PASS
  alpha=25/(63t-1), beta=10/(21t), t>=1
AX = {4,6,9,15,22}: PASS
  alpha=25/(63t-1), beta=15/(32t), t>=1
```

So thirty-three scaled residual families now have exact infinite-family
certificates.

Resolved red flag: the nearby class

```text
AE = {4,6,9,11,15}
```

matches the tempting formula `alpha=33/(75t-1), beta=17/(33t)` for the first few
scales, but the one-period audit rejects it: at `q=15`, `B_A(q)=7` gives a
negative alpha slope. The correct repair is the two-piece certificate above:
`alpha=33/(75t-1)` for `1<=t<=8`, then `alpha=7/(16t-1)` for `t>=9`, with the
same beta bound `17/(33t)`. Thus AE is no longer a residual family.

Bounded window search:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- quints 70 80 --uncovered
```

Output summary:

```text
primitive uncovered 5-sets tested: 4,707,003
worst ratio = 35574/18605 at {61,62,63,64,65}
counterexamples: none in window
```

The worst set is charge-positive, so it is already covered by the general
charge-positive theorem.

## Next target

Size 5 needs a structural separator beyond "count the good charges". Useful next
work:

- add a symbolic quint classifier separating charge-positive, reciprocal-sparse,
  literal `2 in A`, scaled-family, dense-half, and special shared-factor regimes;
- a search for minimal primitive quintuples where the union-bound separator
  `S < 2B(n)/n` fails, if any exist at size 5.
