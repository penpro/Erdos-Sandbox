# Quadruple charge notes for Erdős #488

Status: `AUDIT-PASS` (Codex-authored, Claude-audited 2026-07-07), pending human/
literature referee.

**Claude audit (2026-07-07).** Independently checked every step:
- Reduction `2B = s + H`, `s > nS − 4`, so `H ≥ 4 ⟹ 2B > nS`: correct.
- Prop 8″ (`good ⟹ X_e ≥ 1`): correct — `X_e = t − Σ⌊t/k⌋ ≥ t(1 − charge_e) > 0`
  for integer `X_e` (`t = ⌊n/e⌋ ≥ 1` when `n ≥ max P`).
- Two-good-charge proposition: the pointwise `Y_H` weights `p(2−p−q) +
  2·C(p+q,3) − 2·C(p+q,4)` were recomputed for all `p,q ∈ {0,1,2}` → `{1,0,1,
  0,0,2}`, all `≥ 0`; the two points `k = h₁,h₂` (each `p=1,q=0` by antichain,
  both `≤ d ≤ n`) give `Y_H ≥ 2`. Correct.
- Closing lemmas (a good; b bad ⟹ c good): verified EXHAUSTIVELY — 0 violations
  over all 8,486,881 primitive quadruples with entries ≤ 130 (integer charge
  test), matching Codex's `fastcheck sweep-quad-cert` (residual 0 to ≤ 150).
  `min #good = 2` over all quads, so the two-good bound is tight.
- Deficit classification (from the frenemy workflow): charge(e) > 1 iff cofactor
  multiset `{f/gcd(e,f)}` ∈ `{2,2,k}`(1/k), `{2,3,3}`(1/6), `{2,3,4}`(1/12),
  `{2,3,5}`(1/30). So `1/30` is the SMALLEST deficit; MAX is `1/2` (`{2,2,2}`).
  No triple-intersection structure is needed — the two-good-charge accounting
  (pairwise + the `2T₃−2T₄` correction) suffices.

Next: Lean formalization (Claude), building on the sorry-free `|core| ≤ 3`
development in `lean/ep488`.

This note continues the charge method from `triples_writeup.md` into primitive
quadruples. It proves the ordering-free #488 inequality for every primitive
quadruple, hence for every finite set whose primitive core has size at most `4`.

## Setup

Let

```text
P = {a,b,c,d},        a < b < c < d,
S = 1/a + 1/b + 1/c + 1/d.
```

For `e in P`, define the charge

```text
X_e(n) = floor(n/e) - sum_{f in P, f != e} floor(n/lcm(e,f)).
```

Call `e` good if

```text
sum_{f != e} gcd(e,f)/f < 1.          (G_e)
```

As in Proposition 8'' of `triples_writeup.md`, if `e` is good and
`n >= max(P)`, then `X_e(n) >= 1`.

For four sets, write

```text
s(n)  = sum_e floor(n/e)
P2(n) = sum_{e<f} floor(n/lcm(e,f))
T3(n) = sum_{e<f<g} floor(n/lcm(e,f,g))
T4(n) = floor(n/lcm(a,b,c,d)).
```

Exact inclusion-exclusion gives

```text
B(n) = s(n) - P2(n) + T3(n) - T4(n).
```

Also

```text
2s(n) > nS + s(n) - 4.
```

Therefore it is enough to prove

```text
H(n) := s(n) - 2P2(n) + 2T3(n) - 2T4(n) >= 4,
```

because then

```text
2B(n) = 2s(n) - 2P2(n) + 2T3(n) - 2T4(n)
      > nS + H(n) - 4
      >= nS.
```

The union bound `B(m)/m <= S` then gives the ordering-free #488 conclusion.

## Proposition: two good charges are enough

**Proposition.** Let `P={a,b,c,d}` be primitive. If at least two elements of `P`
are good, then

```text
2B(n) > nS        for all n >= d,
```

and hence `B(m)/m <= S < 2B(n)/n` for all `m >= 1`, `n >= d`.

**Proof.** Let `G` be two good elements and `H=P\G` the other two elements. For
`g in G`, the charge criterion gives `X_g(n) >= 1`, hence

```text
sum_{g in G} X_g(n) >= 2.             (1)
```

Now group the two remaining generators together:

```text
Y_H(n) := sum_{h in H} X_h(n) + 2T3(n) - 2T4(n).
```

We claim `Y_H(n) >= 2`.

Check this pointwise. For a number `k <= n`, let `p` be the number of elements of
`H` dividing `k`, and let `q` be the number of elements of `G` dividing `k`.
Only points with `p > 0` contribute to `Y_H`. Their weights are:

```text
p=1,q=0: 1
p=1,q=1: 0
p=1,q=2: 1
p=2,q=0: 0
p=2,q=1: 0
p=2,q=2: 2
```

So every contribution is nonnegative. Since `P` is primitive, each `h in H` is
divisible by itself and by no other element of `P`; also `h <= d <= n`. Thus the
two points `h` contribute `1` each, and `Y_H(n) >= 2`. Combining with (1),

```text
H(n) = sum_{g in G} X_g(n) + Y_H(n) >= 4.
```

The preceding setup then gives `2B(n)>nS`, and the union bound finishes. QED.

## Closing the charge condition

The conditional lemma proves #488 for every primitive quadruple once we know:

```text
Every primitive quadruple has at least two good elements.
```

This is true.

**Lemma.** In every primitive quadruple `a<b<c<d`, the least element `a` is good.

**Proof.** For each `y in {b,c,d}`, put `q_y = y/gcd(a,y)`. Primitivity gives
`q_y >= 3`, so the corresponding charge term is `1/q_y`. If `q_y=3`, then
`y=3g` with `g=gcd(a,y)` and `g|a`. Since `y>a`, we have `g>a/3`, so
`a/g < 3`. Also `a/g` is an integer greater than `1`; if it were `1`, then
`a|y`. Hence `a/g=2`, so `g=a/2` and `y=3a/2`. Thus at most one of
`b,c,d` can have `q_y=3`. The other two have `q_y>=4`, and therefore

```text
sum_{y in {b,c,d}} gcd(a,y)/y <= 1/3 + 1/4 + 1/4 < 1.
```

So `a` is good. QED.

It remains to show that at least one of `b,c` is good. In fact, `b` and `c`
cannot both be bad.

**Lemma.** In every primitive quadruple `a<b<c<d`, if `b` is bad then `c` is
good.

**Proof.** Write

```text
q = a/gcd(a,b),      u = c/gcd(b,c),      v = d/gcd(b,d).
```

Primitivity gives `q>=2` and `u,v>=3`. If `b` is bad, then

```text
1/q + 1/u + 1/v >= 1.                  (1)
```

If `q>=3`, then (1) forces `u=v=3`; otherwise the sum is at most
`1/3+1/3+1/4<1`. But `u=3` means `c/gcd(b,c)=3`; since
`b/gcd(b,c)` is an integer `<3` and not `1` (else `b|c`), it is `2`, so
`c=3b/2`. Similarly `v=3` gives `d=3b/2`, contradicting `c<d`. Therefore
`q=2`.

Thus `a/gcd(a,b)=2`; write `b/a=w/2` with `w` odd. From (1),

```text
1/u + 1/v >= 1/2.                      (2)
```

Let `c/b=u/r` and `d/b=v/s` be reduced fractions. Here
`2<=r<u`, `2<=s<v`, and the fractions are ordered `1<c/b<d/b`.
The possibilities allowed by (2) are only the following five:

```text
c/b = 3/2,  d/b = 5/3
c/b = 3/2,  d/b = 5/2
c/b = 4/3,  d/b = 3/2
c/b = 5/4,  d/b = 3/2
c/b = 6/5,  d/b = 3/2
```

Indeed, if neither `u` nor `v` is `3`, then (2) forces `u=v=4`, and
`u=4` forces the corresponding ratio to be `4/3`, giving `c=d=4b/3`, impossible.
So one of `u,v` is `3`. If `u=3`, then `c/b=3/2`, and (2) gives
`v<=6`; the order `d/b>3/2` leaves only `d/b=5/3` or `5/2`. If `v=3`, then
`d/b=3/2`, and the order `c/b<3/2` leaves only `c/b=4/3`, `5/4`, or `6/5`.

Now compute the charge of `c` in the five cases. The term from `a` uses
`b/a=w/2`; if the displayed numerator would reduce to `1`, then `a|c`, which is
forbidden by primitivity.

```text
c/b=3/2, d/b=5/3:
  charge(c) <= 1/4 + 1/2 + 1/10 < 1

c/b=3/2, d/b=5/2:
  charge(c) <= 1/4 + 1/2 + 1/5 < 1

c/b=4/3, d/b=3/2:
  charge(c) <= 1/3 + 1/3 + 1/9 < 1

c/b=5/4, d/b=3/2:
  charge(c) <= 1/8 + 1/4 + 1/6 < 1

c/b=6/5, d/b=3/2:
  charge(c) <= 1/5 + 1/5 + 1/5 < 1
```

Thus `c` is good in every case. QED.

Combining the two lemmas, every primitive quadruple has at least two good
elements: `a` is good, and either `b` is good or, if `b` is bad, `c` is good.

## Main theorem for size 4

**Theorem.** Let `A` be finite and let its primitive core have size at most `4`.
Then #488 holds for `A`. More strongly, for every primitive quadruple `P` with
reciprocal sum `S`,

```text
2B(n) > nS        for all n >= max(P),
B(m)/m <= S < 2B(n)/n        for all m>=1, n>=max(P).
```

**Proof.** Sizes `<=3` are Theorem 9 of `triples_writeup.md`. For a primitive
quadruple, the closing lemmas give at least two good charges, and the
two-good-charge proposition above gives `2B(n)>nS`; the union bound gives
`B(m)/m<=S`. Replacing a finite set by its primitive core preserves `B` and can
only lower the maximum element, so the original `n>=max(A)` range is covered.
QED.

## Examples and sharpness of the charge condition

1. Examples with two bad elements exist, e.g. `{12,20,30,45}` has bad charges
   at `30` and `45`, but still has good charges at `12` and `20`.
2. Examples with `b` bad also exist, e.g. `{20,30,45,50}` has charge sum
   `31/30` at `30`, while the other three elements are good. So the missing
   lemma cannot simply be "the two smallest are always good."

## Computation

The Rust workbench now treats the two-good condition as a symbolic regime:

```text
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quad-cert 150 3000000
```

Output summary:

```text
primitive quadruples with entries <= 150: 15,591,140
reciprocal-sparse theorem applies: 6,090,059
charge-positivity theorem applies: 15,577,302
two-good-charge rescue condition applies: 15,591,140
symbolically done by sparse or two-good-charge rescue: 15,591,140
residual after those regimes: 0
```

Thus every primitive quadruple with entries at most `150` has at least two good
charges, matching the theorem above.

An independent exact-audit script also checks the proof's fragile pieces:

```text
python audit_quadruple_charge.py 80
```

Output summary:

```text
pointwise Y weight table: PASS
five-shape enumeration under b bad: PASS
five c-charge estimates: PASS
primitive quadruples up to 80: 1037468
bounded quadruple audit: PASS
```

## Next exact task

Claude/human audit should still attack:

- the five-shape classification under `b` bad;
- the reduction of the `a`-term in the five `charge(c)` estimates;
- the pointwise weights in the two-good-charge proposition.

If it survives that external audit, turn the LaTeX addendum into a polished note
and ask Claude to formalize the arithmetic lemmas after the size-`<=3` Lean
project is settled.
