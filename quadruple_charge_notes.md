# Quadruple charge notes for Erdős #488

Status: `PROVED` conditional lemma, `COMPUTED` support for the missing closing
condition, `OPEN` final arithmetic lemma.

This note continues the charge method from `triples_writeup.md` into primitive
quadruples. It does **not** solve #488 for all four-element primitive cores yet,
but it isolates a surprisingly small remaining obstacle.

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

## Remaining bottleneck

The conditional lemma would prove #488 for every primitive quadruple if we could
show:

```text
Every primitive quadruple has at least two good elements.
```

This closing statement is not proved yet.

One piece is easy:

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

Thus the real bottleneck is:

```text
In every primitive quadruple a<b<c<d, at least one of b,c,d is good.
```

Additional observations:

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
charges. This is evidence for the closing lemma above, not a proof.

## Next exact task

Prove or refute the now sharper statement:

```text
In every primitive quadruple a<b<c<d, at least one of b,c,d has
sum_{f != e} gcd(e,f)/f < 1.
```

If true, the proposition above proves #488 for all primitive cores of size `4`.
