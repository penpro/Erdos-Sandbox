# Consecutive triples lead for Erdos #488

Status: `SUPERSEDED` (2026-07-07, Claude) — the general triple theorem in
`triples_writeup.md` (Theorem 9, charge decomposition) proves #488 for ALL
primitive triples, including every `{a, a+1, a+2}`: they satisfy
`1/(a+1) + 1/(a+2) > 1/a` for `a ≥ 3`, i.e. the uncovered zone, and fall to
Corollary 8'. The desired bound (L) below is exactly Theorem 8's
`2B(n) > nS` (in the equivalent form `B(n)/n > S/2`, slightly stronger than
`3/(2a−1)` at the valley), now proved with no case analysis. Nothing left to
do on this lead.

Original note (kept for the record):

Status: `PLAUSIBLE`, not proved yet.

Target family:

```text
P_a = {a, a+1, a+2},     a >= 4.
```

This appears to be the extremal primitive-triple family. In the exact certificate
for all primitive triples with least element at most `20`, the worst case was
`{19,20,21}` with ratio `666/361`.

## Clean reduction

Let

```text
B_a(x) = |{k <= x : a|k or (a+1)|k or (a+2)|k}|.
```

The union bound gives

```text
B_a(m)/m <= 1/a + 1/(a+1) + 1/(a+2).
```

A direct calculation gives

```text
6/(2a-1) - (1/a + 1/(a+1) + 1/(a+2))
= (9a^2 + 14a + 2) / (a(a+1)(a+2)(2a-1)) > 0.
```

Therefore #488 for `P_a` follows from the prefix lower bound

```text
B_a(n)/n >= 3/(2a-1)       for all n >= a+2.        (L)
```

Indeed, (L) would imply

```text
B_a(m)/m
<= 1/a + 1/(a+1) + 1/(a+2)
< 6/(2a-1)
<= 2 B_a(n)/n.
```

## Computational evidence

The lower bound (L) was checked for every `4 <= a <= 300` and every
`a+2 <= n <= 3a^2`; no failure occurred. The minimum is attained at
`n=2a-1`, with `B_a(2a-1)=3`, for the tested range.

Small exception:

- For `a=3`, the bound (L) with `3/(2a-1)=3/5` is false, but the triple
  `{3,4,5}` is already covered by the exact min-3 certificate.

## Possible proof route

Use the floor lower bound

```text
B_a(x) >= floor(x/a) + floor(x/(a+1)) + floor(x/(a+2))
          - floor(x/lcm(a,a+1))
          - floor(x/lcm(a,a+2))
          - floor(x/lcm(a+1,a+2)).
```

For large `x`, floor-error estimates appear to prove (L) once `x >= 6a`.
The remaining range `a+2 <= x < 6a` should be reducible to finitely many
symbolic interval checks based on the ordered list of multiples

```text
ja, j(a+1), j(a+2),     1 <= j <= 6.
```

This is the next best non-computational attack.

