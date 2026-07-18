# Referee notes for the size-4 charge addendum

Status: `LOCAL-AUDIT-PASS`, not human-refereed and not literature-audited.

Target note: `quadruple_charge_notes.md` and
`writeup/erdos488_quadruples_addendum.tex`.

## Claim under audit

For every primitive quadruple `P={a,b,c,d}`, `a<b<c<d`, with
`S=sum_{e in P} 1/e`,

```text
2B(n) > nS        for every n >= d.
```

The union bound then gives `B(m)/m <= S < 2B(n)/n`, so #488 holds for every
finite set whose primitive core has size at most `4`.

## Audit result

I did not find a break in the proof. The three fragile steps survive the checks
below:

1. The two-good-charge proposition has the correct pointwise weights.
2. Under `b` bad, the five listed shapes for `(c/b,d/b)` are exhaustive.
3. In those five shapes, the displayed upper bounds for the charge of `c` are
   strict.

This upgrades my internal confidence, but it is still not a novelty claim. The
exact size-4 argument needs human review and a thread/literature audit before it
is described as new or publishable.

## Pointwise weight check

Let `G` be the two good generators and `H0` the two grouped generators. For a
number `k`, let `p` be the number of `H0` elements dividing `k`, and `q` the
number of `G` elements dividing `k`.

For

```text
Y = sum_{h in H0} X_h + 2T3 - 2T4,
```

the pointwise weight is

```text
p - (p*q + 2*C(p,2)) + 2*C(p+q,3) - 2*C(p+q,4).
```

For `p=1,2` and `q=0,1,2` this gives exactly

```text
p=1,q=0: 1
p=1,q=1: 0
p=1,q=2: 1
p=2,q=0: 0
p=2,q=1: 0
p=2,q=2: 2
```

All weights are nonnegative, and the two grouped generators themselves each
contribute the `p=1,q=0` weight.

## Bad-b shape check

If `b` is bad, define

```text
q = a/gcd(a,b),  u = c/gcd(b,c),  v = d/gcd(b,d).
```

Badness says `1/q + 1/u + 1/v >= 1`, with `q>=2` and `u,v>=3`. If `q>=3`,
then `u=v=3`, forcing `c=d=3b/2`, impossible. Hence `q=2` and
`1/u + 1/v >= 1/2`.

Enumerating reduced fractions `c/b=u/r`, `d/b=v/s` with `2<=r<u`,
`2<=s<v`, and `c/b<d/b` leaves exactly:

```text
(3/2,5/3), (3/2,5/2), (4/3,3/2), (5/4,3/2), (6/5,3/2).
```

This is also verified by `audit_quadruple_charge.py`.

## c-charge estimates

With `q=2`, write `b/a=w/2` with `w` odd. For each of the five shapes, the
term from `a` in `charge(c)` is bounded by the denominator of `(w/2)*(c/b)`;
if the denominator collapses to `1`, then `a|c`, which primitivity forbids.
The five displayed estimates are:

```text
1/4 + 1/2 + 1/10 < 1
1/4 + 1/2 + 1/5  < 1
1/3 + 1/3 + 1/9  < 1
1/8 + 1/4 + 1/6  < 1
1/5 + 1/5 + 1/5  < 1
```

They check exactly.

## Independent script

Run:

```text
python audit_quadruple_charge.py 80
```

The script checks:

- the pointwise `Y` weight table;
- the five-shape enumeration;
- the five `charge(c)` estimates;
- every primitive quadruple with entries at most the supplied bound.

The script is only a backstop. The proof is the written charge argument.

## Remaining risks

- Priority/literature status is unknown. Do not call this new yet.
- The proof is elementary enough to formalize, but no Lean formalization exists.
- The theorem is specifically size `4`; the per-`n` separator is already known
  to fail for larger primitive families.
