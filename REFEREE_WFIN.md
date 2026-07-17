# Referee audit: W-FIN and the effective size-5 gap

Date: 2026-07-17

Verdict: `PROVED` at paper tier after two local corrections. The theorem proves
that the C-B residual is finite. It does **not** finish size 5, because the
resulting finite cutoff is far beyond the range of the current Rust bank.

## Statement audited

Let `D` be a five-element divisibility antichain, let `d = min(D)`, and assume

```text
gcd(D) = 1,
sum(D) <= R d,
at least three i satisfy sum_{j != i} gcd(d_i,d_j) >= d_i.
```

For fixed `R`, the audited claim is that `d` is bounded by an explicit constant
depending only on `R`. For the #488 window, `R = 1135/7`.

## Hostile check of Claude's proof

The six load-bearing steps in `cbfin_reduction_notes.md` Section 7 survive:

1. Ten pairwise gcd ratios and eleven disjoint intervals give an empty gap.
   The endpoint conventions are correct.
2. A self-bad vertex has an incident gcd at least `d_i/4 >= d/4`, so it is
   nonisolated at the initial `d/5` threshold.
3. In the spanning-tree induction, both the current component gcd `H` and the
   attaching edge gcd `g` divide the old endpoint `d_u`. Thus
   `lcm(H,g) | d_u` and the propagated lower bound is valid.
4. Cofactor transfer uses an integer deficit. If a full self-bad vertex were
   good inside its component, its positive deficit would contribute at least
   one full factor `h_C`, contradicting the upper bound from light cross edges.
5. The size `2,3,4` self-bad ceilings need no gcd-one hypothesis. The size-four
   result is exactly the charge classification used in `Quad.lean`; scaling the
   dual set does not change its charges.
6. The component partition bounds then force either fewer than three self-bad
   vertices or one connected five-vertex component whose common gcd exceeds
   one when `d` is large.

The proof uses the window only to obtain a fixed entry ratio. It proves the
stronger qualitative statement for every fixed `R`.

## Corrections

- The displayed chain only gives `d_max <= (1135/7)d`; rounding that to
  `162d` is not valid by itself. The stated `162d` conclusion is nevertheless
  true because the other four entries are at least `d`, giving the stronger
  bound `d_max <= (R-4)d = (1107/7)d < 162d`.
- The displayed size-three ceiling had the wrong denominators. If `b,c` were
  self-bad, the correct sum is

```text
gcd(a,b)/b + gcd(a,c)/c + gcd(b,c)(1/b + 1/c) >= 2.
```

  Each of the first two terms is at most `1/2`, and, after naming `b<c`, the
  last is at most `(1+b/c)/2 < 1`; contradiction. The intended lemma remains
  valid.

## Shorter threshold proof

The eleven-rung gap ladder can be replaced by a three-level component argument.
Put

```text
U = R - 4,
epsilon_0 = 1/5,
epsilon_{j+1} = epsilon_j^3 / U^2,
```

and let `G_j` join a pair when its gcd is greater than `epsilon_j d`.

At least three vertices are nonisolated in `G_0`, so `G_0` has at most three
components. Compare the component partitions of `G_0,G_1,G_2`:

- if `G_0` and `G_1` have the same components, take `J=0`;
- otherwise, if `G_1` and `G_2` have the same components, take `J=1`;
- otherwise two strict merges have occurred, so `G_2` is connected; take `J=2`.

In either stable case, every cross-component gcd is at most
`epsilon_{J+1}d`. A component of size `k` has common gcd

```text
h_C > epsilon_J^(k-1) d / U^(k-2).
```

For `k=2,3,4`, this is respectively greater than
`3 epsilon_{J+1}d`, `2 epsilon_{J+1}d`, and
`epsilon_{J+1}d`. Cofactor transfer and the size `2,3,4` ceilings therefore
contradict the existence of three self-bad vertices. Hence the selected graph
must be connected. It follows that

```text
gcd(D) > epsilon_J^4 d / U^3 >= epsilon_2^4 d / U^3.
```

Since `gcd(D)=1`, one may take

```text
T = U^3 / epsilon_2^4 = 125^12 U^35.
```

For `R=1135/7`, `log10(T) = 102.1296...`. This is a large improvement over the
original cutoff near `10^(10^7)`, but it is still computationally useless.

## Remaining gap

`C-B-FIN` is now a theorem, not the open gate. Full size 5 still requires one
of the following:

1. reduce the effective cutoff to a range reachable by the exact Rust bank;
2. prove a uniform covering theorem for all residual configurations; or
3. replace enumeration with certificates for the remaining parameter families.

The census through dual bound 240 remains evidence only: 276 residuals, no
three-component residual, and no tower failure. It cannot bridge the effective
gap by saturation alone.
