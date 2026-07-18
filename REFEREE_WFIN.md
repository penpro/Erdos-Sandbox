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
original cutoff near `10^(10^7)`. The forced-merge audit below improves it again.

## Forced-merge audit

Section 9 of `cbfin_reduction_notes.md` is also `PROVED` after two repairs. The
original presentation had to stop as soon as the current component has size five;
otherwise it invoked cofactor transfer where no size-five ceiling exists. It also
estimated a range from sample chains instead of checking every chain.

Use the sharper entry bound `U=R-4` and seed the graph with edges
`gcd(d_i,d_j) >= d/4`. Every bad vertex is nonisolated, so the initial graph has
at most three components and only the patterns
`(5),(4,1),(3,2),(3,1,1),(2,2,1)`. If a component `C` of size `k` has a tree whose
edges satisfy `g_e >= d/Y_e`, tree propagation gives

```text
h_C >= d/Z_C,  Z_C = U^(k-2) product_e Y_e.
```

On every proper partition, either all bad vertices transfer and the size
`2,3,4` ceilings contradict the presence of three bad vertices, or a bad vertex
forces a cross edge of quality `Y_new=(5-k)Z_C`. Adding this bridge preserves a
tree and strictly merges two components. Thus there are at most two merges.

The uniform hand table of initial patterns and bridge targets has provisional
worst case `(3,1,1) -> (4,1) -> (5)` with `Z_full=4^9U^7`. A second hostile pass
uses information discarded by that table:

- in `(3,1,1)`, all triple vertices are globally bad, which forces
  `h_3>d/16` and improves the row to `4^9U^3`;
- in `(2,2,1)`, every bad pair vertex is below `3d/2`, improving the pair-pair
  path to `(3/2)(288U)^2`;
- in initial `(4,1)`, a bad bridge source is below
  `Wd`, where `W=2(R-3)/3`, improving that row to `4^6U^4W`.

The remaining uniform rows are already smaller. Thus the actual worst row is
initial `(4,1)`, and at `U=1107/7`, `W=2228/21`, one may take

```text
T = 4^6 (1107/7)^4 (2228/21)
  = 2.718029482335... * 10^14.
```

The complete inequalities and path table are in Section 9. This audit is a finite
symbolic case analysis, not a search claim. Section 11 improves the constant again.

## Source-owned tree refinement

Claude's subsequent `1.49 * 10^13` host-geometry claim used safe real
relaxations, but its alleged binding path omitted the source's own seed-edge
factor. For any component tree,

```text
h_C >= product_e gcd(e) / product_v d_v^(deg(v)-1).
```

In initial `(4,1)`, the bad vertex sourcing the final bridge owns an in-component
edge at least `d_s/4`; choose a spanning tree containing it. Normalizing
`d_v=x_vd`, the tree degree exponents sum to two, so with
`H=product_v x_v^(deg(v)-1) <= U^2`,

```text
h_4 >= d x_s/(4^3 H),
h_5 >= h_4^2/(x_s d) >= d/(4^6U^4).
```

This handles all star/path geometries at once. A separate audit of the old
pair-singleton route gives denominator `62208U`: after its first bridge the
triple gcd is greater than `d/72`; the two possible sources for the last bridge
give full gcds greater than `d/(62208U)` and `d/(5184U)`.

The resulting six-row table has initial `(4,1)` as its exact worst case. Thus

```text
T = 4^6(1107/7)^4
  = 6151066630557696/2401
  = 2.561876980657... * 10^12.
```

The claimed `1.49 * 10^13` number was a valid but weak overestimate, not a
counterexample or a failure of W-FIN. The stronger cutoff remains far beyond the
bank.

## Residual-specific cutoff

Section 12 of `cbfin_reduction_notes.md` uses the extra C-B hypothesis
`N/d <= 7/2`, which is not part of universal W-FIN. Normalized error bounds
cap the relevant good and bad hosts, source-owned tree edges cancel the remaining
large bad hosts, and a two-variable check handles the only shared-edge path.

The connected `(5)` row has a separate dichotomy. A bad-bad seed edge
puts an internal bad vertex in a tree and its owned edge cancels one host
factor, giving `4^4U^2`. With no bad-bad seed edge, the one-good graph is a
small good-center star; in the two-good graph, residual error gives
`max(c,u)<(R+4)/2=1163/14`. Thus the connected row is at most
`50337207904/343`.

The exact residual path table is

```text
(5)                         50337207904/343
(4,1)                       246688579584/343   [worst]
(3,2)                       11757191168/147
(3,1,1)                     56623104
(2,2,1), pair-pair          12441600
(2,2,1), pair-singleton     622080
```

Therefore the actual C-B residual has

```text
d <= 4^6(369/7)(404/7)^2
   = 246688579584/343
   = 7.192086868338... * 10^8.
```

This does not alter the universal Section 11 theorem and does not close size 5.
It improves the universal cutoff by a factor `3562.0773...`, but remains far
beyond the exact bank. The next constant attack is the shared `(4,1)` path or
a uniform certificate that avoids enumeration.

## Exact cofactor refinement

Section 12A retains the integer cofactor discarded by the preceding real
relaxation. In `(4,1)`, every bad vertex has an internal gcd
`q>(b-1/4)/3`, so the integer cofactor `b/q` is at most `3`; a shared strong
edge therefore has reduced endpoint cofactors exactly `{3,2}`. Bad pair
sources in `(3,2)` and `(2,2,1)` have the same cofactor ceiling.

A second safe observation handles repeated hosts in the connected row. For any
four-element antichain `Q` of total size `K`, separate its largest entry from
the other three. The elementary positive triple deficit and
`2 gcd(z,t)<=t` give

```text
K-2 sum_pair gcd(Q) > -K/2.
```

Applying this to the complement of any residual entry `x`, then using
`E<=7/2` and `x+K<=R`, gives

```text
x < (3R+7)/5 = 3454/35.
```

In the distinct-owner `(4,1)` path, the third bad vertex also has a strong
owned edge. It is automatically distinct from the first two, and the three
owned edges form a spanning tree regardless of which endpoint the third edge
chooses. Keeping that third gain reduces every distinct-owner geometry below
`941000`; the shared `{3,2}` end path is the remaining `(4,1)` maximum.
Re-running the six rows gives

```text
(5)                         3054109696/1225
(4,1)                       652683970881/314230
(3,2)                       91853056/49
(3,1,1)                     33554432/81
(2,2,1), pair-pair          1634904
(2,2,1), pair-singleton     112752
```

The new binding case is the connected bad-bad row. Therefore

```text
d < 4^4(3454/35)^2
  = 3054109696/1225
  = 2493150.772244... .
```

This supersedes the numerical residual table immediately above, not its logic.
The full derivation and the three-owner tree cases are in Section 12A of
`cbfin_reduction_notes.md`. The result is still not an enumerable
completion because it bounds the minimum dual entry, while four further dual
coordinates can range up to `(1135/7)d`.

## Remaining gap

`C-B-FIN` is now a theorem, not the open gate. Full size 5 still requires one
of the following:

1. reduce the effective cutoff to a range reachable by the exact Rust bank;
2. prove a uniform covering theorem for all residual configurations; or
3. replace enumeration with certificates for the remaining parameter families.

The census through dual bound 240 remains evidence only: 276 residuals, no
three-component residual, and no tower failure. It cannot bridge the effective
gap by saturation alone.
