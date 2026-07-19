# Proof attempt — Erdős #488

Notation. `A ⊂ ℤ_{≥1}` finite, `a* = max A`. `B = {k≥1 : a|k for some a∈A}`,
`B(x) = |B∩[1,x]|`. `C = ℤ_{≥1}∖B` (non-multiples), `C(x)=x−B(x)`.
Target **(★)**: for all `m>n≥a*`, `n·B(m) < 2·m·B(n)` (equivalently `B(m)/m < 2B(n)/n`).

**Current-status notice (2026-07-18).** This file preserves the early proof path
and is not the current frontier summary. Primitive-core size `≤4` is now proved
locally and formalized sorry-free in `lean/ep488`. For size 5, the density
inequality is proved, and W-FIN now proves that the C-B residual is finite.
The universal W-FIN cutoff is below `2.562 * 10^12`; the residual inequality
`CRIT <= 7/2` plus exact bad-edge cofactors sharpens the actual C-B cutoff to
below `2.494 * 10^6`. SPREAD proves the full finite-`n` separator for
`max/min >= 7`; the remaining open class is the compact residual box
`min < 3054109696/1225`, `max/min < 7`, `max < 17452056`, still beyond the checked
bank. OUTSIDE-DONOR and the pair-component argument give a finite-block
two-scale form. Claude's v3 exact slot-matrix certificate now passes the full
canonical 906-shape three-bad inventory (`869` vacuous, no zero or short
families); Codex repaired the earlier incomplete 69-file run by generating and
self-checking `clustercheck/shapes906.csv`. This is `COMPUTED` and still needs a
hostile v3 soundness audit. Five-bad residuals are excluded by the proved
minimum-good lemma. For four bads, the necessary-filter enumeration is complete
through normalized minimum `300`, yields 174 shapes (empirically ending at
`40`), and `shape4` certifies all 174. The sole compact-sector gap is now a
proof that no eligible four-bad shape occurs above the searched range; Section
23.7 reduces it to a connected bound `≤1512` plus a finite `(2,2)` box, but its
announced executable leaves are not yet implemented. Full size 5 remains open.
The false G3 min-bound is retracted. See `REFEREE_WFIN.md`,
Sections 22-24 of `cbfin_reduction_notes.md`,
`quintuple_density_notes.md`, and `adversary_collab_chat.md` before relying
on the older status paragraphs below.

## §1. Normalization

- **Quantifiers.** `∀` finite `A`; `∀` integers `m>n≥a*`. Constant `2` absolute.
- **Universe.** Positive integers; `B` is a union of the arithmetic progressions
  `aℤ_{≥1}` (`a∈A`); it is periodic mod `L=lcm(A)`.
- **Degenerate `1∈A`.** Then `B=ℤ_{≥1}`, `B(x)=x`, and (★) reads `nm<2mn` ✔.
  Henceforth assume `min A ≥ 2`, so `1∈C` and `C(x)≥1`, `B(x)≤x−1` for all `x`.
- **Basic bounds.** For `n≥a*`: every `a∈A` satisfies `a≤a*≤n` and `a∈B`, so
  `B(n) ≥ |A| ≥ 1`. Also `B(n) ≥ ⌊n/a₀⌋` where `a₀=min A` (multiples of `a₀`).
- **Sharpness of the constant.** `A={a}`, `n=2a−1`, `m=2a`: `B(n)=1`, `B(m)=2`,
  so `B(m)/m ÷ B(n)/n = (1/a)/(1/(2a−1)) = 2−1/a → 2`. Hence `2` cannot be lowered.
  (This is Erdős's own witness, and it *only* works for the multiples reading —
  see `selected_problem.md` for how it resolves the source typo.)

## §2. The single-element case is sharp (COMPLETE, rigorous)

**Proposition 1.** If `A={a}` (`a≥2`) then for all `m>n≥a`,
`B(m)/m < (2−1/a)·B(n)/n`, and `2−1/a` is attained in the limit.

*Proof.* `B(x)=⌊x/a⌋`. Write `g(x)=⌊x/a⌋/x`. Writing `r = x mod a ∈ {0,…,a−1}`,
we have `⌊x/a⌋=(x−r)/a`, so `g(x) = 1/a − r/(a·x)`. For `x≥a`, `⌊x/a⌋≥1`. Thus:

- **Upper bound (peaks).** `g(x) ≤ 1/a` for all `x`, with equality iff `a|x`.
  So `sup_{x≥a} g = 1/a`.
- **Lower bound (valleys).** For `x≥a`, `⌊x/a⌋ ≥ 1` and the minimum of `g` occurs
  at `x=2a−1` (the smallest `x≥a` with `⌊x/a⌋=1` and largest such `x`):
  `g(2a−1)=1/(2a−1)`. For any `x≥a`, `g(x) = ⌊x/a⌋/x ≥ 1/(2a−1)`, because if
  `⌊x/a⌋=t` then `x ≤ (t+1)a−1` so `g(x) ≥ t/((t+1)a−1) ≥ 1/(2a−1)` (the map
  `t ↦ t/((t+1)a−1)` is increasing in `t≥1`).

Hence for `m>n≥a`: `g(m) ≤ 1/a` and `g(n) ≥ 1/(2a−1)`, so
`g(m)/g(n) ≤ (1/a)/(1/(2a−1)) = 2−1/a < 2`. ∎

This already proves (★) for `|A|=1` with the sharp constant, and identifies the
unique extremal family. ∎

## §3. Complement reformulation and the dense half (COMPLETE, rigorous)

**Lemma 2 (complement form).** (★) is equivalent to
`2·C(n)/n − C(m)/m < 1` for all `m>n≥a*`.

*Proof.* With `B(x)=x−C(x)`: `B(m)/m<2B(n)/n ⇔ 1−C(m)/m < 2−2C(n)/n ⇔
2C(n)/n − C(m)/m < 1`. ∎

**Theorem 3 (dense half).** If `B(n) ≥ n/2` (i.e. `C(n) ≤ n/2`), then (★) holds
for this `n` and every `m>n`.

*Proof.* `C(n)≤n/2 ⇒ 2C(n)/n ≤ 1`. Since `min A≥2`, `1∈C`, so `C(m)≥1` and
`C(m)/m ≥ 1/m > 0`. Therefore `2C(n)/n − C(m)/m ≤ 1 − 1/m < 1`; apply Lemma 2. ∎

**Corollary 4.** (★) holds whenever `B` has upper density `≥ 1/2` on `[1,n]`; in
particular it holds for **all** `n` at which `B(n)≥n/2`. The only outstanding case
is the *sparse valley* case `B(n) < n/2`.

**Corollary 5 (`2∈A`).** If `2∈A`, (★) holds.
[PUBLIC: MalekZ proved this in the #488 thread, post 5163, 31 Mar 2026, by a
different route — do not claim. Clean proof kept for the record, replacing an
earlier sketchy version.]

*Proof.* If `n` is even, `B(n) ≥ n/2` (multiples of 2), so Theorem 3 applies.
If `n=2`, `B(2)=1=n/2`, Theorem 3 again. Let `n ≥ 3` be odd. If `C(n) ≤ n/2`,
Theorem 3 applies. Otherwise `C(n) > n/2`; but `B(n) ≥ ⌊n/2⌋ = (n−1)/2` gives
`C(n) ≤ (n+1)/2`, so `C(n) = (n+1)/2` exactly — i.e. *no odd number `≤ n` lies
in `B`*. Any odd `a∈A` would itself be an odd member of `B` with `a ≤ n`; hence
every element of `A` is even, so `B ⊆ 2ℤ` and `C(m) ≥ ⌈m/2⌉ ≥ m/2` for **all**
`m`. Then `2C(n)/n − C(m)/m ≤ (n+1)/n − 1/2 = 1/2 + 1/n ≤ 1/2 + 1/3 < 1`,
and Lemma 2 concludes. ∎

## Section 3A. Reciprocal-sparse primitive cores (PARTIAL RESULT; thin novelty)

[PRIORITY NOTE, 2026-07-07 Claude audit: the proof below is CONFIRMED correct,
but (i) it is a two-line corollary of Chojecki's public, Lean-verified
Lemma 6.3/Prop 5.1 (single-time union-bound criterion, 20 Mar 2026) combined
with the count `B_P(n) ≥ ⌊n/a⌋+1`; (ii) its `|A|=2` instance is Will Blair's
public post 6864 (06 Jun 2026); (iii) Theorem 3 above is Chojecki's Prop 6.1
(Lean-verified). Any write-up must cite both. See adversary_collab_chat.md.
Citation nit: the `|P|=1` branch defers to Proposition 1, which assumes
`a ≥ 2`; if `1 ∈ A` then `P = {1}` and the §1 degenerate case applies instead.]

Given a finite set `A`, let `P(A)` be its primitive core: the elements of `A` not
divisible by any smaller element of `A`. Then `B_A = B_{P(A)}` and
`max P(A) <= max A`, so proving the inequality for `P(A)` proves it for `A` in
the original range `n >= max A`.

**Theorem 6 (reciprocal-sparse primitive core).** Let `P=P(A)`, let
`a=min P`, and suppose

```text
sum_{d in P} 1/d <= 2/a.
```

Then #488 holds for `A`: for all integers `m>n>=max(A)`,

```text
B_A(m)/m < 2 B_A(n)/n.
```

*Proof.* Since `B_A=B_P`, work with `P`. If `P={a}`, this is Proposition 1.
Assume `|P|>=2`. Since `P` is primitive, no element of `P\{a}` is divisible by
`a`. For every `n>=max(A)>=max(P)`, all elements of `P\{a}` are present by time
`n`, and at least one of them contributes a counted integer not already counted
among the multiples of `a`. Hence

```text
B_P(n) >= floor(n/a) + 1 > n/a.
```

On the other hand, for every `m`,

```text
B_P(m) <= sum_{d in P} floor(m/d)
       <= m * sum_{d in P} 1/d
       <= 2m/a.
```

Therefore

```text
B_P(m)/m <= 2/a < 2 B_P(n)/n,
```

which is exactly the desired strict inequality. QED.

**Consequences.**

- This recovers the two-element case: if `P={a,b}` with `a<b`, then
  `1/a+1/b<2/a`.
- It covers every finite set whose primitive core has reciprocal mass at most
  twice the reciprocal of its least element.
- A small coverage sweep showed this lemma covers 2898/5035 sets with
  `A subset {2,...,20}`, `|A|<=4`; 49065/92170 sets with
  `A subset {2,...,40}`, `|A|<=4`; and 2476171/5495791 sets with
  `A subset {2,...,60}`, `|A|<=5`.
- The first uncovered primitive examples are `{2,3,5}` and `{3,4,5}`. The
  former is already handled by the public `2 in A` argument; the latter is
  handled in the next section.

## Section 3B. Primitive triples with least element 3 (NEW PARTIAL RESULT)

**Theorem 7.** #488 holds for every finite set whose primitive core is a
three-element set of the form `{3,b,c}`.

*Proof.* Let `P={3,b,c}` be primitive with `3<b<c`. If

```text
1/3 + 1/b + 1/c <= 2/3,
```

then Theorem 6 applies. Thus assume

```text
1/b + 1/c > 1/3.      (1)
```

Since `b>=4`, if `b>=6` then `1/b+1/c < 2/b <= 1/3`, contradicting (1).
Hence `b=4` or `b=5`.

If `b=4`, then (1) gives `1/c>1/12`, so `c<12`. Primitivity excludes multiples
of `3` and `4`, leaving

```text
{3,4,5}, {3,4,7}, {3,4,10}, {3,4,11}.
```

If `b=5`, then (1) gives `1/c>2/15`, so `c<15/2`. Primitivity excludes `c=6`,
leaving only

```text
{3,5,7}.
```

It remains to check these five exceptional triples. For each, the counting
function is periodic modulo `L=lcm(P)`: if `D=B_P(L)`, then

```text
B_P(Lq+r) = Dq + f(r),      0 <= r < L.
```

The exact finite certificate `verify_min3_triples.py` proves the following
global bounds for all `x>=max(P)`:

| P | L | D | lower alpha | upper beta | beta/alpha |
|---|---:|---:|---:|---:|---:|
| `{3,4,5}` | 60 | 36 | `13/23` | `7/10` | `161/130` |
| `{3,4,7}` | 84 | 48 | `7/13` | `2/3` | `26/21` |
| `{3,4,10}` | 60 | 32 | `1/2` | `3/5` | `6/5` |
| `{3,4,11}` | 132 | 72 | `1/2` | `13/22` | `13/11` |
| `{3,5,7}` | 105 | 57 | `1/2` | `3/5` | `6/5` |

In every row, `beta < 2 alpha`. Therefore for all `m>n>=max(P)`,

```text
B_P(m)/m <= beta < 2 alpha <= 2 B_P(n)/n.
```

This proves #488 for the five exceptional triples, and hence for every primitive
triple with least element `3`. QED.

## Section 3C. Machine-checked primitive triples with least element at most 20

**Theorem 8 (finite exact certificate).** #488 holds for every finite set whose
primitive core is a three-element set `{a,b,c}` with `a<=20`.

*Proof structure.* Let `P={a,b,c}` be primitive, `a<b<c`.

If

```text
1/b + 1/c <= 1/a,
```

then Theorem 6 applies.

It remains to check the reciprocal-heavy triples

```text
1/b + 1/c > 1/a.
```

For each fixed `a`, this is a finite set because it implies `b<2a` and
`c < ab/(b-a)`. The exact verifier `verify_triples_min_leq.py` enumerates these
triples for `3<=a<=20`.

For each enumerated triple, it computes exact rationals `alpha,beta` such that

```text
alpha <= B_P(x)/x <= beta        for all x >= c,
```

using the periodic identity

```text
B_P(Lq+r) = Dq + f(r),            L=lcm(a,b,c).
```

For fixed residue `r`, the ratio `(Dq+f(r))/(Lq+r)` is monotone in `q`, so the
global extrema occur at the first allowed `q` or at the limiting density `D/L`.
The script checks all residues in exact rational arithmetic and verifies
`beta < 2 alpha` for every reciprocal-heavy triple with `a<=20`.

The run

```text
python verify_triples_min_leq.py 20
```

checked 6944 reciprocal-heavy primitive triples and returned `RESULT: PASS`.
The worst certified ratio was attained by `P={19,20,21}`:

```text
alpha = 3/37 at x=37,
beta  = 54/361 at x=361,
beta/alpha = 666/361 < 2.
```

This proves the theorem, conditional only on the finite exact certificate.

**Interpretation.** The worst cases up to `a=20` are consecutive triples
`{a,a+1,a+2}`. This strongly suggests the next non-computational target:
prove #488 for all consecutive primitive triples.

[AUDIT NOTE, 2026-07-07 Claude: (1) certificate logic and script CONFIRMED
sound (q_min/r=0 handling, asserted slope conditions, exact-rational
strictness at `beta < 2*alpha`); (2) the five-triple completeness is CONFIRMED
by hand enumeration (b=4 → c∈{5,7,10,11}; b=5 → c=7; b≥7 → none); (3) the
periodicity-certificate METHOD is public (MalekZ posts 5089/5101), and the
result is subsumed by Chojecki's claimed Cor 4.7 (all primitive cores of size
≤ 3, Lean modulo one `sorry`). Defensible framing: independent, sorry-free
verification of a subcase of Cor 4.7.]

## §4. The sparse case `B(n) < n/2` — core difficulty (OPEN; partial progress)

This is the only remaining case and it contains the extremal family (single
element `A={a}`, `n=2a−1`, where `B(n)=1<n/2`). The constant `2` is saturated only
here and only in the limit, so **no lossy bound can work** — a correct proof must
be tight to first order.

Reductions and observations (all rigorous):

1. Writing `g(x)=B(x)/x`, (★) for a fixed valley `n` says
   `g(n) > (1/2)·sup_{m>n} g(m)`. It therefore suffices to prove the
   ordering-free **(★★)**: `inf_{x≥a*} g(x) > (1/2)·sup_{x≥a*} g(x)`,
   which computation supports (worst observed ratio `1.999…`, always `<2`).

2. Let `δ = lim_{x→∞} g(x)` (natural density; exists — Davenport–Erdős — and
   equals `B(L)/L`). Taking `m→∞` along multiples shows a **necessary** condition:
   `g(n) ≥ δ/2` for every valley `n≥a*`. Equivalently `inf_{x≥a*} g ≥ δ/2`.
   For `A={a}` this is `1/(2a−1) > 1/(2a) = δ/2` — true with the minimal possible
   margin, which is exactly why the theorem is sharp.

3. The obstruction to a one-line proof: for a set of multiples the counting
   function is *irregular* near the origin — e.g. `B` can be strictly denser than
   `δ` on an initial/interior window (`A={2,3}`: `g(4)=3/4 > δ=2/3`), so
   `sup g > δ` in general. Thus one cannot prove (★★) by `sup g ≤ δ ≤ 2·inf g`;
   the surplus of `sup` over `δ` and the deficit of `inf` below `δ` must be shown
   to trade off. Concretely, (★★) is equivalent to
   `s − 2i < δ`, where `s = sup_{x≥a*}(B(x)−δx)/x ≥ 0` and
   `i = inf_{x≥a*}(B(x)−δx)/x ≤ 0`.

4. Failed clean lemmas (recorded so they are not re-tried):
   - `B(m) ≤ (m/n)B(n)` for the tail — **false** (`A={3},n=5,m=100`: `32>20`).
   - `n·B(m) ≤ (m+n)·B(n)` — **false** (`A={3},n=5,m=100`: `165>105`).
   - `B(2x) ≤ 2B(x)` for `x≥a*` — **false** (`A={3},x=5`: `B(10)=3>2`).
   - "`[1,n]` is the sparsest length-`n` window" — **false** (`A={2,3},n=4`:
     window `(4,8]` has 2 `< B(4)=3`); the initial window is typically *denser*.

**Status (updated 2026-07-07, post Theorem 9):** (★) is now PROVED for every
`A` whose primitive core has **at most 3 elements** — see `triples_writeup.md`
(Lemmas 1–5, Theorem 8: the charge decomposition gives `2B(n) > nS` for every
`n ≥ max P` in the uncovered zone `1/b+1/c > 1/a`; Theorem 6 covers the rest;
Corollary 8'/Theorem 9 conclude). This subsumes §2, Corollary 5, §3A and §3B
above (the five periodicity certificates are no longer needed). Novelty
caveat: the size-≤3 RESULT is publicly claimed (Chojecki Cor 4.7, Lean modulo
one `sorry`); our proof is an independent, elementary, sorry-free route — see
adversary_collab_chat.md before claiming anything.

**Open:** primitive cores with `|P| ≥ 4`. Warning from the audit: the per-n
criterion `2B(n) > nS` is FALSE in general (`A = {2p : p ≤ 100}`, 25 elements,
fails at every large n) even though (★) holds there via the shared-factor
mechanism (`B_{2A'}(x) = B_{A'}(⌊x/2⌋)`, so `sup g ≤ 1/2 < 2δ`). Expect ≥ 3
regimes for `|P| ≥ 4`: charge/union-bound, dense half, and scaling recursion.
§4.2–3 remain the correct frame for the general problem. See `final_report.md`
for the verdict and `computational_results.md` for the evidence.
