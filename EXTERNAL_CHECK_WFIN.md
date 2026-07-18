# External check package: W-FIN (paste into ChatGPT / any strong model)

Purpose: independent hostile review of a proof both internal reviewers (Claude,
Codex) have accepted. Framed neutrally and self-contained — no project context
needed, to avoid leading the reviewer. Paste everything between the lines.

---

I have an elementary number theory proof I want you to referee HOSTILELY. For
Tasks 1–5, do not search the internet. Try to BREAK it: find a counterexample,
a gap, an invalid step, or an off-by-one. Only if you genuinely cannot break it,
say so. Please check every step independently — do not take my word for any
sub-claim. Task 6 is a separate literature check and requires browsing; if you
cannot browse primary sources, report it as NOT CHECKED rather than guessing.

**Definitions.** Let `D = {d_1 < d_2 < d_3 < d_4 < d_5}` be five distinct
integers `≥ 2` forming a *divisibility antichain* (no element divides another),
with `gcd(D) = 1`. Call element `i` **self-bad** if
`Σ_{j≠i} gcd(d_i, d_j) ≥ d_i`. Fix a constant `R > 5` and assume the **ratio
condition** `d_1 + … + d_5 ≤ R·d_1`.

**Claim (W-FIN).** For every fixed `R` there is an explicit constant `T(R)` such
that: if `D` satisfies all of the above AND at least THREE elements are
self-bad, then `d_1 ≤ T(R)`. (I.e. there are only finitely many such `D`.)

**Proof.**

*Step 0 (ceilings).* (a) In any antichain, `gcd(d_i,d_j)` is a proper divisor of
both, hence `≤ min(d_i,d_j)/2`. (b) A 2-element antichain has no self-bad
element (its single gcd is `≤ d/2 < d`). (c) A 3-element antichain has at most
ONE self-bad element: if any two elements were self-bad, call those two `b<c`
and call the remaining element `a` (with no assumed order between `a` and
`b,c`). Divide `b`'s inequality by `b` and `c`'s by `c` and add:
`gcd(a,b)/b + gcd(a,c)/c + gcd(b,c)·(1/b + 1/c) ≥ 2`; but the left side is
`≤ 1/2 + 1/2 + (b/2)(1/b + 1/c) = 1 + (1 + b/c)/2 < 2` since `b < c`. (d) A
4-element antichain has at most TWO self-bad elements. [You may take (d) as
given — it is a separately machine-verified theorem — but sanity-check its
plausibility.]

*Step 1 (gap ladder).* Let `d := d_1`. Define `ε_0 := 1/5` and
`ε_{k+1} := ε_k⁴/(4R³)`. The ten values `gcd(d_i,d_j)/d` lie in `(0, R/2]`. The
eleven intervals `(ε_{k+1}, ε_k]`, `k = 0,…,10`, are disjoint, so at least one
interval `(ε_{J+1}, ε_J]` contains NONE of the ten values. Call a pair **heavy**
if `gcd(d_i,d_j) > ε_J·d`, **light** if `≤ ε_{J+1}·d`. Every pair is exactly one
of the two.

*Step 2.* If `i` is self-bad, its four gcds sum to `≥ d_i ≥ d`, so its largest
gcd is `≥ d/4 > d/5 = ε_0·d ≥ ε_J·d` — a heavy edge. So every self-bad vertex
lies in a connected component (of the heavy-pair graph) of size `≥ 2`.

*Step 3.* Let `C` be a heavy component, `|C| = k ≥ 2`. Claim:
`h_C := gcd(d_i : i ∈ C) ≥ ε_J⁴·d/R³ = 4·ε_{J+1}·d`. Take a spanning tree of
`C`'s heavy edges, and add vertices one at a time; maintain
`H = gcd(all d_i in the current subtree)`. Attaching new vertex `v` through
tree edge `{u, v}` (`u` already in the subtree), with `g := gcd(d_u, d_v) >
ε_J·d`: both `H` and `g` divide `d_u`, so `lcm(H, g) ∣ d_u`, so
`gcd(H, g) = H·g/lcm(H,g) ≥ H·g/d_u ≥ H·(ε_J·d)/(R·d) = H·ε_J/R`.
Since `g ∣ d_v`, `gcd(H, d_v) ≥ gcd(H, g)`. Starting from `H = (first edge's
g) > ε_J·d` and applying at most 3 attachments: `h_C ≥ ε_J·d·(ε_J/R)³`.

*Step 4.* Write `d_i = h_C·c_i` for `i ∈ C`. The `c_i` are distinct integers
`≥ 2` (if `c_i = 1` then `d_i = h_C` divides every element of `C`, contradicting
the antichain), form an antichain (`c_i ∣ c_j ⟺ d_i ∣ d_j`), and for EVERY pair
in `C` (heavy or not), `gcd(d_i, d_j) = h_C·gcd(c_i, c_j)`. Now let `i ∈ C` be
self-bad in `D`. Pairs from `i` to vertices outside `C` are light (a heavy edge
would have merged the components), and there are at most 3 of them, so:
`d_i ≤ Σ_{j≠i} gcd(d_i,d_j) ≤ h_C·Σ_{j∈C, j≠i} gcd(c_i,c_j) + 3·ε_{J+1}·d`.
Dividing by `h_C` and using `h_C ≥ 4·ε_{J+1}·d`:
`c_i − Σ_{j∈C,j≠i} gcd(c_i,c_j) ≤ 3·ε_{J+1}·d/h_C ≤ 3/4 < 1`, and since both sides
of `c_i ≤ Σ + 3/4` are integers apart from the `3/4`:
`c_i ≤ Σ_{j∈C,j≠i} gcd(c_i,c_j)`,
i.e. **`i` is self-bad within the cofactor antichain `{c_j : j ∈ C}`**.

*Step 5.* By Step 0, an antichain of size `k` has at most `0, 0, 1, 2` self-bad
elements for `k = 2, 3, 4` (sizes 1 trivially 0).

*Step 6.* If some heavy component has `k = 5`: `gcd(D) = h_C ≥ 4·ε_{11}·d > 1`
as soon as `d > T := 1/(4·ε_{11})` — contradicting `gcd(D) = 1`. Otherwise all
components have `k ≤ 4`, and the total number of self-bad elements is at most
the best over partitions of 5: `(4,1) → 2`, `(3,2) → 1`, `(3,1,1) → 1`,
`(2,2,1) → 0`, etc. — always `≤ 2 < 3`, contradicting three self-bad elements.
Hence `d ≤ T`; then every `d_i ≤ R·d`, so only finitely many integer quintuples
are possible. ∎

**Your tasks, in order:**
1. Try to construct a COUNTEREXAMPLE to the claim itself: an infinite family of
   gcd-1 antichain quintuples, entries within a fixed ratio, with ≥3 self-bad
   elements. (If you find one, the proof must be wrong — say where.)
2. Attack Step 1: is the pigeonhole airtight (10 values, 11 intervals,
   disjointness, endpoint conventions)? Can a gcd value evade classification?
3. Attack Step 3: is `lcm(H,g) ∣ d_u` justified at every attachment (H divides
   d_u because u is already in the subtree — check the induction order)? Is the
   final bound's exponent right (≤3 attachments after the first edge)?
4. Attack Step 4: the integrality trick (`3/4 < 1` forcing the integer
   inequality); the claim `gcd(d_i,d_j) = h_C·gcd(c_i,c_j)` for all pairs in C;
   the count of cross edges (≤3).
5. Attack Step 0(c): verify the 3-line k=3 ceiling computation independently.
6. Separately, now using primary-source browsing: does this statement or proof
   pattern already exist in the literature on primitive sequences / divisibility
   antichains (Erdős, Behrend, Anderson, Pillai)? Cite the closest precise theorem
   or say that no match was located. Do not infer novelty merely from no match.

---

Also useful as a second, separate prompt (paste after the first is resolved):

"Same setup. A stronger claim is proved by a colleague: the eleven-interval
ladder can be replaced by three graph levels: `U := R−4`, `ε_0 = 1/5`,
`ε_{j+1} = ε_j³/U²`; let graph `G_j` join pairs with `gcd > ε_j·d`. If `G_0` and
`G_1` have the same connected components take `J=0`; else if `G_1,G_2` match
take `J=1`; else two strict merges occurred and `G_2` is connected, take `J=2`.
In the stable cases every cross-component gcd is `≤ ε_{J+1}d`; the spanning-tree
bound gives `h_C > ε_J^{k−1}·d/U^{k−2}` for a size-k component, which exceeds
`(5−k)·ε_{J+1}·d` for `k = 2,3,4`. The final constant is `T = U³/ε_2⁴ =
125¹²·U³⁵`. Attack: (a) does partition stability at level J really imply all
cross-component pairs are `≤ ε_{J+1}d` — or could a pair be in the gap
`(ε_{J+1}, ε_J]`? (b) is `h_C > (5−k)·ε_{J+1}d` verified for each k with these
constants? (c) is the 'two merges ⟹ connected' step right when G_0 already has
≤3 components?"

A third, separate prompt audits the current strongest constant:

"Same five-antichain setup, now fix `R=1135/7`, put `d=min(D)`,
`U=R−4=1107/7`, and join pairs with gcd at least `d/4`. Every globally self-bad
vertex is nonisolated, so the initial component pattern is one of
`(5),(4,1),(3,2),(3,1,1),(2,2,1)`. Give each seed-tree edge quality `Y=4`.
For any component tree, edges `g_e≥d/Y_e` imply
`h_C≥d/Z_C`, `Z_C=U^(|C|−2)∏Y_e`.

At the TOP of each loop, stop if all five vertices are connected. On a proper
partition, if every global bad vertex has cross-component gcd sum `<h_C`, all
bad vertices transfer to the component cofactor antichains and the size-2/3/4
ceilings give at most two bad vertices, contradiction. Otherwise a bad vertex
in a size-k component forces a bridge with
`g≥h_C/(5−k)≥d/((5−k)Z_C)`. Add the bridge to the two old trees and merge.
There are at most two merges.

The uniform path table is then refined as follows. In initial `(3,1,1)`, all
triple vertices are bad; each has an internal edge `>d_i/4`, which gives
`h_3>d/16` and terminal denominator `4^9U^3`. In initial `(2,2,1)`, every bad
pair vertex has `d_i<3d/2`; the pair-pair-first path has terminal denominator
`(3/2)(288U)^2`, while the pair-singleton-first path keeps the safe uniform
bound `18U^4 4^5`. In initial `(4,1)`, the seed gives
`h_4≥d/(4^3U^2)` and any bad bridge source satisfies
`d_i<Wd`, `W=2(R−3)/3=2228/21`, so its terminal denominator is `4^6U^4W`.
The unchanged `(5)` and `(3,2)` bounds are `U^3 4^4` and `2U^4 4^5`.
The claimed maximum is therefore

`T=4^6(1107/7)^4(2228/21)=2.718029482335...×10^14`.

Referee this HOSTILELY without browsing: (a) verify the terminal check occurs
before transfer; (b) verify old tree-edge qualities survive merges; (c) enumerate
all initial patterns and bridge targets; (d) rederive each bad-rich inequality,
especially `h_3>d/16`, `d_i<3d/2`, and `d_i<Wd`; (e) compare all six bounds
exactly. Distinguish a flaw in this optimized constant from a flaw in W-FIN
itself. This still does NOT solve full size 5 or Erdős #488."

A fourth, separate prompt audits the newest source-owned-tree refinement:

"Use the same W-FIN setup and initial `d/4` component graph. A component spanning
tree `T` with edge gcds `q_e` is claimed to satisfy

`h_C >= product_e q_e / product_v d_v^(deg_T(v)-1)`.

For initial `(4,1)`, let `s` be the bad source of the final bridge and normalize
`d_v=x_vd`, `1<=x_v<=U=1107/7`. The initial singleton has all cross gcds `<d/4`.
Badness gives `s` an incident edge at least `x_sd/4`, so that edge lies inside
the four-component; choose a spanning tree containing it. With
`H=product_v x_v^(deg(v)-1)`, the degree exponents sum to two, hence `H<=U^2`.
The claim is

`h_4>=d x_s/(4^3H)` and
`h_5>=h_4^2/(x_sd)>=d/(4^6U^4)`.

The formerly coarse `(2,2,1)` pair-singleton path is also claimed to improve.
Every bad pair vertex is `<3d/2`. The first bridge gives a triple gcd `h_3>d/72`.
If the last bridge is sourced in that triple, `h_5>d/(62208U)`; if sourced in
the remaining pair, `h_5>d/(5184U)`. Together with the previously audited rows,
the exact maximum is

`T=4^6(1107/7)^4=2.561876980657...×10^12`.

Referee HOSTILELY without browsing: (a) prove or break the tree-product identity;
(b) verify the source-owned edge must be in the four-component and may be included
in a spanning tree chosen after the source is identified; (c) check the squared
source cancellation in the final bridge; (d) rederive both pair-singleton source
cases and all constants; (e) compare the six rows exactly. A flaw here would only
downgrade this optimized cutoff unless it also attacks Sections 7-9. This still
does NOT solve full size 5 or Erdős #488."
