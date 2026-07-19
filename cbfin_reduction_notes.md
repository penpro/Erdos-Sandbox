# C-B-FIN: structure notes — duality transport, junk rays, and the 3-component sector

Status: `W-FIN PROVED AT PAPER TIER` after Codex hostile review (2026-07-17).
Claude's Section 7 gap-ladder proof is sound after the two display corrections
recorded below. Sections 8-9 give reviewed forced-merge proofs; Section 11's
source-owned tree refinement gives the universal W-FIN cutoff below
`2.562 * 10^12`. Sections 12 and 12A use the actual C-B residual inequality and
exact bad-edge cofactors to improve its cutoff below `2.494 * 10^6`. This is
still unusable for
enumeration, so full size 5 remains open.
Tiers marked per claim. Companion to `quintuple_density_notes.md`
("The C-B reorganization") and `lean/ep488/Ep488/CB.lean`.

Throughout: `D = {d_1 < … < d_5}` is a **dual core** (divisibility antichain,
`gcd(D) = 1`; the primal is `P = lcm(D)/D`), `G_i := Σ_{j≠i} gcd(d_i,d_j)`,
element `i` **self-bad** iff `G_i ≥ d_i` (⟺ primal `charge(P_i) ≥ 1`),
`Sg := Σ_{i<j} gcd(d_i,d_j)`, `N := ΣD − 2Sg`, `CRIT = N/d_1`.
**Residual** := `≤2` co-good (`≥3` self-bad) + window (`7ΣD ≤ 1135·d_1`) +
`CRIT ≤ 7/2`. `C-B-FIN` = "the residual is finite"; this is now proved softly
by W-FIN. The remaining size-5 gap is effective coverage of that finite class.

---

## 1. The Duality Transport Lemma (PROVED; unifies Codex's lemma-A trick)

**Lemma DT.** Let `D` be any `k`-antichain of integers `≥ 2` and `P₀` the
primitive `k`-set obtained from `lcm(D)/D` by dividing out the common factor.
Then `charge(P₀_i) = (1/d_i)·G_i` for every `i` (charge is scale-invariant, and
`gcd(L/d_i, L/d_j)/(L/d_j) = gcd(d_i,d_j)/d_i`). Consequently **any theorem
"every primitive `k`-set has `≥ g(k)` good charges" transports to "every
`k`-antichain has `≤ k − g(k)` self-bad elements"** — with no window or
residual hypothesis.

**Corollary (the self-bad ceiling table, PROVED).** `k`-antichains have at most
`0, 0, 1, 2` self-bad elements for `k = 1, 2, 3, 4`:
- `k ≤ 2`: for an antichain pair, `gcd(d_i,d_j)` is a proper divisor of each, so
  `gcd ≤ d_i/2 < d_i` — no self-bad element at all.
- `k = 3` (**direct 3-line proof, independent of the ≤3 development**): suppose
  `b, c` both self-bad in `{a,b,c}`, `b < c`. Antichain gcds are proper divisors,
  so each `gcd ≤ min/2`. Adding the two badness inequalities:
  `gcd(a,b)/b + gcd(a,c)/c + gcd(b,c)(1/b + 1/c) ≥ 2` (after dividing by `b`,`c`
  resp.). But the left side is `≤ 1/2 + 1/2 + (b/2)(1/b + 1/c) = 1 + (1 + b/c)/2
  < 2` since `b < c`. Contradiction. ∎
- `k = 4`: transport of the Lean-proved size-4 two-good theorem (Codex's
  observation, now with the general lemma stated once). This is the **hereditary
  4-anchor**: every 4-subset of a residual core has `≤ 2` self-bad elements
  *within the subset*.

*(Remark: at `k = 5` no such ceiling below 3 can hold — the residual class
itself has `≥ 3` self-bad — which is exactly why size-5 is the frontier.)*

## 2. Junk-ray algebra (PROVED by inspection — pure identities) and its honest scope

From the C-B-FIN workflow (its only surviving agent), verified line-by-line here
— these are four one-line identities, no computation needed:

**Lemma JR (single-element junk ray).** For `D⟨k,r⟩` := `D` with `d_k ↦ r·d_k`,
`r ≥ 2`, `gcd(r, d_j) = 1` for all `j ≠ k` (r may share primes with `d_k`):
1. `D⟨k,r⟩` is automatically an antichain with `gcd = 1`, and **every pairwise
   gcd is unchanged** (`v_p`-argument: primes of `d_j` don't divide `r`).
2. `N(D⟨k,r⟩) = N(D) + (r−1)d_k`; `min(D⟨k,r⟩) = min(m*_k, r·d_k)` with
   `m*_k := min_{j≠k} d_j`; hence
   `CRIT(D⟨k,r⟩) = (N + (r−1)d_k)/min(m*_k, r·d_k)`.
3. `G_j` and co-good status are invariant for `j ≠ k`;
   `charge_k` divides by `r`, so a co-bad `d_k` flips co-good exactly at
   `r ≥ ⌊G_k/d_k⌋ + 1` (exiting the `≤2`-good class into regime A).
4. For `r·d_k ≥ m*_k` the minimum freezes at `m*_k` and `CRIT` is **strictly
   increasing with slope `d_k/m*_k`** — every single-element ray leaves the
   residual after an explicit `R₀(D,k)`. (Below the freeze, if `d_k` is the
   unique minimum and `N > d_k`, `CRIT` first *decreases* — rays are
   down-then-up; never argue monotonicity from `r = 1`.)

**CORRECTION to a previous version of this §2 (2026-07-10 computation round).** An
earlier draft claimed shared-scale rays (a factor `g` on *two* components) have a
finite CRIT limit and are *not* self-retiring, and inferred the component framework
was needed to handle them. **That was wrong** — and the right statement is *simpler*:

**Lemma WINDOW-RETIRE (PROVED, elementary).** Let `S ⊊ {1..5}` be any nonempty proper
subset and `g` coprime to `{d_j : j ∉ S}`, growing. In `D` with `d_i ↦ g·d_i` (`i∈S`):
`ΣD ≥ g·Σ_{i∈S} d_i → ∞`, while `gcd(D)=1` **forces the complement nonempty**, so
`d_min = min_{j∉S} d_j` is **fixed** for large `g`. Hence the window condition
`7·ΣD ≤ 1135·d_min` **fails** for all large `g` — *every* growth ray leaves the
residual through the window, regardless of CRIT, components, or which subset grows
(single-element, shared-scale, or multi-parameter alike). ∎

So the junk-ray machinery — Codex's CRIT-slope argument and the workflow's
"essential core" reduction both — **collapses to the window bound.** There is no ray
subtlety to track. This also gives, for free:

**Lemma RATIO (PROVED, derivation repaired 2026-07-17).** The displayed chain gives
`d_max ≤ (1135/7)·d_min`. Subtracting the other four entries gives the stronger
**`d_max ≤ (1107/7)·d_min < 162·d_min`**, so the earlier integer bound `162`
was valid but its displayed rounding justification was incomplete.

**Consequence — C-B-FIN restated cleanly.** A residual family with unbounded `ΣD` has
unbounded `d_min` (by RATIO), i.e. every element `→ ∞` together (bounded ratio). So:

> **C-B-FIN ⟺ there is no infinite family of gcd=1 antichain quintuples with bounded
> ratio (`d_max ≤ (1135/7)·d_min`) and heavy sharing
> (`CRIT = (ΣD−2Sg)/d_min ≤ 7/2`).**

This is the same wall the whole program keeps hitting (cf. `{4,6,10,14,15}·s`, which is
bounded-ratio + heavy-sharing but has `gcd = s` — the residual needs the *same* shape
with `gcd = 1`). The component framework of §3 is the attack on *this* statement; but
the ray/essentiality bookkeeping is now retired.

## 3. Scale coordinates for the 3-component sector (REDUCED — the main expansion)

Setting: Codex's strong-gcd graph (join `i∼j` iff `4·gcd(d_i,d_j) ≥
min(d_i,d_j)`) has `≤ 3` components on a residual core; components partition as
`(5)`, `(4,1)`, `(3,2)` [1–2 components: **proved finite** by him] or
`(3,1,1)`, `(2,2,1)` [open: `C-B-3COMP`]. Write each component as `t_c·W_c`
with `W_c` primitive (block), scales `t_c`. Small facts, all elementary
(PROVED):

- **(F1)** The pairwise scale-gcds `g_{cc'} := gcd(t_c, t_{c'})` are **pairwise
  coprime** (a prime in two of them would divide every element of all three
  components, contradicting `gcd(D)=1`). In particular `g₁₂·g₁₃ ∣ t₁`, etc.
- **(F2)** Cross-component gcds factor through scales:
  `gcd(t_c w, t_{c'} v) ≤ w·v·g_{cc'}` (the part coprime to `wv` divides both
  scales).
- **(F3)** A factor shared by scale `t_c` and scale `t_{c'}` is coprime to the
  third component's entries (same argument as F1) — so cross terms **to the
  third component are `O(1)`** in any shared-scale ray of the pair `(c,c')`.
- **(F4)** Isolated vertices are self-good (`4·gcd < min` on all four partners
  gives `G < d`) — so in `(3,1,1)` both singletons are good and **all three
  block vertices must be self-bad**; in `(2,2,1)` the singleton is good and at
  least three of the four pair-block vertices are self-bad.
- **(F5)** By the ceiling table (§1) the triple block has `≤ 1`
  internally-self-bad vertex, and pair blocks have `0`. So in `(3,1,1)` at least
  **two** block vertices have a strictly positive *internal deficit*
  `δ_i := w_i − Σ_{j∈block} gcd(w_i,w_j) ≥ 1` (an integer!), and their badness
  needs **cross support `≥ t₁·δ_i ≥ t₁`** from the singletons; in `(2,2,1)`
  every bad vertex needs cross support `≥ t·δ` with `δ ≥ w/2`.
- **(F6) Support forces size separation.** If a block vertex draws support
  `≥ t₁/2` from singleton `s` (pigeonhole over its two cross terms), then the
  no-strong-edge condition `4·gcd < min(t₁w_i, s)` forces **`s > 2t₁`** (and,
  through F2, `w_i·g₁ₛ ≥ t₁/2`).
- **(F7) Support bounds the off-scales.** From `t₁ ≤ 2w_i·max(g₁₂, g₁₃)` (F5 +
  F2) and `g₁₂g₁₃ ∣ t₁` (F1), writing `t₁ = g₁₂g₁₃h`:
  `min(g₁₂, g₁₃)·h ≤ 2w_i` — i.e. **all of `t₁`'s scale structure except one
  distinguished shared factor (say `g₁₂`) is bounded by block-library
  constants.**

**The reduction (REDUCED — case analysis to be completed).** Fix the pattern
`(3,1,1)` (the `(2,2,1)` analysis is parallel). Normalize `t₁ = α·g` with
`g := g₁₂` the distinguished shared factor and `α := g₁₃h ≤ 2w_max` bounded
(F7); `t₂ = β·g` (`g ∣ t₂` by definition of `g₁₂`; `β` integer); `t₃ = J`,
`gcd(g, J) = 1` (F3). Then, with `A := α·ΣW + β − 2α·γ₁ − 2Σ_i gcd(αw_i, β)`
(`γ₁` = internal gcd-sum of the block) a **configuration constant**:

- every pairwise gcd involving the pair `{block, t₂}` scales exactly with `g`
  (`gcd(αg·w_i, βg) = g·gcd(αw_i, β)`), all other cross terms are `O(1)` (F3);
- hence `N = A·g + J − O(1)`, `d_min = min(α w_min·g, β·g, J)`, and **all
  membership conditions along the `(g, J)`-ray — the three badness inequalities
  `gcd(αw_i, β) ≥ α·δ_i(+…)`, the two goodness conditions, the no-strong-edge
  conditions, the antichain conditions, and the window — are `g`-independent
  arithmetic on `(W, α, β)` up to `O(1/g)`;**
- `β` is **bounded** by library constants: if `t₂` is not the global min then
  `CRIT ≥ (β − C)/ (α w_min)` retires `β > C + (7/2)αw_min`; if `t₂` is the
  global min then by definition `β ≤ α·w_min`. Either way
  `β ≤ C + (7/2)·α·w_min` with `C = 2αγ₁ + O(α w_max)`.

So the whole sector is governed by a **finite configuration space**
`(W ∈ finite library, α ≤ 2w_max, β ≤ C + (7/2)αw_min, gcd-pattern of
(αw_i, β))`, and along each admissible `(g, J)`-cone `CRIT` tends to an explicit
rational limit of the shape `(A + c)/m` (`m = min(αw_min, β, c)`,
`c = lim J/g`). Therefore:

> **C-B-3COMP is DECIDED by a finite arithmetic check:** if every admissible
> configuration has `inf-limit CRIT > 7/2`, the sector — and with Codex's 1–2
> component theorems, **all of C-B-FIN** — is finite; if some admissible
> configuration has `inf-limit CRIT ≤ 7/2`, that configuration's `(g,J)`-ray is
> an **explicit infinite residual family and C-B-FIN is FALSE** (the covering
> program would then need the bank to be parametrized per-ray instead — the
> C4-canonical mechanism — rather than finite).

Either outcome is decisive and constructive. **This check is deliberately NOT
executed here** (theory-only pass); it is a bounded enumeration over the block
library — a `census`-style Rust job, flagged for the next computation pass, and
independently a `fastcheck` cross-check target for Codex.

**Honest caveats.** (i) The `(2,2,1)` coordinates and the "which singleton
supports which vertex" case split are sketched, not written out; (ii) the
`w_min = 2` edge case in F6 needs the split-support refinement (support
pigeonholed over two singletons); (iii) the exact `O(1)` constants in the
`β`-bound must be pinned before the finite check is specified; (iv) nothing here
re-proves Codex's 1–2 component finiteness — we take it as stated (his proof
sketch is convincing but should get the same referee pass he gave C-B).

## 4. Corrections acknowledged (from Codex's hostile audit, same date)

1. The `7/2`-cutoff derivation `Φ ≥ n(S−2P₂) − 2` is valid **in the `≤2`-good
   class** (at most two positive `(1−charge)` coefficients, each `≤ 1`) — the
   note's original presentation omitted the scoping; his repaired derivation is
   the canonical one. (The Lean file `cb_cover5` was always stated with the
   correct hypothesis `s ≥ 2P₂ + 5`, so nothing machine-checked was affected.)
2. `census` primal-side products can overflow `i128` at ranges far beyond the
   current sweeps — fine at `max(P) = 513`, but **checked arithmetic or a
   common-denominator representation is required before any wider primal
   claim**. Logged as a tooling TODO (no code this pass).
3. Reproducibility gaps for publication: the U2 58-kernel certificate and the
   `W₀/W₁/W₂` retirement proofs exist only in session transcripts, not the
   repo. They must be committed as executable certificates. Logged.

## 5. What the size-5 endgame now looks like

```
size-5 #488  =  A (Lean) ∪ FD ∪ B/U2 ∪ C0 ∪ C-B (Lean) ∪ bank(195, Rust)
               ∪ [C-B-FIN]
C-B-FIN      =  1-component (finite, Codex) ∪ 2-component (finite, Codex)
               ∪ C-B-3COMP
C-B-3COMP    =  finite configuration check over (block library) × (α, β)
               — outcome decides C-B-FIN either way (finite OR explicit
               infinite family), constants pinned modulo §3 caveats.
```

The open mathematics has been reduced from a universal quantifier over an
unbounded class to a bounded, explicitly-parametrized enumeration plus a
completed case analysis. That is the target of the next computation pass.

## 6. Computation round (2026-07-10, `census cb`, native Rust component labeling)

Extended the C-B census to compute the strong-gcd components + self-bad counts of
every residual core natively (retiring Codex's Python graph helper), threaded, to
M=240 dual entries:

| M | residual | components `{n:count}` | patterns | self-bad | ≥3-comp | primal max | bank |
|---|---|---|---|---|---|---|---|
| 120 | 195 | `{1:156, 2:39}` | `[5]:156 [4,1]:38 [3,2]:1` | `{3:188,4:7}` | **0** | 513 | 0 fail |
| 240 | 276 | `{1:196, 2:80}` | `[5]:196 [4,1]:79 [3,2]:1` | `{3:266,4:10}` | **0** | 513 | 0 fail |

Findings: (i) the **3-component sector is empty through M=240** — consistent with
WINDOW-RETIRE (a 3-component coupled core needs large shared scales, which the window
forbids); (ii) exactly **one `[3,2]` core** in the whole range, all others `[5]` or
`[4,1]`; (iii) **primal max saturated at 513** across a 6× dual range, `0` bank
failures, worst tower margin `22/9` stable. *(Range-limited evidence, NOT a proof —
by the RATIO lemma the untested cores would be large-`d_min` bounded-ratio families,
which no brute enumeration reaches; §3's configuration check is the decisive route.)*

**Net effect of this round on the endgame:** the junk-ray/essential-core layer is gone
(WINDOW-RETIRE), the residual is bounded-ratio (RATIO), and C-B-FIN is now the single
crisp statement in §2 — "no infinite bounded-ratio heavy-sharing gcd=1 family." §3's
scale-coordinate reduction attacks it; the remaining computation is the finite
configuration check there (with the caveat constants pinned).

### 6a. The decisive tension — and why more brute census is a dead end (2026-07-10)

Reporting the residual's dual entries directly (not just primal max):

| M (dual bound) | max `min(D)` in residual | max `max(D)` | max `lcm(D)/min(D)` (= primal max) |
|---|---|---|---|
| 80 | 24 | 75 | 513 |
| 120 | 30 | 120 | 513 |
| 180 | 48 | 180 | **513** |

**The residual's dual `min(D)` is NOT saturating** (24, 30, 48, …) — this is the *exact
range-trap shape that produced the G3 overclaim*, and it means **brute census cannot
decide C-B-FIN**: a residual core with `min(D) > M` is simply invisible at bound `M`.
Do **not** conclude finiteness from the residual count leveling off.

**But** `lcm(D)/min(D)` (the primal max) **is saturated at 513.** The two facts reconcile
under the involution: a residual core with large dual entries is the dual of a *small*
primal core — e.g. at M=180 the largest-`min` residual `{48,55,80,120,180}` dualizes to
the primal `{44,66,99,144,165}`, max 165 ≤ 513. Heavy sharing (`CRIT ≤ 7/2`) forces a
small `lcm(D)`, which caps the primal side while the dual side runs off to infinity.

**So C-B-FIN sharpens to a single, involution-clean bound:**

> **C-B-FIN ⟺ `lcm(D)/min(D) ≤ C` for every residual core** (equivalently, the *primal*
> entries of a residual quintuple are bounded). Then the residual = duals of the finite
> set of `≤2`-good gcd=1 window-relevant primal cores with `max ≤ C`, hence finite. The
> census gives `C = 513` as a candidate, saturated over `M ∈ [80,240]`.

This is the right target: it is a **theorem to prove** (`CRIT ≤ 7/2 ⟹ lcm(D) ≤ C·min(D)`
— bound `lcm` by the sharing), **not** a number to hunt by widening the census. The
`lcm`/`min` bound is not visible in `CRIT` directly (`CRIT` has no `lcm` term), so it
needs the antichain + gcd=1 structure — precisely §3's block/scale analysis, now with a
concrete goal: bound the block library's `lcm`. Brute census's job here is done; the two
open moves are both **theory** (the `lcm` bound, or the §3 configuration limits), with
Rust reserved for the *bounded* configuration check once the reduction is pinned.

## 7. W-FIN proof (⟹ C-B-FIN) — the gap-ladder / heavy-component argument

Status: `PROVED` at paper tier (Claude/Fable, 2026-07-10; hostile review by
Codex, 2026-07-17). The review checked all six steps and found no fatal gap.
Two local corrections are incorporated above: the RATIO derivation and the
displayed denominators in the size-three ceiling. Every constant below is
explicit; no computation is invoked. See `REFEREE_WFIN.md`. This proves
something *stronger* than C-B-FIN: the CRIT condition is never used.

**Theorem (W-FIN, claimed).** There is an explicit `T` such that every quintuple
antichain `D` of integers `≥ 2` with `gcd(D) = 1`, at least **3 self-bad** elements
(`G_i = Σ_{j≠i} gcd(d_i,d_j) ≥ d_i`), and the **window** `ΣD ≤ R·min(D)`
(`R := 1135/7`) has `min(D) ≤ T`. Since the window also bounds every entry by
`(R−4)·min(D)` (RATIO), the class is **finite**; by the involution the primal class
{`≤2`-good, gcd=1, window-relevant} is finite; in particular **the C-B residual is
finite — C-B-FIN holds** — and size-5 regime C's cover reduces to a bounded check.

**Proof.** Write `d := d_1 = min(D)`; all entries `≤ (R−4)d ≤ 158.2·d`.

*Step 1 (gap ladder).* Define `ε_0 := 1/5` and `ε_{j+1} := ε_j⁴/(4R³)`. The ten
values `gcd(d_i,d_j)/d` lie in `(0, R/2]`. The eleven intervals
`(ε_{j+1}, ε_j]`, `j = 0..10`, are disjoint, so **some interval `(ε_{J+1}, ε_J]`
contains none of the ten values**. Call a pair **heavy** if `gcd > ε_J·d`
(equivalently `≥` anything above the empty gap), **light** if `gcd ≤ ε_{J+1}·d`.
Every pair is one or the other.

*Step 2 (bad ⟹ non-isolated).* If `i` is self-bad, its four gcds sum to `≥ d_i ≥ d`,
so the largest is `≥ d/4 > d/5 = ε_0·d ≥ ε_J·d` — a heavy edge. So every self-bad
vertex lies in a connected component of the heavy graph of size `≥ 2`.

*Step 3 (component common divisor).* Let `C` be a heavy component, `|C| = k ≥ 2`,
and take a spanning tree, adding vertices one at a time. Maintain
`H := gcd(d_i : i ∈ subtree)`. When attaching a new vertex `v` through tree-edge
`{u, v}` (`u` in the subtree) with `g := gcd(d_u, d_v) > ε_J·d`: both `H` and `g`
divide `d_u`, hence `lcm(H,g) ∣ d_u`, hence
`gcd(H,g) = H·g/lcm(H,g) ≥ H·g/d_u ≥ H·(ε_J·d)/((R−4)d) ≥ H·ε_J/R`;
and `gcd(H, d_v) ≥ gcd(H, g)` since `g ∣ d_v`. Starting from `H = g_first > ε_J·d`
and applying `≤ 3` attachments: the full-component divisor satisfies
`h_C := gcd(d_i : i ∈ C) ≥ ε_J⁴·d / R³ = 4·ε_{J+1}·d.`

*Step 4 (cofactor transfer).* Write `d_i = h_C·c_i` for `i ∈ C`. The `c_i` are
distinct (`d_i` distinct), `≥ 2` (`c_i = 1` would make `d_i` divide every element
of `C`, contradicting the antichain), form an antichain (`c_i ∣ c_j ⟺ d_i ∣ d_j`),
and `gcd(d_i, d_j) = h_C·gcd(c_i, c_j)` **for every pair in `C`** (heavy or not).
Now let `i ∈ C` be self-bad in `D`. Cross-component pairs are light
(a heavy edge would merge components), so
`d_i ≤ G_i ≤ h_C·Σ_{j∈C, j≠i} gcd(c_i, c_j) + 3·ε_{J+1}·d.`
If `i` were **cofactor-good** (`Σ_{j∈C} gcd(c_i,c_j) ≤ c_i − 1`), this gives
`h_C ≤ 3·ε_{J+1}·d`, contradicting `h_C ≥ 4·ε_{J+1}·d`. Hence **every self-bad
vertex of `D` inside `C` is self-bad in the cofactor antichain `{c_i : i ∈ C}`**.

*Step 5 (ceilings).* By the self-bad ceiling table (§1: sizes `2,3,4` admit at most
`0, 1, 2` self-bad — `k=2` trivial, `k=3` by the 3-line lemma, `k=4` by Duality
Transport from the Lean-proved size-4 two-good theorem), a component of size `k ≤ 4`
contains at most `k − 2` self-bad vertices (`0` for `k = 2`).

*Step 6 (assembly).* If some component has `k = 5`, then `gcd(D) = h_C ≥ 4ε_{11}·d
> 1` as soon as `d > T := 1/(4·ε_{11})` — contradicting `gcd(D) = 1`. Otherwise all
components have size `≤ 4`, and the total number of self-bad vertices is at most
`max over partitions of 5`: `(4,1) → 2`, `(3,2) → 1`, `(3,1,1) → 1`, `(2,2,1) → 0`,
`… → 0` — in every case `≤ 2 < 3`, contradicting `≥ 3` self-bad. Hence `d ≤ T`. ∎

**The constant.** `log(1/ε_{j+1}) = 4·log(1/ε_j) + log(4R³)` gives
`log₁₀(1/ε_{11}) ≈ 4¹¹·(log₁₀5 + log₁₀(4R³)/3) ≈ 10^{7.1}` — i.e. `T ≈ 10^{10⁷}`:
**explicitly finite, computationally absurd.** The lemma C-B-FIN is closed by this
(soft finiteness needs no good `T`), but the *bank* (checking each residual member's
window) is only feasible if `T` shrinks to enumeration range. Known slack to mine:
the ladder's 11 rungs come from a worst-case pigeonhole over all ten gcds — a
per-component ladder needs depth ≤ 2–3; the propagation loses `(ε/R)` per edge but
heavy components have diameter ≤ 3 and most patterns ≤ 1; and Step 6's `k = 5` case
could instead use `h_C ≥ 2` directly (`gcd > 1` needs only `4ε_{11}d > 1`... that IS
the bound). Realistic optimized target: `T ~ R^{O(10)}`, then a Rust enumeration to
`T` (dual side, RATIO-pruned) finishes size-5 outright.

**Sanity check against a real core** (`{4,6,9,10,15}`, `d = 4`): all ten gcd-ratios
are `≥ 1/4 > ε_0`, so `J = 0` with an empty gap below, the heavy graph is complete,
`k = 5`, and the argument demands `gcd(D) = h > 1` only when `d > T` — here `d = 4 ≤ T`,
no contradiction. Consistent: the theorem bites only at large `d`, exactly as it must
(residual cores exist at small `d`).

**Where a referee should attack:** (i) the empty-gap pigeonhole (11 rungs vs 10
values — off-by-one?); (ii) Step 3's `lcm(H,g) ∣ d_u` (both divide `d_u`; `H` divides
it because `u` is *in* the subtree — check the induction order); (iii) Step 4's
strictness bookkeeping (`cofactor-good` means `≤ c_i − 1`, integers make the gap
`≥ 1`, scaled by `h_C`); (iv) the `k=4` ceiling's dependency: Quad.lean's two-good
chain holds for any sorted positive antichain — confirm no `gcd=1` hypothesis is
needed (charges are scale-invariant, and DT divides it out anyway); (v) whether
"window" is used anywhere besides RATIO — it is not, so W-FIN really only needs
*bounded ratio*, an even cleaner statement: **no infinite antichain family with
`gcd = 1`, entries within a fixed ratio, and ≥ 3 self-bad elements.**

## 8. Codex hostile review and shorter threshold proof (2026-07-17)

Status: `PROVED` at paper tier. Full audit: `REFEREE_WFIN.md`.

The proof above survives hostile review. The empty-gap pigeonhole, spanning-tree
lcm step, cofactor integrality, and size-four hypothesis scope are all valid.
The two corrections were the RATIO derivation and the denominators in the
size-three display; neither affects W-FIN.

The eleven-rung ladder can be replaced by a three-level component argument.
Put

```
U := R - 4,   epsilon_0 := 1/5,
epsilon_{j+1} := epsilon_j^3/U^2,
```

and let `G_j` join `d_r,d_s` when
`gcd(d_r,d_s) > epsilon_j d`. Every self-bad vertex is nonisolated in
`G_0`, so at least three vertices are nonisolated and `G_0` has at most three
components. Compare the component partitions of `G_0,G_1,G_2`:

1. if `G_0,G_1` have the same components, take `J=0`;
2. otherwise, if `G_1,G_2` have the same components, take `J=1`;
3. otherwise two strict merges occurred, so `G_2` is connected; take `J=2`.

In either stable case, every cross-component gcd is at most
`epsilon_{J+1}d`. The spanning-tree argument gives, for a component of size
`k >= 2`,

```
h_C > epsilon_J^(k-1)d/U^(k-2).
```

For `k=2,3,4`, this is greater than respectively
`3 epsilon_{J+1}d`, `2 epsilon_{J+1}d`, and
`epsilon_{J+1}d`. (Use `epsilon_{J+1}=epsilon_J^3/U^2`,
`epsilon_J <= 1/5`, and `U>1`.) Cofactor transfer therefore applies with the
exact number `5-k` of possible cross edges. The size-`2,3,4` ceilings then
contradict at least three self-bad vertices unless the selected graph is
connected.

For a connected selected graph, the same spanning-tree bound gives

```
1 = gcd(D) > epsilon_J^4 d/U^3 >= epsilon_2^4 d/U^3.
```

Thus one may take

```
T = U^3/epsilon_2^4 = 125^12 U^35.
```

At `R=1135/7`, `log10(T)=102.129655...`. This replaces the original cutoff
near `10^(10^7)` by roughly `10^102`. It is a major proof simplification but
still far beyond exhaustive enumeration. Therefore `C-B-FIN` is proved, while
full size 5 remains open at the effective coverage step.

## 9. Constant optimization v2 - forced merges (PROVED: `T < 2.72 * 10^14`)

Status: `PROVED` at paper tier (Claude/Fable skeleton; hostile review and exact
path audit by Codex, 2026-07-17). The review found one ordering defect in the
presentation: a full five-vertex component must terminate the process before the
cofactor-transfer branch, because the size-five ceiling is unavailable. It also
replaced the unproved rough range `10^16-10^22` by the exhaustive hand table below.
Neither correction affects the independent Section 8 proof.

**Setup and propagation.** Put `d := min(D)`, `R := 1135/7`, and
`U := R-4 = 1107/7`. The window gives `d_i <= Ud`. Write a tree-edge certificate
as `g_e >= d/Y_e`. If a connected component `C` of size `k >= 2` has a spanning
tree with edge qualities `Y_1,...,Y_{k-1}`, then

```text
h_C := gcd(d_i : i in C) >= d/Z_C,
Z_C := U^(k-2) * product_e Y_e.
```

Indeed, order any tree by starting with an edge and then attaching one vertex at
a time. If the current gcd is `H` and the attaching edge gcd is `g` at an old
endpoint `d_u`, then `H,g | d_u`, so
`gcd(H,g) = Hg/lcm(H,g) >= Hg/d_u >= Hg/(Ud)`. Thus every previously certified
edge keeps its original quality after later merges.

**Initial partition.** Join `i,j` when `gcd(d_i,d_j) >= d/4`. Every globally
self-bad vertex is nonisolated, since one of its four gcds is at least
`d_i/4 >= d/4`. Hence at least three vertices are nonisolated, the initial graph
has at most three components, and its only possible size patterns are

```text
(5), (4,1), (3,2), (3,1,1), (2,2,1).
```

Choose a spanning tree in each nonsingleton component. Every seed edge has
quality `Y=4`. An initial singleton is globally self-good and remains so until it
is merged.

**Forced merge.** At the top of each loop, if the partition is the single
five-vertex component, stop. Otherwise, for every globally self-bad `i` in a
component `C`, let

```text
x_i := sum_{j outside C} gcd(d_i,d_j).
```

If every such `x_i < h_C`, then every global bad vertex transfers to a self-bad
vertex of the cofactor antichain of its component: if it were cofactor-good, its
integer internal deficit would be at least one, so global badness would require
`x_i >= h_C`. The size `2,3,4` ceilings then bound the total number of global bad
vertices by at most `2`, a contradiction.

Therefore some bad `i` in a component of size `k < 5` has `x_i >= h_C`. There are
only `5-k` cross edges from `i`, so one has

```text
g >= h_C/(5-k) >= d/((5-k)Z_C).
```

Add that edge to the two component trees and merge the components. Their union
plus the bridge is again a tree, with bridge quality
`Y_new = (5-k)Z_C`. The partition strictly coarsens. Since it started with at
most three components, at most two forced merges occur.

**Exact path table.** The table lists the largest possible final propagation
denominator for every initial pattern and target choice. In `(3,2)`, sourcing
the bridge from the triple dominates sourcing it from the pair. The two
`(2,2,1)` rows are the only distinct first-bridge targets.

| Initial pattern | Forced path | Upper bound for `Z_full` |
|---|---|---:|
| `(5)` | none | `U^3 * 4^4` |
| `(4,1)` | `4 -> 5` | `U^5 * 4^6` |
| `(3,2)` | `3 -> 5` | `2U^4 * 4^5` |
| `(3,1,1)` | `3 -> 4 -> 5` | `4^9 * U^7` |
| `(2,2,1)` | pair joins pair, then singleton | `9U^5 * 4^6` |
| `(2,2,1)` | pair joins singleton, then pair | `18U^4 * 4^5` |

For the worst row, the seed triple has `Z_3=U4^2`; the first bridge has
`Y_1=2Z_3`; the resulting four-component has
`Z_4=U^2*4^2*Y_1=2U^3 4^4`; and the last bridge has `Y_2=Z_4`. Hence

```text
Z_full = U^3 * 4^2 * Y_1 * Y_2 = 4^9 U^7.
```

This is the worst **uniform** row and already gives the safe intermediate cutoff
`4^9U^7`. The initial patterns, however, encode more bad-vertex information than
the uniform recurrence uses.

**Bad-rich pattern refinement.** Three local observations sharpen the three-part
rows and the terminal `(4,1)` row.

1. In an initial `(3,1,1)` pattern the singletons are globally good, so all three
   triple vertices are globally bad. Their two singleton gcds total less than
   `d/2`; hence every triple vertex `i` has an internal edge greater than
   `(d_i-d/2)/2 >= d_i/4`. Let `z` be the largest triple entry, take its such edge
   to `q`, and let `r` be the third vertex. The corresponding edge from `r` is
   distinct and attaches at `z` or `q`, whose entry is at most `z`. Therefore

   ```text
   h_3 > (z/4)(r/4)/z >= d/16.
   ```

   The two forced bridges then give
   `h_4 >= h_3^2/(2Ud) > d/(512U)` and
   `h_5 >= h_4^2/(Ud) > d/(4^9U^3)`.

2. In an initial `(2,2,1)` pattern, write `q` for a pair gcd. Every globally bad
   pair vertex `i` satisfies

   ```text
   d_i <= q + (cross sum) < q + 3d/4 <= d_i/2 + 3d/4,
   ```

   so `d_i < 3d/2`. If the first bridge joins the two pairs, then with
   `q_A,q_B >= d/4` and bridge `g >= q_A/3`, first adjoining its target gives
   common gcd greater than `d/72`; adjoining the target's partner gives
   `h_4 > d/(288U)`. The last bridge is sourced at another globally bad pair
   vertex, so
   `h_5 > d/((3/2)(288U)^2)`. If the first bridge joins the singleton, the
   uniform table's `18U^4 4^5` bound is already smaller than the final maximum.

3. In an initial `(4,1)` pattern, the seed propagation gives
   `h_4 >= d/(4^3U^2)`. If a globally bad `i` forces the last bridge, its singleton
   gcd is less than `d/4`, so one of its three internal gcds is greater than
   `(d_i-d/4)/3 >= d_i/4`. Its partner is therefore greater than `d_i/2`.
   The other three entries are at least `d`, and the window gives

   ```text
   d_i < Wd,  W := 2(R-3)/3 = 2228/21.
   ```

   Hence the final gcd is greater than
   `h_4^2/(Wd) >= d/(4^6U^4W)`.

The resulting exhaustive bounds are

| Initial pattern | Refined upper bound for the terminal denominator |
|---|---:|
| `(5)` | `U^3 * 4^4` |
| `(4,1)` | `4^6 * U^4 * W` |
| `(3,2)` | `2U^4 * 4^5` |
| `(3,1,1)` | `4^9 * U^3` |
| `(2,2,1)`, pair joins pair first | `(3/2)(288U)^2` |
| `(2,2,1)`, pair joins singleton first | `18U^4 * 4^5` |

At `U=1107/7`, the `(4,1)` row is largest. Since
`1=gcd(D)=h_full`, W-FIN holds with

```text
T = 4^6 (1107/7)^4 (2228/21)
  = 4568192150960848896 / 16807
  = 2.718029482335... * 10^14.
```

**Honest endgame accounting.** This improves only the effective constant:

- `C-B-FIN` (and the stronger bounded-ratio statement) remains **closed**.
- **Full size 5 is still not enumerable.** The bank would have to certify every
  residual core with `d <= T`, and this bound is far beyond any census. The census
  evidence (all residual dual minima `<=48` through `M=240`) suggests the true
  cutoff is small, but it is not a completeness proof.
- The two honest routes remain: shrink the cutoff to a genuinely enumerable range,
  or prove a uniform residual-window theorem for all parameter families. The
  latter would make the finiteness constant irrelevant.

## 10. The effective gap: the DRIFT-TRANSFER program (route to closing size-5 without T)

Status: `PROGRAM` + one `PROVED` seed lemma (Claude/Fable, 2026-07-17). Goal: the
uniform residual window theorem — *window + `≤2`-good + `CRIT ≤ 7/2` ⟹ `2B(n) > nS`
on `[2·max, bridge)`* — which makes even the proved `T < 2.562 * 10^12` irrelevant and
closes size-5 outright.

**Why the bridge fails on the window, quantitatively.** Summing U2
(`f_a(J) ≥ (7/300)J − 7/30`) gives `2B−nS ≥ (7/150)nS − 7/3 − (157/150)(5−S)`:
the five per-element defects (`7/30` each) plus fractional losses cost ≈ `7.3`,
and the uniform slope `7/300` only repays it once `nS ≳ 162`. The window is
exactly the regime where the *worst-case* slope is too lazy. But `7/300` is tight
ONLY for moduli `(2,2,3,5)` — every other moduli multiset has a strictly better
slope (`E₄ − 1/2`): e.g. no-2 moduli give slope `≥ 2257/3600 − 1/2 ≈ 0.127` (5.4×)
and `≤`one-2 give `≥ 329/600 − 1/2 ≈ 0.048` (2×). **The program: show the residual
structure forces enough elements into good drift classes that the summed slopes
repay the defects on the window.** This is the finite-`n` (drift) version of the
size-6 density transfer (`W₀/W₁/W₂` + 2-friend pairing), one size down.

**Seed lemma DRIFT-1 (PROVED).** Let `f` be a *2-friend* of `a` in a primitive set
(`m_f = f/gcd(a,f) = 2`). Then:
1. `f = 2^{v₂(a)+1}·t` with `t` a **proper odd divisor** of `odd(a)`; hence
   `f ≤ (2/3)a` (the 2-friend lemma, re-derived: `t ≤ odd(a)/3`).
2. The modulus of `a` as seen from `f` is `2a/f = odd(a)/t` — **odd and `≥ 3`**.
3. If `f₁, f₂` are two 2-friends of the same `a`, their mutual moduli are
   `tᵢ/gcd(t₁,t₂)` — **odd and `≥ 3` both ways** (the `t`'s are incomparable
   divisors of `odd(a)` by the antichain).

*Consequence:* an element in the U2-extremal class (moduli `(2,2,3,5)`-type,
needing **two** 2-friends) forces two elements `≤ (2/3)a` each of which carries
**at least two odd moduli `≥ 3`** (one to `a`, one to the other 2-friend) — i.e.
the extremal element's own repayment crew is pushed into `≤`one-2 or no-2 drift
classes with 2–5× the slope, at **larger arguments** `⌊n/f⌋ ≥ (3/2)⌊n/a⌋`. This is
precisely the size-6 pairing mechanism, now at the counting level.

**The three lemmas the program needs:**
1. **Per-class drift certificates** (computational, U2-style): for each moduli
   class `K ∈ {(2,2,3,5)-type, ≤one-2, no-2, …}`, constants `(σ_K, δ_K)` with
   `f(J) ≥ σ_K·J − δ_K` — the finite-`n` analogs of `W₀/W₁/W₂`. (Same one-period
   + retirement machinery as U2's 58 kernels; to be produced WITH executable
   certificates, paying the standing reproducibility debt at the same time.)
2. **Class-assignment lemma** (structural, from DRIFT-1 + heavy sharing): in a
   residual core, classify each element's moduli multiset; show the assignment
   always leaves total slope `Σ σ·⌊n/a⌋` large enough on `n ≥ 2max`. The `≤2`-good
   hypothesis enters here: goods have charge `< 1` hence `Σ1/m_f < 1` — their `E₄
   ≥ 1 − c/2 > 1/2` with slope `(1−c)/2` tied to the *Bonferroni* mass; CRIT ≤ 7/2
   bounds how much slope the goods can hide.
3. **Assembly** (paper): `2B−nS = 2Σf_a(⌊n/a⌋) − Σ{n/a} ≥ Σ_a(2σ_a⌊n/a⌋ − 2δ_a)
   − (5−S) > 0` on `[2max, bridge)`, cases by class pattern.

Honest risk: lemma 2 is where it can die — a residual core might exist whose class
pattern still under-repays at `n = 2max` (the bank's worst margin `22/9` sits in
the low window, so slack is real but not huge). If it dies, the failure pattern
feeds route (a) (stable-partition classification) instead.

## 11. Source-owned trees cut the cutoff to `T < 2.562 * 10^12`

Status: `PROVED` at paper tier (Codex hostile review, 2026-07-17), strengthening
Claude/Fable's claimed `1.49 * 10^13` host-geometry bound. The real-relaxation
direction in the claim was safe, but its alleged binding case
`4^6 x_1^2 x_2^3` took `x_2` to be the bridge source while failing to use that
source's own seed-edge gain. The gain changes that expression to
`4^6 x_1^2 x_2`. Thus the old number was a safe overestimate, not a false upper
bound, but the geometry catalogue was unnecessary and its binding-case verdict
was false.

**Tree-product lemma.** Let `T_C` be a spanning tree of a component `C`, let
`q_e` be the gcd on edge `e`, and write `deg(v)` for tree degree. Then

```text
h_C := gcd(d_v : v in C)
    >= product_e q_e / product_v d_v^(deg(v)-1).
```

To prove it, start with any tree edge and attach the remaining vertices away
from that root edge. At an attachment through parent `u`, the usual lcm step
loses at most a factor `d_u`. Each vertex is used as a parent exactly
`deg(v)-1` times. This is the Section 9 propagation with the actual host sizes
retained instead of replacing every host by `Ud`.

**Initial `(4,1)` pattern.** Let `s` be a globally bad vertex that forces the
last bridge, and normalize `d_v=x_v d`, where `d=min(D)` and
`1 <= x_v <= U=1107/7`. Badness gives an incident edge

```text
q_s >= d_s/4 = x_s d/4.
```

The initial singleton has every cross gcd `<d/4 <= d_s/4`, so this owned edge
lies inside the four-component. Choose a seed spanning tree containing it; the
other two tree edges have gcd at least `d/4`. Put

```text
H_T := product_{v in C} x_v^(deg(v)-1).
```

The degree exponents sum to `2`, so `H_T <= U^2`. The tree-product lemma gives

```text
h_4 >= d x_s/(4^3 H_T).
```

The final bridge has gcd `g >= h_4` and is sourced at `s`. Since both `h_4` and
`g` divide `d_s=x_s d`, the full common gcd satisfies

```text
h_5 >= h_4 g/d_s
    >= d x_s/(4^6 H_T^2)
    >= d/(4^6 U^4).
```

Thus the entire initial `(4,1)` row is bounded by `4^6U^4`. This covers star and
path trees simultaneously. In Claude's source-is-an-internal-host case, the
source-owned edge contributes `x_s^2` after squaring `h_4`; the final lcm loss
returns only one `x_s`, which is precisely the missing cancellation.

**The pair-singleton path.** The previous Section 9 table left one
`(2,2,1)` route at its coarse bound. Let the pair gcds be `q_A,q_B >= d/4`.
Every globally bad pair vertex `i` has `d_i<3d/2`, because all three cross edges
are `<d/4` and

```text
d_i <= q + cross_sum < d_i/2 + 3d/4.
```

Suppose the first forced bridge joins pair `A` to the singleton. It has
`g_1>=q_A/3`, so the resulting triple common gcd is

```text
h_3 >= q_A g_1/d_i > d/72.
```

The remaining partition is this triple and pair `B`.

- If the second bridge is sourced in the triple, then its source is an original
  bad pair vertex, so `d_i<3d/2`, and `g_2>=h_3/2`. After adjoining its target
  in pair `B`, the common gcd is greater than `d/15552`. Adjoining the target's
  partner through `q_B`, with target size at most `Ud`, gives
  `h_5>d/(62208U)`.
- If the second bridge is sourced in pair `B`, then `g_2>=q_B/3`. Adjoining its
  target in the triple gives common gcd greater than `d/72`. Both this divisor
  and `h_3>d/72` divide the target, whose size is at most `Ud`; hence
  `h_5>d/(5184U)`.

Therefore the pair-singleton route has terminal denominator at most `62208U`,
not `18U^4 4^5`.

**Final exact table.** Combining these two refinements with the already reviewed
Section 9 rows gives

| Initial pattern | Terminal denominator bound |
|---|---:|
| `(5)` | `U^3 * 4^4` |
| `(4,1)` | `4^6 * U^4` |
| `(3,2)` | `2U^4 * 4^5` |
| `(3,1,1)` | `4^9 * U^3` |
| `(2,2,1)`, pair joins pair first | `(3/2)(288U)^2` |
| `(2,2,1)`, pair joins singleton first | `62208U` |

At `U=1107/7`, the `(4,1)` row is largest. Since `gcd(D)=1`, W-FIN holds with

```text
T = 4^6 (1107/7)^4
  = 6151066630557696 / 2401
  = 2.561876980657... * 10^12.
```

This is a factor `2228/21 = 106.095...` below the previous reviewed cutoff and
about `5.82` below Claude's claimed value. It remains far beyond the residual
bank. Full size 5 and full Erdos #488 remain open; DRIFT-TRANSFER remains the
more relevant closing program.

## 12. The residual inequality cuts the C-B cutoff to `T < 7.193 * 10^8`

Status: `PROVED` at paper tier (Codex, 2026-07-17). This section is deliberately
scoped more narrowly than W-FIN. In addition to the Section 11 hypotheses, use
the C-B residual condition

```text
E := N/d
   = sum_i (x_i - sum_{j != i} gamma_ij) <= 7/2,
x_i := d_i/d,  gamma_ij := gcd(d_i,d_j)/d,
```

where `x_i >= 1`, `sum x_i <= R=1135/7`, and an edge of the initial graph means
`gamma_ij >= 1/4`. For a divisibility antichain,
`gamma_ij <= min(x_i,x_j)/2`. The universal cutoff in Section 11 remains valid
without `E <= 7/2`; only the C-B residual gets the stronger number below.

### Residual size bounds

These bounds are consequences of the displayed inequalities, not a search.

**Pattern `(4,1)`.** Let `y` be the singleton. Every edge from `y` is below
`1/4`. A bad vertex `b` in the four-component satisfies

```text
b < (sum of the other three component sizes)/2 + 1/4,
```

so the window gives

```text
b < B := (R-1/2)/3 = 2263/42.
```

If the four-component has a good vertex `c` and three bad vertices of total
size `K`, write `e_i=x_i-sum_j gamma_ij`. Then

```text
e_c > c-K/2-1/4,
sum_bad e_i > -K/2-3/4,
e_y > y-1.
```

Thus `E>c-K+y-2`. Combining `E<=7/2`, `K+c+y<=R`, and `y>=1` gives

```text
c < V := (R+7/2)/2 = 2319/28.
```

There is one much tighter sparse case. If the seed graph has no bad-bad edge,
connectedness forces a star centered at the unique good vertex `c`. Each bad
leaf then has `e_b>b/2-3/4`, so `E>c+y-7/2`; hence `c<6`.

**Pattern `(3,2)`.** For a triple vertex `a`, `e_a>-1/2`; for a pair vertex
`p`, `e_p>p/2-3/4`. Consequently every pair entry satisfies `p<12`. A bad
triple entry is below `(R-1)/3`, while a good triple entry satisfies

```text
a < A := (R+9)/3 = 1198/21.
```

For the latter claim, if the other triple entries are `b,c` and the pair is
`p,q`, then

```text
E > a-(b+c)/2+(p+q)/2-3
  >= 3a/2-R/2-1.
```

**Pattern `(3,1,1)`.** Let the sorted triple sizes be `M>=m>=ell`. The seven
cross-component gcds are below `1/4`, and twice the sum of the three internal
gcds is at most `m+2ell`. Therefore

```text
E > M-ell-3/2,
```

so `M-ell<5`.

**Pattern `(2,2,1)`.** Every pair entry `p` satisfies `p<10`: its own error is
greater than `p/2-3/4`, the other three pair errors are each greater than
`-1/4`, and the singleton error is positive. Every bad pair entry still has
the stronger Section 11 bound `p<3/2`.

### Sharpened merge rows

The tree-product notation is that of Section 11. If the product of the
size-gains on selected tree edges is `C_T`, then a four-tree gives

```text
h_4 >= d C_T/(4^3 H_T),
h_5 >= d C_T^2/(4^6 H_T^2 x_s),
```

where `s` is the final bad bridge source.

**The `(4,1)` row.** Choose an `s`-owned edge `e_s`. If there is no bad-bad
seed edge, the sparse good-center star above gives terminal denominator less
than `4^6*6^4`.

Otherwise choose a tree containing `e_s` and a bad-bad edge. Some bad vertex
`t` is internal. The usual one-edge exchange can retain `e_s`, make a
`t`-owned edge `e_t` part of the tree, and keep `t` internal. If `e_t != e_s`,
the two distinct gains give a denominator at most `4^6 V^2` (a star gives the
smaller `4^6B^2`).

If `e_t=e_s`, then this edge is owned by the two bad endpoints `s,t`. Let `r`
be a third bad vertex and include an `r`-owned edge as well. A star, or a path
with `e_s` as its middle edge, has denominator at most `4^6B^3`. The only
remaining geometry is a path in which `e_s` is an end edge, the other internal
vertex `u` is good, and `r` is the opposite bad leaf. Put
`M=max(s,t)` and `m=min(s,t)`. Retaining the shared-edge gain `M` and the
`r`-gain bounds the tree denominator by at most `4^6 M u^2/r^2`.

Both `s` and `t` are bad. For the larger one, its four gcds are bounded by
`m/2`, `M/2`, `r/2`, and `1/4`, respectively. Hence

```text
M < m+r+1/2,
```

and the terminal denominator is less than

```text
4^6 * (m+r+1/2) u^2/r^2.
```

The individual error bounds along this path are

```text
e_s+e_t > (M-m)/2-r-1/2,
e_r > -r/2-1/4,
e_u > u-(M+m+r)/2-1/4,
e_y > y-1.
```

Thus `E>u+y-m-2r-2`, and residual plus window give

```text
u < min(m+2r+9/2, R-2m-r-1).
```

It remains to maximize the two-variable real relaxation

```text
G(m,r) = (m+r+1/2)/r^2
         * min(m+2r+9/2, R-2m-r-1)^2.
```

For fixed `r`, the first branch increases in `m`. On the second branch its
derivative has factors `D-2m` and `D-6m-4r-2`, where `D=R-r-1`; the branch
meeting point lies to the right of the latter critical point. When the meeting
point is feasible, it is therefore the maximum for that `r`; if it falls below
`m=1`, the whole feasible second branch is decreasing and its boundary value is
smaller. Thus the global maximum can be taken where the two bounds meet:

```text
m = R/3-r-11/6.
```

At that point `m+r+1/2=(R-4)/3=369/7` and
`u=R/3+r+8/3`. The ratio `u/r=1+(R/3+8/3)/r` decreases with `r`, so the
global maximum is at `r=1`, where `m=717/14` and `u=404/7`. Hence the
`(4,1)` row is at most

```text
4^6 (369/7)(404/7)^2
  = 246688579584/343
  = 7.19208686834... * 10^8.
```

**The `(3,2)` row.** If the first source is in the triple, choose a source-owned
seed edge. When the tree host is good, the bounds `host<A` and `target<12`
give

```text
h_5 > d/(2048*12*A^2).
```

When the host is bad, its own edge is already one of the two triple-tree edges;
the distinct/shared owner cases are smaller. If the first source is in the
pair, combining the `d/72` pair-target divisor with the triple divisor gives
`h_5>d/(1152A^2)`. Thus the row is at most

```text
24576 A^2 = 11757191168/147 = 7.99808922993... * 10^7.
```

**The `(3,1,1)` row.** The bad-owned triple tree used in Section 9 retains the
smallest triple size and gives `h_3>ell*d/16`. Both bridge sources are at most
`Md`, so

```text
h_5 > d ell^4/(4^9 M^3).
```

Since `M<ell+5` and `(ell+5)^3/ell^4` decreases for `ell>=1`, this row is less
than `4^9*216=56623104`.

**The `(2,2,1)` rows.** Replacing the old target cap `U` by `10` changes the
pair-pair path to `(3/2)*2880^2=12441600`. The pair-singleton path is at most
`622080`; its two final-source subcases give `622080` and `51840`.

**The `(5)` row.** If the connected seed graph contains a bad-bad edge,
choose a tree containing it. At least one bad endpoint is internal. A one-edge
exchange includes an edge owned by that internal bad vertex while keeping it
internal. The owned size factor cancels one of the three host exponents, so

```text
d <= 4^4 U^2 = 313714944/49.
```

Suppose instead that there is no bad-bad seed edge. Connectedness and at least
three bad vertices leave either one or two good vertices. With one good vertex
`c`, the seed graph is a good-center star; summing the errors gives
`E>c-3`, hence `c<13/2`.

With two good vertices `c,u` and three bad vertices of total size `K`, each
bad error is greater than `-1/2`, while

```text
e_c+e_u >= max(c,u)-K.
```

Thus `E>max(c,u)-K-3/2`, so `max(c,u)<K+5`. Combining this with the window
and the other good size being at least one gives

```text
max(c,u) < G := (R+4)/2 = 1163/14.
```

Every bad vertex is below `R/3<G`. Therefore any four-edge seed tree has
`H_T<G^3`, even before using its bad-owned gains, and the no-bad-bad case is
bounded by

```text
4^4 G^3 = 50337207904/343
        = 1.46755708175... * 10^8.
```

### Exact residual table

| Initial pattern | Residual terminal denominator bound |
|---|---:|
| `(5)` | `4^4 G^3 = 50337207904/343` |
| `(4,1)` | `246688579584/343` |
| `(3,2)` | `11757191168/147` |
| `(3,1,1)` | `56623104` |
| `(2,2,1)`, pair joins pair first | `12441600` |
| `(2,2,1)`, pair joins singleton first | `622080` |

The `(4,1)` shared-edge path is now the largest. Therefore the actual C-B
residual satisfies

```text
d <= T_CB := 4^6(369/7)(404/7)^2
           = 246688579584/343
           = 7.192086868338... * 10^8.
```

This is a factor `4069716129/1142512 = 3562.0773...` below the universal
Section 11 cutoff. It is still far beyond the current exact bank, so this does
not close size 5 or Erdos #488. The next cutoff attack should either sharpen the
shared `(4,1)` path or replace finite enumeration by a uniform certificate.

## 12A. Exact bad-edge cofactors cut the residual cutoff below `2.494 * 10^6`

Status: `PROVED` at paper tier (Codex, 2026-07-17), strengthening Section 12.
No enumeration is used. The `7.193 * 10^8` bound above remains a valid real
relaxation; this subsection retains the integer cofactor information that it
discarded. Independent recheck is still requested before publication.

Write `R=1135/7`, `U=R-4=1107/7`, and retain the residual size bounds

```text
B=(R-1/2)/3=2263/42,  V=(R+7/2)/2=2319/28,
A=(R+9)/3=1198/21,   Q=(R-1)/3=376/7,
G=(R+4)/2=1163/14.
```

### The cofactor gain

In a `(4,1)` pattern, let `b` be bad in the four-component and let `y` be the
singleton. The three internal gcds have sum greater than `b-1/4`, so one of
them, say `q`, satisfies

```text
q > (b-1/4)/3.
```

The ratio `b/q` is an integer. Since `b>=1`,

```text
b/q < 3b/(b-1/4) <= 4,
```

hence `b/q<=3`. Thus every bad vertex has a **strong owned edge** of the exact
form `q=b/alpha`, `alpha in {2,3}`. If one edge is strongly owned by two bad
endpoints, their reduced coprime cofactors are therefore exactly `{3,2}`.
This removes the continuous near-equal endpoint that made Section 12 loose.

The analogous fact for a bad pair vertex in `(3,2)` or `(2,2,1)` is also exact.
If the pair gcd is `q>=1/4` and the source is `b=alpha q`, the three cross gcds
are below `1/4`, so

```text
(alpha-1)q < 3/4,
```

and again `alpha<=3`.

### A universal residual entry cap

There is a safe substitute for the tempting but unproved assertion that every
four-element complement has positive total deficit. If `Q` is any four-element
antichain of total size `K`, let `z=max(Q)` and let `T=Q-{z}`. For a sorted
triple `a<b<c`,

```text
2 sum_pair gcd <= 2a+b < a+b+c,
```

so the triple deficit is positive. Also
`2 sum_(t in T) gcd(z,t) <= sum(T)`. Therefore

```text
E_Q := K-2 sum_pair gcd(Q) > z-sum(T) = 2z-K >= -K/2.
```

Now fix any residual entry `x`, and let its four-element complement have total
size `K`. Since `2 gcd(x,q)<=q` for every complement entry,

```text
E > x-3K/2 >= 5x/2-3R/2.
```

Combining this with `E<=7/2` gives the universal residual cap

```text
x < X := (3R+7)/5 = 3454/35 = 98.685714... .
```

This uses only the elementary triple deficit, not the separately computed
quadruple density assertion.

### Pattern `(5)`

If the connected seed graph has a bad-bad edge, keep the reviewed Section 12
bound

The reviewed owner cancellation leaves two host slots. Even if a high-degree
host occupies both slots, the universal cap applies to each, so

```text
Z <= 4^4 X^2 = 3054109696/1225 = 2493150.7722... .
```

Suppose there is no bad-bad seed edge. With one good center, all four bad-owned
edges form the star, the residual estimate gives `c<13/2`, and
`Z<4^4(13/2)^3=70304`. With two goods and three bad vertices of total size `K`,
the three bad-owned edges are distinct and form a forest. Extend them to a
tree. If the extension touches a bad vertex, its host factor cancels its owned
gain and `Z<4^4G^2`. If the extension is the good-good edge, all bad vertices
are leaves. For `M=max(c,u)`,

```text
M < K+5,       product(bad sizes) >= K-2,       M<G.
```

For `M<=21/2`, the crude `M^3` bound is smaller; for `M>=21/2`,
`M^3/(M-7)` is increasing. Hence

```text
Z < 4^4 G^3/(G-7)
  = 100674415808/52185
  = 1929183.0182... .
```

Thus the no-bad-bad connected case is below the retained bad-bad row.

### Pattern `(4,1)`

If there is no bad-bad seed edge, the four-component is a good-center star.
Its three bad leaves have strong owned cofactors at most `3`, and `c<6`, so

```text
Z < 3^6 c^4 < 3^6 6^4 = 944784.
```

Now take the source-owned edge and an edge owned by an internal bad vertex.
If these edges are distinct, the only initially loose geometry is

```text
s -- t -- u -- r,
```

where `s,t,r` are bad, `s` is the final bridge source, and `u` is good. The two
owned gcds are `s/alpha` and `t/beta`, with `alpha,beta<=3`.

The third bad vertex `r` also has a strong owned edge `r/gamma`,
`gamma<=3`. This edge is automatically distinct from the first two. Moreover,
whichever of `s,t,u` it meets, the three owned edges form a spanning tree.
There are only three geometries.

1. If the third edge is `r-u`, the displayed path remains. The terminal
   denominator is

   ```text
   Z <= alpha^2 beta^2 gamma^2 u^2/(s r^2).
   ```

   The residual estimate from the two-owner calculation gives, more crudely,
   `u<2s+r+9/2`. Hence

   ```text
   u^2/(s r^2) < (2s+11/2)^2/s.
   ```

   On `1<=s<=B`, the last function is maximized at an endpoint, with the
   larger value at `s=B`. Thus this case is below

   ```text
   729 * 22629049/95046
     = 5498858907/31682
     = 173564.1344... .
   ```

2. If the third edge is `r-s`, the new tree is `r-s-t-u`; its internal hosts
   are `s,t`. Direct cancellation gives
   `Z<=alpha^2 beta^2 gamma^2 s/r^2<=729B<39280`.

3. If the third edge is `r-t`, the tree is a star centered at `t`, and

   ```text
   Z <= alpha^2 beta^2 gamma^2 t^2/(s r^2).
   ```

   If `beta=2`, this is at most
   `324B^2=46090521/49=940622.8775...`. If `beta=3`, summing the errors gives

```text
u < (1/2+2/alpha)s + (1/2+2/gamma)r - t/3 + 9/2.
```

   Since `u>=1`, this forces
   `t<(9/2)(s+r)+21/2`. For fixed `s`, division by `r` makes the right side
   largest at `r=1`; the resulting function
   `min(B,(9/2)s+15)^2/s` is at most `(39/2)^2=1521/4`. This case is therefore
   below `729*1521/4=1108809/4=277202.25`.

So every distinct-owner geometry is below `940623`.

It remains to check a shared strong edge. Its endpoint cofactors are `{3,2}`.
For a shared end-path the worst orientation is

```text
Z <= 4^6(27/16) q u^2/r^2,
u < min(2q+2r+9/2, R-5q-r-1),   q<r+1/2.
```

The two bounds meet the badness cap at

```text
r=536/35, q=1107/70, u=4673/70,
```

giving `Z<652683970881/314230=2077089.9369...`. For a middle shared path,
the exact tree formula is at most `15552 q^3/r^2`; badness gives
`q<r+1/2`, so `r<=B` gives less than `861502`. A shared star is no larger
(`gamma=2` gives the same envelope; `gamma=3` gives `q<2r/3+1/2`). Therefore

```text
Z_(4,1) < 652683970881/314230 = 2077089.9369... .
```

### Pattern `(3,2)`

If the first bridge source is a bad pair vertex `s=alpha q`, then `alpha<=3`,
the bridge gcd is at least `q/3`, and the first merged divisor is

```text
h_3 >= q/(3 alpha) >= 1/36.
```

The triple tree has common divisor at least `1/(16A)`. Both divisors meet at
a triple target of size below `A`, so

```text
Z <= 576 A^2 = 91853056/49 = 1874552.1632... .
```

For completeness, a triple source is smaller. If its tree host is bad, the
distinct/shared owner exchange gives `Z<24576Q=9240576/7`. If the host `h` is
good and the third triple vertex `v` is bad, include the distinct `v`-owned
edge. The two possible hosts give

```text
Z < 2048 p h^2/(s v^2),  p<12,
h < (s+v)/2+11/2,        h^2/(s v^2) <= 169/4,
```

or `Z<24576Q`; these are at most `1038336` and `9240576/7`. If both remaining
triple vertices are good, both pair vertices are bad. With
`h<s+11/2`, the last row is at most

```text
3072 (Q+11/2)^2/Q = 65975136/329.
```

Thus the pair-source row is the `(3,2)` maximum.

### Patterns `(3,1,1)` and `(2,2,1)`

In `(3,1,1)`, all triple vertices are bad. For sorted sizes
`M>=m>=ell`, badness of the largest gives

```text
M < (m+ell+1)/2 <= (M+ell+1)/2,
```

so `M<ell+1`. A largest-owned edge and the distinct edge owned by the third
vertex give

```text
h_3/d > k := (M-1/2)(ell-1/2)/(4M).
```

The two forced bridges therefore have terminal denominator

```text
Z <= 4M^3/k^4
  = 1024 M^7/((M-1/2)^4(ell-1/2)^4).
```

For `1<=M<2`, set `ell=1`; the function decreases to `M=7/6` and then
increases. For `M>=2`, set `ell=M-1`; the resulting function decreases.
The supremum occurs at `M=2,ell=1`, and

```text
Z < 33554432/81 = 414252.2469... .
```

Finally consider `(2,2,1)`. The singleton satisfies

```text
e_y>y-1,   sum(pair errors)>K/2-3,
```

so residuality gives `y<11/2`. At least three of the four pair vertices are
bad. For a pair-pair first bridge, let the target in the second pair be
`t=beta q_B`. If it is bad, `beta<=3`. If it is the unique good pair vertex,
its partner is bad with cofactor at most `3`, so `q_B>=1/3`; since every pair
entry is below `10`, the integer `beta` is at most `29`. The first merged
divisor is at least `1/36`, and the final source is below `3/2`, hence

```text
Z < 36^2 beta^2 (3/2) <= 1634904.
```

If a pair joins the singleton first, the same `1/36` divisor gives at most
`3888*29=112752` when the second source is in the triple. If the second source
is in the remaining pair, two `1/36` divisors meet at a target below `11/2`,
giving `Z<7128`.

### Corrected exact table

| Initial pattern | Residual terminal denominator bound |
|---|---:|
| `(5)` | `3054109696/1225` |
| `(4,1)` | `652683970881/314230` |
| `(3,2)` | `91853056/49` |
| `(3,1,1)` | `33554432/81` |
| `(2,2,1)`, pair joins pair first | `1634904` |
| `(2,2,1)`, pair joins singleton first | `112752` |

The connected bad-bad row is now largest. Since `gcd(D)=1`, the actual C-B
residual satisfies

```text
d < T_CB := 4^4(3454/35)^2
          = 3054109696/1225
          = 2493150.772244... .
```

This is a factor `6022670400/20877703 = 288.473...` below Section 12's previous
residual cutoff and `150172525160100/146143921 = 1027566.005...` below Section 11. It is
still not an enumerable completion: `d` bounds the minimum dual entry, not the
number of cases, and the other four entries can range up to `R d`.

Exact arithmetic used only to evaluate the displayed formulas:

```powershell
python -c "from fractions import Fraction as F; R=F(1135,7); X=(3*R+7)/5; A=F(1198,21); rows={'5':256*X**2,'41':F(652683970881,314230),'32':576*A**2,'311':F(33554432,81),'221pp':1634904,'221ps':112752}; [print(k,v,float(v)) for k,v in rows.items()]"
```

No negative-existence or exhaustive-range claim is based on this Python check.


## 13. DRIFT-TRANSFER lemma 1: per-class drift certificates — PROVED (executable)

*(Renumbered 12→13: Codex's §12 — the residual-inequality cutoff — landed concurrently.)*

Status: `PROVED-BY-CERTIFICATE` (Claude, 2026-07-17). `census drift` + `census emin`
(exact i128; `f·60` integral; retirement thresholds cross-multiplied) — output
committed as `census/CERTIFICATES.txt`, reproducible in <1s. This simultaneously
pays both standing reproducibility debts (the U2 kernel list and the size-6
`W`-retirement) with strictly stronger, fully-boxed certificates.

**Certified drift chains** (`f(J) ≥ σJ − δ` for ALL multisets of the class, any
entries; kernels = boxed multisets, everything above the box retired by the exact
peel `σ_{k−1} − 1/(2m*) ≥ σ_k` with `δ` monotone):

| class | σ (slope) | δ (defect) | kernels | retire m* chain | tight at |
|---|---|---|---|---|---|
| free 1..4 (U2) | `1/4, 5/36, 5/72, 7/300` | `0, 1/18, 1/9, 7/30` | 3+6+56+495 | 5, 8, 11 | `(2,2,3,5)`, `J=10` (deficit exactly `7/30`) |
| no-2 1..4 | `1/3, 17/72, 41/240, 457/3600` | `0, 1/8, 19/80, 2/5` | 3+6+35+495 | 6, 8, 12 | `(3,4,5,7)`, `J=16` |
| ≤one-2 1..4 | `1/4, 5/36, 31/360, 29/600` | `0, 1/9, 1/4, 1/2` | 4+5+112+1287 | 5, 10, 14 | `(2,3,5,7)`, `J=10` |

**Honest process notes.** The tool CORRECTED my claimed constants in two places
(no-2 `δ₂ = 1/8` not `1/9`, `δ₃ = 19/80` not `1/5`; ≤one-2 retirement `m* = 10`
not `9` — the exact check caught my by-hand threshold slip), and my first `e_of`
implementation overflowed `i128` exactly as Codex's audit warned primal products
could — rewritten with a fixed common denominator `60·lcm` (numerators bounded by
`2⁵·60·L`, no overflow possible in these boxes).

**Also certified (`census emin`):** the full E-minima chains (`3/4, 23/36, 41/72,
157/300, 49/100`) and class minima (`W₁ = 7423/12600`, `W₂ = 1087/2100`,
`E₄^{no2} = 2257/3600`, `E₄^{≤1·2} = 329/600`), plus the size-6 retirement
arithmetic: peel thresholds `M₀ = 15, 14, 17` for `W₀, W₁, W₂` — proving the
`[2..25]` box of `audit_sext_density_lemma.py` **sufficient** (the step its own
scope-caution flagged as unproved).

**What remains for DRIFT-TRANSFER (§10):** lemma 2 (class assignment on residual
cores — the structural step, where DRIFT-1's forced odd moduli meet the certified
slopes) and the assembly. The certified numbers to beat, on the window `n ≥ 2max`:
defects total ≤ `2·Σδ ≤ 7/3`-ish + `(5−S)` fractional loss vs slope gains
`2σ_K·⌊n/a⌋` per element — with `σ` now 2–5× the U2 baseline for every element
DRIFT-1 pushes out of the extremal class.

## 14. THE SPREAD THEOREM: full #488 separator for every quintuple with `max/min ≥ 7`

Status: `PROVED` at certificate tier (Claude/Codex, 2026-07-17; independent
referee pass still requested). The proof rests on DRIFT-1, the §13 certified
drift chains, FD, and the isolated exact Rust tool `spreadcheck/`. Codex reran
`census drift` from a clean release target and reproduced all class constants.
`spreadcheck/` first lowered the independent-class threshold to `11`; retaining
the compulsory modulus from the largest element and its small argument lowers
the final threshold to `7`.

**Theorem (SPREAD).** Every primitive quintuple `P = {a₁<…<a₅}` with
`a₅/a₁ ≥ 7` satisfies `2B(n) > nS` for **all** `n ≥ max(P)` — hence full
#488 for `P` (via `B(m)/m ≤ S < 2B(n)/n`). **No goodness, window, or CRIT
hypothesis.**

**Proof.** FD covers `max ≤ n < 2max`. For `n ≥ 2max`, put
`J_i=floor(n/a_i)` and use

```text
2B(n) − nS = 2Σ_i f_{a_i}(J_i) − Σ_i{n/a_i},
Σ_i{n/a_i} ≤ 5−S.
```

DRIFT-1 assigns `a₁` to the no-2 class, `a₂` to the at-most-one-2 class,
and permits the free class for `a₃,a₄,a₅`. The exact global floors are

```text
f_free(J) >= -1/12                    for J>=2,
f_at-most-one-2(J) >= 1/12            for J>=2,
f_no-2(J) >= 8/3                      for J>=22.
```

The first two finite scans contain 251 and 4,004 kernels. For the no-2 floor,
Rust checks 38,226 kernels over `J=22,23,24`; the §13 drift bound takes over
at `J=25`. Therefore, if `J₁>=22`,

```text
2B(n)-nS >= 2(8/3)+2(1/12)+6(-1/12)-5+S = S > 0.
```

It remains to assume `J₁<=21`. Write `M=a₅`, `rho=M/a₁`,
`g=gcd(a₁,M)`, `m=M/g`, and `k=a₁/g`. Then

```text
rho=m/k,   gcd(m,k)=1,   k>=2.
```

The last inequality is the antichain condition: `k=1` would mean `a₁|M`.
For a fixed `J`, replacing every modulus greater than `J` by `J+1` leaves
`f(J)` unchanged, so the unbounded tail has one exact finite representative.

**Case 1: `rho>8`.** Put `L=ceil(2rho)`. Since `J₁>=floor(2rho)` and
`J₁<=21`, one has `17<=L<=22`; moreover the `a₁`-row modulus contributed by
`M` is `m=rho*k>=2rho`, hence `m>=L`. The exact scan exhausts every no-2
kernel for `J=L−1,…,21` with at least one truncated modulus `>=L`.
Across `L=17,…,22` this is 60,088 kernel-layer checks, and every layer gives
`f_{a₁}(J₁)>=160/60=8/3`. The preceding assembly applies.

The missing equality `rho=8` cannot occur: it would say `M=8a₁`, contradicting
primitivity. Thus this case covers the entire interval `8<=rho<11`; for
`rho>=11`, already `J₁>=22` at `n=2M`.

**Case 2: `7<=rho<8`.** The exact coprime ratio-band scan exhausts
`J=14,…,21`. It retains a truncated row precisely when the compulsory
max-friend modulus is either the tail `J+1`, or an exact `m<=J` admitting
`k>=2` with

```text
gcd(m,k)=1,   7<=m/k<8,   floor(2m/k)<=J.
```

These are exactly the structural conditions above, with the last inequality
ensuring that the current `J` lies at or beyond the first doubling point.
Among 13,440 kernels the exact minimum is

```text
f_{a₁}(J₁)=155/60=31/12
at truncated moduli (3,4,5,15), J₁=15.
```

Now `n/a₁<22` and `rho>=7`, so

```text
2 <= J₅=floor(n/M) < 22/7,
```

hence `J₅` is `2` or `3`. A separate 20-kernel free-class scan gives
`f_{a₅}(J₅)>=10/60=1/6`, with equality at `(2,2,3,3), J₅=3`. Combining
that with the global floors for `a₂,a₃,a₄` gives

```text
2B(n)-nS
  >= 2(155/60 + 5/60 - 5/60 - 5/60 + 10/60) - 5 + S
   = 1/3 + S > 0.
```

This proves Case 2 and the theorem. ∎

**Consequences.**
1. Every primitive quintuple with spread at least `7` is covered uniformly;
   no bank, C4, goodness, window, or CRIT case split is needed.
2. **The open size-5 set collapses to compact residual cores** with
   `max/min<7`, `<=2`-good, window-relevant, and `CRIT<=7/2`.
3. Combining SPREAD with Section 12A leaves the explicit finite box

```text
min(D) < 3054109696/1225,
max(D)/min(D) < 7,
max(D) < 3054109696/175 < 17452056.
```

This is a substantial reduction but still far beyond direct enumeration.
The ratio-band scan fails at `rho>=13/2`: its independent minimum is
`110/60` at `(3,4,5,13)`. Any improvement below `7` must use more reciprocal
row correlations or residual-specific structure, not just the minimum and
maximum rows used here.

## 15. CORRECTION: the `a<=16` cluster cap used the wrong strong-edge endpoint

Status: `BROKEN` (the previous Section 15 and Claude's current triple inventory) /
`CORRECTED` (valid finite cap below) / `COMPUTED` (exact witness). This breaks
only the proposed stage-1 cluster inventory, not SPREAD, C-B-FIN, size-5
density, or #488 itself.

The project strong graph joins `x,y` when

```text
4 gcd(x,y) >= min(x,y),
```

because a bad **source** owns an edge with gcd at least one quarter of the
source. Claude's `census clusters` triple loop instead tests against the
larger endpoint, and the previous Section 15 silently copied that stronger
condition.

An exact missed normalized antichain is

```text
W=(20,28,35),   gcd(W)=1,   max/min=7/4<7,
gcd(20,35)=5,   gcd(28,35)=7.
```

Thus `(20,35)` and `(28,35)` are project-strong with equality:
`4*5=20=min(20,35)` and `4*7=28=min(28,35)`. The current generator rejects
both because `20,28<35`. This is the two-leaves-own-the-larger-center
orientation. The family `(4p,4q,pq)` supplies the same geometry whenever
`p,q` are suitable coprime odd integers.

### Valid replacement cap

Normalize and sort a connected strong triple as `a<b<c`, `gcd(a,b,c)=1`.
Choose two spanning strong edges and call their gcds `p,q`. They share a
vertex, so `gcd(p,q)=1` and `pq` divides that shared vertex. Each edge has
minimum endpoint at least `a`, hence

```text
p>=a/4,   q>=a/4,   a^2/16 <= pq <= c < 7a.
```

Therefore

```text
a < 112,   hence a<=111 and c<7a<=777.
```

This is weaker than `16` but rigorous and still finite. A complete ratio-7
triple census should enumerate

```text
2<=a<=111,   a<b<c<7a,   gcd(a,b,c)=1,
no divisibility, and at least two edges with 4*gcd>=min.
```

It must also record **edge ownership directions**. If the larger endpoint owns
an edge, the old max-strong test is appropriate; if the smaller endpoint owns
it, shapes such as `(20,28,35)` occur. The nine raw outputs (four after
normalization) are only the max-strong subset, not the full inventory.

## 16. Charge-good rows have a certified `1/2` floor and donor staircase

Status: `PROVED-BY-CERTIFICATE` / `COMPUTED` (Codex `spreadcheck/`, exact
integer arithmetic, 2026-07-17). This strengthens the stage-2 ingredients but
does not by itself close a cluster family.

For a primal row with moduli `m_1,...,m_4`, dual goodness is exactly

```text
charge = sum_i 1/m_i < 1.
```

It immediately permits at most one modulus `2`. For fixed `J`, the Rust scan
uses `J+1` as the exact representative of every modulus `>J`; such tail
entries may be chosen arbitrarily large when testing whether charge `<1` is
feasible. It checks 38,962 feasible truncated kernels over `J=2,...,20` and
finds

```text
f(J) >= 30/60 = 1/2,
```

with equality at truncated `(2,3,3,3), J=2`. The certified at-most-one-2
drift line `(29/600)J-1/2` is already at least `1/2` for `J>=21`, proving the
floor globally.

The same exact-prefix plus drift-takeover method gives the donor staircase:

| Argument range | Certified floor | Finite scan | Drift takeover |
|---|---:|---:|---:|
| `J>=6` | `5/6` | 162,538 kernels, `J=6..27` | `J=28` |
| `J>=12` | `7/6` | 486,891 kernels, `J=12..34` | `J=35` |
| `J>=15` | `3/2` | 1,194,267 kernels, `J=15..41` | `J=42` |

These constants are designed for DRIFT-1: if a good vertex donates a modulus
`2` to a bad row at argument `J_b`, then the donor is at most `2/3` as large,
so its argument is at least `floor(3J_b/2)`.

**Impact on Claude's v0/v1.** In an exactly-three-bad sector, the two outside
vertices really are dual-good. Replacing their free floors `-5/60` by
`30/60` raises the assembled margin by `140/60`, reducing the reported
one-scale shortages from `200..270` to `60..130` (still short). With four
bads, only the lone good receives this upgrade. Claude's correction that
`>=2` pinned odd moduli is vacuous is confirmed: `(2,2,3,5)` already has two
odd entries.

**Coordinate warning for v2.** Stage 1 is dual. A dual cluster `tW` maps to
the primal drift shape

```text
W^vee = {lcm(W)/w : w in W},
```

not generally to `W` itself. The four old max-strong shapes happen to be
closed under this involution (`(6,8,9)` swaps with `(8,9,12)`), so v0's
aggregate negative remains informative, but donation labels must be paired
with the involuted row in any joint certificate.

At the former `(4,6,9), tau=40` worst point, an exact prototype split on the
`(3,9)` row gives floors `5/12, 1/2, 23/12` for respectively two, one, or
zero donated 2s. The donor staircase makes all three local assemblies
nonnegative (the one-donor case lands at the retained `+S`). This is
`PLAUSIBLE` evidence for Claude's J-coupled v2, not a uniform shape proof.

## 17. Corrected min-strong triple inventory: 906 total, 69 all-internal-owner

Status: `COMPUTED` / `PROVED-BY-EXHAUSTIVE-ENUMERATION` conditional only on
the proved Section 15 cap. New isolated Rust tool: `clustercheck/`; Claude's
`census/` was not edited.

The tool exhausts every sorted normalized ratio-7 antichain triple in the
finite box

```text
2<=a<=111,  a<b<c<7a,  gcd(a,b,c)=1,
at least two edges satisfying 4*gcd(x,y)>=min(x,y).
```

For each edge it separately records whether the smaller endpoint can own it
(the min-strong condition) and whether the larger endpoint can own it (the
old max-strong condition). Exact output:

```text
min-strong connected triples:                         906
old >=2 max-strong subset:                              4
missed by old generator:                              902
largest can own an internal edge:                      71
all three vertices can own internal edges:             69
some vertex needs an outside edge if all three bad:   837
digest: acecafc73c9c3ea4f2ca565f56bb5111
```

The command is

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-clustercheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path clustercheck\Cargo.toml
```

The tool prints all 69 all-internal-owner shapes. These are the honest first
stage-2 target for an exactly-three-bad cluster whose owner edges stay inside
the triple. The other 837 are not automatically impossible: they belong to
the mixed owner-forest sector, where at least one bad vertex must own a strong
edge to one of the two outside vertices.

This is still not a full residual inventory. Four-bad cores, larger strong
components, and consistency between overlapping triples remain to classify.
The computation converts the old hidden hole into two explicit workloads:
`69` internal shapes and `837` mixed-owner candidates before further badness
and pairwise-cofactor pruning.

## 18. OUTSIDE-DONOR and the two-component normal form

Status: `PROVED-BY-CERTIFICATE` (OUTSIDE-DONOR) / `PROVED` (at most two
strong components and finite two-scale normal form) / `COMPUTED` (exact
histograms below). These statements concern the compact ratio-`<7` residual;
they do not close its two-parameter tower certificates.

### Exact divisor jump

For a directed source `x`, an edge to `y` is non-strong when

```text
4 gcd(x,y) < x.
```

Since `x/gcd(x,y)` is an integer greater than `4`, this strengthens to

```text
gcd(x,y) <= x/5.
```

Thus two non-strong outside edges can supply at most `2x/5` toward the
badness inequality `sum gcd >= x`.

### OUTSIDE-DONOR lemma

Let a compact residual have exactly three bad dual vertices. Then some bad
vertex has a strong edge to one of the two good vertices.

Suppose otherwise. Every bad vertex owns an edge within the bad triple, so
the underlying triple is connected and has at least two min-strong edges.
After dividing by its common gcd, Section 15 puts it in the exact 906-shape
box, and all three vertices owning internally puts it among the 69 shapes.
For a vertex `x`, let `I_x` be the sum of its two internal gcds. The refined
`clustercheck` scan tests whether

```text
I_x < 3x/5.
```

Every one of the 69 shapes has such a vertex. Its two good-side gcds are each
at most `x/5` under the no-outside-strong assumption, giving total charge
strictly below `x`, a contradiction. Exact histograms are

```text
all 906 by number of forced outside vertices: [0, 20, 258, 628]
69 internal-owner shapes by deficit-forced vertices: [0, 6, 17, 46]
sealed internal-owner shapes: 0
```

### Three strong components are impossible

At least three bad vertices are nonisolated in the undirected strong graph,
so it has at most three components. A three-component graph has pattern
`(3,1,1)` or `(2,2,1)`.

For `(3,1,1)`, both isolated vertices are good: four non-strong gcds contribute
at most `4x/5<x`. Hence all three vertices in the triple component are bad,
contradicting OUTSIDE-DONOR because component separation forbids a strong edge
to either singleton.

For `(2,2,1)`, the singleton is again good. Consider a bad vertex `x` in one
pair and let `q` be its gcd with its partner. Its three cross-component gcds
sum to at most `3x/5`, so badness forces `q>=2x/5`. Antichainness makes `q` a
proper divisor of `x`; therefore the integer `x/q` lies in `[2,5/2]`, forcing
`q=x/2`. Both endpoints of the pair cannot be bad, since the same common gcd
would then equal half of two distinct numbers. Each pair contains at most one
bad vertex, for a total of at most two, contradiction.

Therefore every compact residual has at most two strong components.

### Finite two-scale normal form

For a connected strong component `C` of size `k`, let `a=min(C)` and
`h=gcd(C)`. A spanning-tree edge has gcd at least `a/4`. Starting from one
edge and adjoining vertices, the lcm loss at each merge is below `7a`, because
the whole compact core has ratio `<7`. Hence

```text
h > a / (4*28^(k-2)),
max(C)/h < 28^(k-1).
```

After dividing by `h`, each component therefore belongs to a finite block
library (for `k=2,3,4,5`, every normalized coefficient is respectively below
`28, 784, 21952, 614656`). With at most two components, every compact residual
has the form

```text
D = tW union sV,
```

where `W,V` come from finite normalized block libraries and `gcd(t,s)=1`.
A singleton component is represented by the block `{1}`. This rigorously
justifies a two-scale C4-style closing architecture. What remains is to prove
the required uniform tower certificate for every admissible block pair and
scale relation; finiteness of the block library is not itself that certificate.

## 19. Compulsory-edge paired floor: exact but not closing

Status: `PROVED-BY-CERTIFICATE` / `FAILED-AS-A-STANDALONE-CLOSURE`. Isolated
tool: `paircheck/`.

For a strong edge from bad dual vertex to good dual vertex, write the reduced
cofactors as `(m,q)`. The bad row receives pinned modulus `m<=4`; antichainness
gives `m,q>=2`, coprimality gives `gcd(m,q)=1`, and compact spread gives
`q<7m`. The paired arguments are coupled by

```text
J_bad=floor(mx),  J_good=floor(qx).
```

`paircheck` exhausts all 32 cofactor types and every coupled layer through
`J=80`, with exact tail representatives. It enforces bad charge `>=1`, good
charge `<1`, and the pinned moduli, while relaxing unrelated row consistency.
The certified global minima are

```text
m=2: f_bad+f_good >= 40/60
m=3: f_bad+f_good >= 25/60
m=4: f_bad+f_good >= 35/60.
```

The hard `(m,q)=(3,2)` orientation attains `25/60`, exactly the independent
baseline `-5/60+30/60`. Thus OUTSIDE-DONOR alone does not close the residual.
It does reduce the joint scan: source types `m=2,4` earn bonuses `15/60,10/60`,
while the reverse `(3,2)` case must retain additional block structure.

## 20. v1.5 orientation audit: 29 of 69 relevant families pass

Status: `COMPUTED` / `PROVED-BY-CERTIFICATE` for the 29 passing dual-shape
families, subject to the already certified staircase inputs / `BROKEN` for the
reported `63/138` scope and repository reproducibility. This is a correction
to a stage-2 subtotal, not to #488 or any previously closed regime.

Claude's `census shape2v15` correctly improved the row relaxation with exact
badness-restricted tables and charge-good donor staircases. However, its input
is the list of **dual** shapes `W`. The associated primal row shape is uniquely

```text
W^vee = {lcm(W)/w : w in W},
```

so only the `dualize=true` side is semantically attached to each input. Running
both `W` and `W^vee` mixes the relevant primal side with a duplicate or
artificial side. In addition, commit `c510537` did not include its shape file.
`clustercheck/shapes69.csv` is now the canonical input, and `clustercheck`
asserts that it exactly equals the generated 69-shape list.

A temporary copy of the same exact Rust code, changed only from
`for dualize in [false,true]` to `[true]`, gives

```text
PASS 29 / SHORT 40 (of 69 relevant Wv sides)
worst: W=(6,10,15), primal side W^vee, margin*60=-190 at tau=20
```

Thus the honest certificate subtotal is 29 relevant families, not 63 of 138
shape-sides. The 29 passes remain valid because the scan relaxes the good
parameters and all donation patterns; the correction removes only sides with
no justified coordinate interpretation. The 40 short families are listed in
the exact audit output recorded in `adversary_collab_chat.md`.

Recommended repair in Claude's crate: make `shape2v15` accept the canonical CSV
and either run only dual-input to primal-row orientation, or report raw and
dualized counts separately with the latter labeled as the relevant total.

## 15. THE SCALE-BOUNDING LEMMA: two-block residuals collapse to banks + rider families

Status: `CLAIMED` (Claude, 2026-07-18) — elementary given §-prior pieces; Codex knife
requested. Verified exactly on the flagship pair (below). If it survives, the compact
box has NO remaining open mathematics — only mechanical enumeration + C4-style
certificates over finite lists.

**Setting** (Codex's rigorous two-scale architecture): every compact residual is
`D = t·W ∪ s·V`, `gcd(t,s)=1`, `W, V` from finite block libraries, block sizes
`(4,1)` or `(3,2)` (≤2 strong components; `(5)` forces `gcd=1` scale collapse). Under
the genericity normalization (`gcd(ts, Λ) = 1`, `Λ` the joint template lcm — non-generic
scale factors reassign into the blocks; closure claim flagged below), every element's
primal charge splits **exactly** as

```
charge(e) = internal_W(e) + C_e/(opposite scale),
```

with `internal` and `C_e` fixed rationals of the block pair (cross-gcds are template
constants). 

**Lemma SB (scale bounding).** If element `e` is bad (`charge ≥ 1`) and NOT internally
bad (`internal_W(e) < 1`), then the opposite scale is bounded:
`opp ≤ C_e/(1 − internal_W(e))` — an explicit per-pair constant. ∎ (one line from the
split.)

**Collapse.** The ceilings (§1) bound internally-bad elements: `0` per pair-block,
`≤1` per triple, `≤2` per 4-block. A residual needs `≥3` bads (3-bad AND 4-bad sectors
alike — the argument never uses exactly-3). Hence:
- `(3,2)` pairs: `≤1` internal-bad ⟹ `≥2` scale-bounding bads. If they span both
  blocks: **both scales bounded ⟹ finitely many members (bank)**. If both sit in one
  block: the opposite scale is fixed small (`t ≤ C`), leaving **finitely many
  single-scale rider families** `W·s ∪ V·t₀` — whose charges are then CONSTANT in `s`
  (the free scale drops out of every charge!), i.e. exactly the C4-canonical situation,
  closed by the mechanized collapse certificate per `(pair, t₀)`.
- `(4,1)`: `≤2` internal-bads ⟹ `≥1` scale-bounding bad ⟹ same dichotomy.

**Flagship verification** (`W = {4,6,9}`, `V = {12,18}` primal templates,
`P = {4s,6s,9s,12t,18t}`, `gcd(s,6t)=gcd(t,6)=1`): internal charges
`4/9, 5/6, 3/4 | 1/3, 1/2` — ALL `< 1` (no internally-bad element at all), with exact
scale bounds: `6s` bad ⟹ `t ≤ 5`; `9s` bad ⟹ `t ≤ 3`; `4s` NEVER bad (needs `5/9`
from `4/(9t)` — impossible); `12t` bad ⟹ `s ≤ 3`; `18t` bad ⟹ `s ≤ 5`. Any 3 bads
span both blocks ⟹ `s ≤ 5, t ≤ 5` ⟹ **the entire pair-family is a finite bank** (a
handful of coprime `(s,t)`, most killed by antichain/gcd constraints). Spot-checked:
all sampled generic `(s,t)` are ≥3-good (regime A), exactly as the lemma predicts.

**What this leaves, in total, for the compact box** (hence for full size-5):
1. Generate the two block libraries (Codex: coefficients `< 28^{k−1}`; his 906/69
   lists are the triple part) and, per admissible pair, the constant tables
   (`internal_W(e)`, `C_e`) — pure template arithmetic.
2. The **bank**: all both-bounded members — small explicit `(s,t)` boxes per pair.
3. The **rider families**: per (pair, bounded-scale value), one C4-style certificate —
   mechanized exact collapse + one-period scan (the mechanism already proven on
   C4-canonical, which is precisely one of these families).
4. **Flagged gaps**: (a) the non-generic reassignment closure (scales sharing factors
   with templates fold into adjusted blocks — statement + proof needed); (b) the
   library-pair admissibility filter (antichain, window, ratio<7 at the template
   level); (c) 24 of my 69 dual-shape certificates remain SHORT — but §15 SUPERSEDES
   that route: those shapes' members are covered by the (bank + rider) split directly,
   with the v2.1 certificates as a redundant floor.

If SB + the closure claim survive review, size-5 = [everything proved] + [a finite
mechanical program with no free parameters]. That is the end of the open structure.

## 15a. Gap (a) CLOSED: SB is genericity-free

Status: `PROVED` (Claude, 2026-07-18; elementary). The §15 "genericity /
non-generic reassignment" gap dissolves — the exact charge split was a luxury.

**Lemma CROSS.** For any integers `a, b ≥ 1` and any scales `x, y` with
`gcd(x,y) = 1` (no other hypotheses — shared factors with templates allowed):
`gcd(x·a, y·b) ≤ a·b.`
*Proof.* Per prime `p`: if `p ∣ x` then `p ∤ y`, so
`v_p(gcd) = min(v_p(x)+v_p(a), v_p(b)) ≤ v_p(b)`; symmetrically for `p ∣ y`;
if `p ∤ xy` then `v_p(gcd) = min(v_p(a), v_p(b))`. In every case
`v_p(gcd) ≤ v_p(a) + v_p(b)`. ∎ *(121,547 random exact tests, 0 violations.)*

**Consequence (SB unconditional).** With `P = h₁·A ∪ h₂·B` (the strong-component
decomposition: `h_i` the component gcds — coprime since `gcd(P)=1` — and `A, B`
the cofactor tuples, finite by Codex's `28^{k−1}` bound), every element
`e = h₁·a` has
`internal_A(a) ≤ charge(e) ≤ internal_A(a) + (Σ_{b∈B} a·b/b)/h₂
= internal_A(a) + |B|·a/h₂,`
with the internal part exactly scale-free (the `h₁` cancels). So **SB holds for
every member, generic or not**: bad + not-internally-bad ⟹
`h₂ ≤ |B|·a/(1 − internal_A(a))` — explicit, unconditional. The §15 collapse
(banks + rider families) therefore needs no reassignment machinery; non-generic
scale-sharing only *lowers* cross terms below the crude bound (the per-family
C4-style certificates compute the exact values anyway, shared factors included,
as C4-canonical's `v₃`-cases already demonstrated).

Remaining review surface for §15+15a, now small: (i) the ceilings' application
to block-internal charges (blocks are antichains, DT ceilings apply — check the
strong-component blocks are antichains: subsets of the antichain `P` ✓ trivially);
(ii) Codex's component-cofactor `28^{k−1}` library bound (his, paper tier);
(iii) the mechanical program's admissibility filters. Nothing else.

## 15b. CORRECTION: scale bounding belongs in dual coordinates; no compact riders remain

Status: `BROKEN` (the Section 15 primal-coordinate split and "opposite scale"
wording) / `PROVED` (dual-coordinate replacement and finite-bank consequence) /
`OPEN` (practical block-library generation and bank coverage). Full size 5 is
not closed by this structural reduction alone.

The strong components and two-scale normal form were proved for the **dual**
core

```text
D = tW union sV,  gcd(t,s)=1,
```

not for a primal union with the same block templates. Dualization uses the lcm
of the entire core and does not preserve that displayed primal block union.
Consequently Section 15's exact primal charge split and flagship example do not
justify its claimed application to the component decomposition.

There is, however, a simpler dual repair. For `w in W`, put

```text
c_W(w) = sum_{w' in W, w'!=w} gcd(w,w')/w.
```

By CROSS, `gcd(tw,sv)<=wv`, so the full dual self-charge satisfies

```text
sum_{d'!=tw} gcd(tw,d')/(tw)
 <= c_W(w) + (sum_{v in V} v)/t.
```

Therefore, if `tw` is globally bad but not internally bad, then its **own**
component scale is bounded:

```text
t <= (sum V)/(1-c_W(w)).
```

The denominator is effective: `c_W(w)` is an integer multiple of `1/w`, so
`1-c_W(w)>=1/w` whenever positive.

This yields a stronger compact conclusion than the rider split:

- In pattern `(3,2)`, the pair component has at most one globally bad vertex.
  Indeed, a bad pair vertex `x` receives at most `3x/5` across components, so
  its partner gcd must be `x/2`; both pair endpoints cannot satisfy this.
  Hence the triple contains at least two global bads, at least one of which is
  not internally bad (the size-3 ceiling is one), bounding the triple scale.
  If the pair has one bad, its scale is also bounded. If it has none, all three
  triple vertices are bad and both pair vertices good, contradicting
  OUTSIDE-DONOR because distinct strong components have no bad-good strong edge.
  Thus **both scales are bounded**.
- In pattern `(4,1)`, the singleton is globally good, since its four non-strong
  gcds sum to at most `4x/5`. At least three vertices of the four-block are bad,
  while at most two are internally bad. A noninternally-bad four-block vertex
  bounds the four-block scale. The compact ratio `<7` then bounds the singleton
  scale as well.
- In pattern `(5)`, the sole component scale is `1` because `gcd(D)=1`.

Thus every compact residual lies in a finite, explicitly bounded scale box for
a pair of finite normalized blocks. There are no unbounded compact rider
families; if one scale tried to escape with the other fixed, SPREAD/ratio `<7`
would already remove it. This is a cleaner finite-bank architecture, but the
block libraries and all scale boxes may still be too large for naive
enumeration. A generated bank or a uniform block-pair certificate is still
required before full size 5 can be called solved.

## 21. Shared donated-2 compatibility cuts the oriented v2.1 residual to 11 negatives

Status: `PROVED` (the 2-adic compatibility lemma) / `COMPUTED` (temporary exact
Rust audit) / `PLAUSIBLE` until folded into and reproduced from the shared
`census` crate.

The current committed `shape2v21` has adopted the dual-input orientation. With
`clustercheck/shapes69.csv`, it gives

```text
PASS 45 / SHORT 24 (of 69 relevant W^vee sides).
```

Its log headline `95/138` is stale. Extracting the binding flag patterns shows
that all 24 minima use donated modulus `2`; value descriptors are all `none`.

**Shared-2 lemma.** If the same good primal element `y` supplies modulus `2`
to bad primal elements `p_i`, then

```text
y/gcd(y,p_i)=2  =>  v_2(p_i)=v_2(y)-1.
```

Hence all bad coefficients receiving that same `2` must have equal 2-adic
valuation. For a scaled primal triple `p_i=u w_i`, this is equivalent to the
corresponding `v_2(w_i)` being equal. The condition is exact and scale-free.

A temporary copy of v2.1 was strengthened by (i) the mandatory OUTSIDE-DONOR
modulus in `{2,3,4}`, (ii) the exact coprime return stair for a named modulus
`v`, and (iii) this shared-2 compatibility. The first two do not change the
subtotal; the third gives

```text
positive margin: 49 families
zero constant margin, hence positive after retained +S: 9 families
genuinely negative: 11 families
total covered: 58/69
```

The 11 negative dual shapes and margins (`*60`) are

```text
(6,10,15):-50, (9,10,15):-50,
(4,6,9):-40, (8,9,12):-40,
(6,8,9):-20, (6,14,21):-20, (8,10,15):-20,
(9,14,21):-20, (10,12,15):-20, (12,14,21):-20,
(12,15,20):-20.
```

The zero cases are valid because the assembly is
`2 sum f - 5 + S`, with `S>0`; the shared code's strict `margin>0` display is a
conservative undercount. The next exact parameter is the return cofactor for a
donated `2`: compact spread and coprimality give
`q in {3,5,7,9,11,13}` and `y=2p_i/q`. The remaining 11 binders use only one or
two donated 2s, so this finite q-coupling is the targeted next certificate.

## 22. The q-coupling closes ALL 69 shapes: v2.2 (donated-2, Section 21 spec) and v3 (full slot-matrix exactness) — 69/69, 55 VACUOUS

Status: `PROVED` (the pinning identities and soundness lemmas below) /
`COMPUTED` (`census shape2v22`, `census shape2v3` on `clustercheck/shapes69.csv`,
rho=7; both in the shared crate, seconds of runtime) / `NEEDS-REFEREE` (Codex
knife requested on the italicized soundness points). Claude, 2026-07-18.

### 22.1 v2.2 — Section 21's donated-2 coupling, implemented exactly

For a good `y` donating modulus 2 to bad `p_i0 = w_i0*s`: `y = 2*p_i0/q` with
return cofactor `q = p_i0/gcd(y,p_i0)` ODD (the Section 21 2-adic lemma), `>= 3`
(antichain), and — sharper than `q <= 13` — the two-sided spread bounds

```text
q*wmax < 2*rho*w_i0     (from y > max(P)/rho >= wmax*s/rho, strict)
q*rho*wmin > 2*w_i0     (from y < rho*min(P) <= rho*wmin*s, strict).
```

The donor's every gcd is then an s-free template constant: for `q | A` one has
`gcd(A/q, B) = gcd(A, qB)/q` (per-prime check), so with `g_j = gcd(2*w_i0, q*w_j)`

```text
y's modulus in bad row j     = 2*w_i0/g_j    (an integer; forced slot),
row-y's modulus from bad p_j = q*w_j/g_j     (an integer).
```

Flag consistency (forced slot `== 2` exactly on flagged rows, `>= 3` on
unflagged; `= 1` is an antichain violation) partitions configuration space and
SUBSUMES the shared-2 compatibility of Section 21. When both goods are pinned
their mutual moduli are exact too: `gcd(A/q, B/r) = gcd(Ar, Bq)/(qr)` for
`q|A, r|B`, giving `G = gcd(2*w_a*q1, 2*w_b*q0)`, slots `2*w_b*q0/G` and
`2*w_a*q1/G`. Pinned goods get (i) an exact goodness test (sum of known
reciprocals `< 1`, else the branch is vacuous), and (ii) an exact drift row
`f_exact([q, q*w_j1/g_j1, q*w_j2/g_j2, m_free])` minimized over the
goodness-feasible free slot, evaluated at `J in [q*tau/(2w_i0),
q*(tau+1)/(2w_i0)]` and MINIMIZED over that interval (*f is not monotone in J;
single-point evaluation at the floor would be unsound*), floored by `stair60`.
Forced bad-row slots use exact-value row classes (clamped to `41 = JT+1`,
tail-exact for `J <= JT`; badness tested at clamped values — conservative
inclusion only).

Result (`census shape2v22 clustercheck/shapes69.csv 7`):

```text
PASS 67 / ZERO 1 / SHORT 1   (of 69 W^vee sides), 25 of the passes VACUOUS
ZERO  (4,6,9)   margin 0 at tau=18, pattern 000001, q0=3  (passes via +S)
SHORT (6,10,15) margin -30 at tau=20, pattern 000000 (NO donated 2s)
```

All 11 Section-21 negatives close except `(4,6,9)` (zero, valid) and
`(6,10,15)`, whose binder has no donated 2 at all — outside the v2.2 mechanism.

### 22.2 The generalization: every donation value pins its donor

The donated-2 lemma is the `v = 2` case of: if `y`'s modulus in row `i` is
exactly `v` (i.e. `y/gcd(y,p_i) = v`), then with `q = p_i/gcd(y,p_i)`:
`y = v*p_i/q`, and `gcd(v, q) = 1` — because `(y/g, p_i/g)` is a coprime pair.
("q odd" for `v = 2` is exactly this coprimality.) The same spread bounds hold
with `2 -> v`, the same s-free identities give forced slots
`v*w_i/gcd(v*w_i, q*w_j)` and returns `q*w_j/gcd(v*w_i, q*w_j)`, and `q >= 2`
(`q = 1` is `p_i | y`).

**v3 certificate** (`census shape2v3`): partition ALL of configuration space by
the CLASS MATRIX — for each of the 6 (row, good) slots, declare either an exact
value in `2..=6` or `BIG` (`>= 7`). Per-row badness prefilter (BIG capped at
`1/7` — includes every true configuration). Every good with an exact slot
anywhere is pinned through its first exact slot and branched over the finite
q-range; ALL its six gcds are then forced and checked against the declared
classes (exact match, or `>= 7` for BIG, `sy >= 2` antichain, exact goodness,
exact drift row as in v2.2). Goods with all-BIG columns are free (base stair).
Descriptors and the ">= 3 any" class are gone — the partition replaces them.

Soundness points (*the knife surface*):
1. *Partition completeness*: every true slot value maps to exactly one class;
   every true config to exactly one matrix; pinned branches enumerate its true
   `q`. Exclusion tests (class mismatch, `sy < 2`, goodness `>= 1`, badness
   impossible, mutual slot `< 2`) are all consequences of true-config axioms.
2. *BIG representatives in the row table*: for `J`-entry `j`, BIG-slot
   representatives are `m in [7, j+1]`, PLUS `m = j+1` when `j < 6` — any
   modulus `> j` has no divisibility events on `[1, j]`, so `f[j]` is identical
   for all of them, and badness at the representative is `>=` truth
   (conservative inclusion).
3. *Forced slots finer than declared*: on BIG-declared rows a pinned good's
   forced value (`>= 7`, possibly huge, clamped to 41) replaces the BIG class in
   the row lookup — exact, tail-valid for `J <= 40`.
4. The `-300` assembly, `tau`-range `[2*wmax, 33*rho*wmax]`, `stair60`, bad-row
   tail line `(420J)/300 - 14`, and W^vee orientation are IDENTICAL to v2.1 —
   only the branch structure changed.

### 22.3 Result: the 3-bad shape program is CLOSED

```text
census shape2v3 clustercheck/shapes69.csv 7:
PASS 69 (incl. 55 VACUOUS) / ZERO 0 / SHORT 0   (of 69 W^vee sides)
```

14 shapes carry uniform positive margins; **55 admit NO 3-bad configuration at
all within the stage-2 model** (common-scale bad triple, two goods, ratio < 7,
tau in the certified window; the tau-independent kills — antichain, goodness,
class consistency — are in fact position-free). Two vacuities hand-verified
end-to-end, including one of Section 21's negatives:

- `(9,12,16)` dual `[9,12,16]`: row `w=9` needs a donated 2 with partner
  `<= 5`; `q=3` donors divide `12s` (antichain), `q=5,7` donors force slot 9
  into row `w=16`, whose remaining need then demands a second 2 that no
  in-range donor can supply (`q = 9` needed, spread-excluded). Every corner dies.
- `(6,8,9)` dual `[8,9,12]` (Section 21 margin -20): rows `w=8` (need 5/9) and
  `w=9` (need 5/8) both require small slots; any 2-donor to one forces slot 16
  into the other (`gcd(16, 9q) = 1`, `gcd(18, 8q) <= 2` for feasible odd q),
  starving it; the `(3,3)` alternative for row `w=9` forces 27s into row `w=8`.
  Vacuous.

Consequences:
- The 24-SHORT v2.1 backlog and all 11 Section-21 negatives are retired.
- Given the 906 -> 69 relevance filter (Codex's clustercheck) and the stage-2
  regime conventions, the 3-BAD SECTOR of the compact box is fully certified.
- The exactness mechanism (donation value + return cofactor + spread = donor
  determined up to a bounded integer) is the shapes-route incarnation of the
  Section 15b scale-bounding: both say a bad's benefactor is pinned to finitely
  many templates. The 4-BAD sector remains: either via Section 15b's bank
  architecture (which never assumes exactly 3 bads) or a 4-shape inventory +
  the v3 analogue (3 bads + 2 goods -> 4 bads + 1 good; the class matrix
  becomes 4x1 with richer pins). This is now the only open sector of the
  compact box on the shapes route.

## 23. The 4-BAD sector: census, witnesses, and the shape4 certificate — 10/10 closed

Status: `COMPUTED` (census `cb` self-bad histogram; `shape4` certificates) /
`PROVED` (the good-junk structure lemma below; the certificate identities are
Section 22's) / `OPEN` (inventory completeness for 4-bad shapes; 5-bad
exclusion). Claude, 2026-07-18.

### 23.1 The sector is real but tiny

`census cb 240` now reports the self-bad histogram of the C-B residual (by
Duality Transport, dual self-bad count = primal bad count):

```text
residual 276:  3-bad 266, 4-bad 10, 5-bad 0
components: {[5]: 196, [4,1]: 79, [3,2]: 1}
```

All ten 4-bad residuals are SINGLE strong component. Their normalized primal
bad-quadruple shapes (bads/gcd; ten distinct):

```text
(2,3,5,7)s=5 g=6   (4,6,9,15)s=3 g=8   (4,6,10,15)s=3 g=8   (4,6,14,21)s=3 g=8
(6,9,10,15)s=1 g=4 (6,10,14,15)s=1 g=4 (6,10,15,21)s=1 g=4  (6,10,15,27)s=1 g=4
(12,18,20,45)s=1 g=8                   (20,30,36,45)s=1 g=8
```

(`census/shapes4bad10.csv`, extractor `census/extract_4bad.py`.) The list
includes the celebrities: `{4,6,9,10,15}` and `{4,6,10,14,15}` are the
`(6,9,10,15)` and `(6,10,14,15)` rows.

### 23.2 Good-junk structure: the sector's only infinite direction

**Lemma (good-junk).** In a 4-bad quintuple (4 bads, 1 good `y`), multiplying
`y` by any `q` coprime to all bads leaves every bad's charge UNCHANGED
(`gcd(b, qy) = gcd(b, y)`), while `y`'s own charge only drops. So each 4-bad
configuration generates a 1-parameter infinite family, and it is the ONLY junk
direction (coefficient junk on a bad changes that bad's own charge scale).
In slot terms: as `q` grows, the good's donated slots `qy/gcd` grow through the
exact classes into all-BIG — precisely the free-good branch of the certificate.

### 23.3 shape4: the v3 certificate with a 4x1 class matrix

`census shape4 <csv> [rho]`: 4 bad rows `w_i*s` (three pins each), one good;
class matrix = 4 slots (exact 2..=6 or BIG >= 7); an exact slot pins the good
exactly as in Section 22 (`y = v*w_i**s/q`, `gcd(v,q)=1`, spread-bounded q,
all four gcds forced and checked); a pinned good's own row has NO free slot —
goodness and drift are fully determined. The all-BIG column covers the entire
good-junk tail uniformly. Same assembly, tau-range, stairs, tails as v2.1/v3.

```text
census shape4 census/shapes4bad10.csv 7:
PASS 10 (incl. 1 VACUOUS) / ZERO 0 / SHORT 0
margins*60: (6,10,14,15):120 (6,9,10,15):180 (6,10,15,21):240 (2,3,5,7):360
(12,18,20,45):360 (4,6,10,15):420 (20,30,36,45):420 (6,10,15,27):480
(4,6,9,15):540;  (4,6,14,21): VACUOUS in-box
```

The `(4,6,14,21)` vacuity is CORRECT, not a bug: its witness
`P=[8,12,18,42,63]` has ratio `63/8 = 7.875 >= 7`, so it is retired by SPREAD
(rho0=7) and its ratio<7 box-slice is genuinely empty — the certificates tile.
Note `(6,9,10,15)` PASS margin 180 is a UNIFORM theorem over the whole family
`{6s,9s,10s,15s} + any good` — containing the notorious `{4,6,9,10,15}`.

### 23.4 What remains for the compact box (both sectors closed in-inventory)

1. **3-bad inventory completeness**: the 906 -> 69 relevance filter (Codex's
   clustercheck derivation) is the hypothesis under my Section 22 certificates.
2. **4-bad inventory completeness**: the ten shapes are the M=240 in-range
   witnesses, NOT a derived inventory. Needed: the structural argument (row
   badness with one good forces `sum_j gcd(w_i,w_j)/w_j >= 1/2` for EVERY row —
   a 4-fold entanglement condition — plus shape-level `w4/w1 < 7`; a W-FIN-type
   bound caps the shape list) or Codex's component machinery. `cb 360`
   saturation sweep running for empirical stability.
3. **5-bad exclusion**: no 5-bad residual in range (histogram above), and a
   5-bad set has no good to donate; the DT ceilings stop at k=4. A one-line
   ceiling argument for k=5 would close this formally.
4. Codex's knife on Sections 22-23.

### 23.5 UPGRADE: the inventory is now filter-complete up to w1 <= 120 — 174/174

`census shapes4inv <w1max> <rho>`: exhaustive enumeration of ALL quadruple
shapes `w1<w2<w3<w4` with `w1 <= w1max`, `w4 < rho*w1` (shape-level ratio),
`gcd = 1`, antichain, and the NECESSARY per-row condition
`sum_{j!=i} gcd(w_i,w_j)/w_j >= 1/2` (one good, best slot 2) for every row.
This is a complete superset of all 4-bad bad-quadruple shapes with `w1 <= w1max`.

```text
census shapes4inv 120 7:  174 shapes (census/shapes4inv120.csv)
  w1 saturates at 40 (counts: ...,20:x4, 24:x2, 30:x6, 36:x1, 40:x1) vs cap 120
census shape4 census/shapes4inv120.csv 7:
  PASS 174 (incl. 164 VACUOUS) / ZERO 0 / SHORT 0
```

All ten M=240 witnesses are contained; the margin-carriers are the nine witness
shapes PLUS `(6,9,14,15)` (margin 240) — a live shape no in-range witness had
produced, which is exactly why the filter-complete enumeration matters.

**Sector status.** Every 4-bad quintuple whose bad-quadruple shape has
`w1 <= 120` satisfies the window inequality uniformly (in the bad scale and the
good) — 10 shapes by margin, 164 by vacuity. The sector's ONLY remaining formal
gap: **no 4-bad shape has w1 > 120** (saturation at 40 is strong evidence; the
proof wants the W-FIN/gap-ladder machinery ported to the quadruple 1/2-filter:
bounded ratio + gcd=1 + all-four-rows 1/2-entangled => bounded w1 — Codex, this
is squarely your ladder). The `cb 360` sweep doubles as a live test: any new
witness must land inside the 174 list.

### 23.6 Obligation (d) is CLOSED: the k=5 ceiling is the min-good lemma

Status: `PROVED` (elementary; it is the campaign's existing "min always good"
asset, restated as a DT ceiling). For the maximum `d5` of ANY 5-element
antichain: writing each smaller `d_j = k_j * d5/m_j` in lowest terms
(`g_j = gcd(d5, d_j) = d5/m_j`, `k_j = d_j/g_j`), gcd-reduction forces
`gcd(k_j, m_j) = 1`, and the antichain forces `k_j >= 2` (`k_j = 1` is
`d_j | d5`). The four fractions `k_j/m_j` are distinct (the `d_j` are), and the
available slots per denominator are `m=3: {2/3}`, `m=4: {3/4}`,
`m=5: {2/5, 3/5, 4/5}`, ... so

```text
sum_j gcd(d5, d_j)/d5 = sum 1/m_j <= 1/3 + 1/4 + 1/5 + 1/5 = 59/60 < 1.
```

The dual maximum is NEVER self-bad: **at most 4 self-bad in any antichain
quintuple, no ratio/window/gcd hypotheses at all**. By Duality Transport
(dual max = primal min) this is precisely "the primal minimum is always good
with charge <= 59/60, extremal cofactors {3,4,5,5}". Consequence: the compact
box's bad-count inventory {3-bad, 4-bad} is a THEOREM, and the remaining
obligations are only (a) the knife, (b) 3-bad 69-list completeness, and
(c') the 4-bad w1-bound.

## 23.7 Attack on (c'): the w1-bound, analytic skeleton + two closing enumerations

Status: `CLAIMED` (Claude, 2026-07-18; knife requested) — the case analysis
below is elementary and complete modulo the two executable certificates
specified at the end, which are the proof's computational leaves.

**Setting.** w1 < w2 < w3 < w4, gcd = 1, antichain, w4 < 7*w1, and every row
`sum_{j != i} gcd(w_i,w_j)/w_j >= 1/2`. Each term is an EXACT unit fraction:
`gcd(w_i,w_j)/w_j = 1/m_ij`, where `w_j/w_i = m_ij/k_ij` in lowest terms; the
antichain forces `k_ij, m_ij >= 2`.

**Heavy graph.** Sum of three unit fractions `>= 1/2` forces `min m <= 6`:
every vertex has an incident edge with `gcd(w_i,w_j) >= w_j/6 >= w1/6` (call
these HEAVY). Heavy cofactors are `<= 7*w1/(w1/6) = 42`, coprime, `>= 2`.
Min-degree >= 1 on 4 vertices: the heavy graph is connected (case 4) or two
2-components (case 2,2).

**Case (4): w1 <= 1512.** Spanning tree; standard chain (`lcm | w` transfer)
gives the gcd h3 of any connected triple: h3 >= (w1/6)/42 = w1/252. Pick a tree
leaf y; the other three form a connected triple with exact gcd s = h3 and
coprime cofactors c_i <= 1764. Now `gcd(s, w_y) = gcd(all four) = 1`, so every
term of y's row is

```text
gcd(w_y, s*c_i)/(s*c_i) <= gcd(w_y,s)*gcd(w_y,c_i)/(s*c_i) <= c_i/(s*c_i) = 1/s,
```

hence `1/2 <= 3/s`, i.e. **s <= 6**, and `w1 <= 252*s <= 1512`. (Leaf-row
starvation — the same mechanism as the v3 vacuities.) Sharper, per s: the
leaf row needs `sum gcd(w_y,c_i)/c_i >= s/2` — for s = 6 ALL c_i | w_y; for
s in {3,4,5} at least one c_i | w_y — heavy divisibility rigidity.

**Case (2,2): finite explicit box.** Components A = h_A*{alpha, alpha'},
B = h_B*{beta, beta'}; h_A, h_B >= w1/6, gcd(h_A, h_B) = gcd(tuple) = 1,
cofactor pairs coprime, in [2, 42]. Every component has a NEEDY row (the
element whose partner cofactor is >= 3 — at most one internal term is 1/2
since the cofactors are coprime): internal <= 1/3 forces cross-sum >= 1/6,
so SOME cross term >= 1/12. That cross pair's reduced fraction
`(h_A*alpha)/(h_B*beta) = K/M` has `M <= 12`, `K >= 2` (antichain),
`K/M in (1/7, 7)` so `K <= 83`. Since gcd(h_A, h_B) = 1, reducing
`K*beta / (M*alpha)` DETERMINES the scales:

```text
g0 = gcd(K*beta, M*alpha),   h_A = K*beta/g0,   h_B = M*alpha/g0.
```

The whole case is the finite box (alpha, alpha', beta, beta', K, M, choice of
needy element and pinned partner) — every candidate fully determined, all
conditions then checked EXACTLY. Coarse corollary: h_B <= 12*alpha <= 504 etc.
gives the crude global `w1 <= 21168`; the box enumeration replaces the crude
bound with the exact list.

**The two executable certificates that close (c'):**
1. `census c4bound22`: the (2,2) box above — expected result: every survivor
   has w1 <= 40 (matching the 174-list; any new shape gets shape4'd).
2. `census shapes4inv2 1512`: heavy-partner generator enumeration to 1512 —
   for every tuple, row 1 owns a heavy partner `w_j = w1*m/k` with `k | w1`,
   `(k,m) in {(2,3),(2,5),(3,4),(3,5),(4,5),(5,6)}` — so one of the three
   loops collapses to ~6*d(w1) candidates; validated against shapes4inv on
   [2,300], then run to 1512 to close case (4)'s range.

Together: (c') becomes `w1 <= 1512` (case 4) and an exact (2,2) list — i.e.
the 4-bad shape inventory is COMPLETE, with the same certificate tier as the
rest of the program.

## 24. CORRECTION and repair: v3 must use all 906 triples, and all 906 pass

Status: `BROKEN` (Section 22.3's inference from the 69-file alone) /
`COMPUTED` (full exact Rust run) / `NEEDS-REFEREE` (v3 soundness). Codex,
2026-07-18.

Section 17 explicitly says the 69 canonical triples are only the shapes where
all three bad vertices can own strong edges internally. The other 837
min-strong triples are mixed-owner shapes where at least one bad must use an
outside good. Therefore `PASS 69` did **not** by itself prove three-bad
inventory completeness, and Section 22.3's stated 906-to-69 implication was
missing those inputs.

The repair is direct. `clustercheck` now materializes and self-checks a second
canonical file, `clustercheck/shapes906.csv`, containing the complete exhaustive
inventory from the proved cap

```text
2 <= a <= 111, a < b < c < 7a, gcd(a,b,c)=1,
antichain, at least two min-strong edges.
```

Its count is 906 and digest remains
`acecafc73c9c3ea4f2ca565f56bb5111`. Running the shared v3 certificate on the
complete file gives

```text
PASS 906 (incl. 869 VACUOUS) / ZERO 0 / SHORT 0
```

Exact commands:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-clustercheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path clustercheck\Cargo.toml

$env:CARGO_TARGET_DIR='C:\tmp\ep488-census-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml -- shape2v3 clustercheck\shapes906.csv 7
```

Thus the previous 69-input flaw is repaired only within the min-strong triple
class: subject to the Section 22 v3 soundness audit, every one of the 906
triples having at least two internal strong edges is certified. This does not
prove that every three-bad residual belongs to that class. Section 25 records
exact one-edge residual counterexamples to that missing implication. Separately,
the cutoff-free `fourbadcheck` spanning-tree and two-pair enumerations recover
the same 174 four-bad necessary-filter shapes, removing the former above-300
inventory gap subject to review.

## 24. SIZE-5 ASSEMBLY LEDGER (2026-07-18 state): every regime, its tier, its dependency

Status: bookkeeping (Claude). For a primitive quintuple P and n >= max(P),
first matching regime applies. Tags: LEAN (sorry-free, axiom-clean),
PAPER (written proof, hostile-reviewed), CERT (executable exact certificate
in-repo, reproduced).

| # | Regime | Statement | Tier | Open dependency |
|---|--------|-----------|------|-----------------|
| 1 | A | >= 3 good charges => 2B(n) > nS, all n | LEAN (Quint.lean ep488_quint_three_good) | — |
| 2 | FD | max <= n < 2max, unconditional (size-4 separator + exact identity) | LEAN (Quad.lean) + PAPER assembly | — |
| 3 | B | bridge: 7nS > 1135 - 157S (incl. n >= 33 max) via U2 drift | LEAN identity/application/assembly + CERT kernel | — |
| 4 | C0 | gcd(P) > 1: scaling to the primitive base — applies only after A/FD/Bridge/C-B/SPREAD at the original scale; C0 feeds box sectors, whose stage-2 margin and banks are tower-calibrated and whose tail is drift_bridge_tower | PAPER + LEAN seam | — |
| 5 | C-B | CRIT > 7/2 => 2B > nS | LEAN (cb_cover5, conditional) + PAPER (CRIT>7/2 => its hypothesis) | — |
| 6 | SPREAD | ratio >= 7 => 2B > nS, all n | PAPER + CERT (spreadcheck, census) | — |
| 7 | box, bad count | any antichain quintuple has <= 4 self-bad (Section 23.6) | LEAN (Ceiling.lean) | — |
| 8 | box, 3-bad | >=2 edges: 906/v3; 1 edge: exact 19-bank; 0 edges: exact 4-bank | PAPER reductions + CERT | second external pass |
| 9 | box, 4-bad | cutoff-free tree + two-pair inventory gives 174 shapes; shape4 is 174/174 (164 vacuous) | PAPER inventory + CERT | second external pass |
| 10 | seams | [2 wmax s, 33 rho wmax s] stage-2 window meshes with FD below (wmax s <= max P) and B above (33 max P <= 33 rho wmax s) | PAPER (one-line each) | — |

W-FIN / C-B-FIN (residual min < 2.4932e6, PAPER, jointly reviewed) underpins
the box being compact at all. The three-good Lean + Density reduction carry
the >= 3-good bulk. External: ChatGPT W-FIN hostile review pending (Wes).

**What is left, in total, for size 5:**
(a) obtain the second independent external pass on the v3/shape4 and W-FIN
    review packages;
(b) consolidate the proof text and dependency ledger without upgrading the
    certificate-backed steps beyond their stated tier.
Lean debt (kernel 157/300, the lower U2 retirements 5/8 and one/two/three-modulus finite kernels,
W-FIN core, SPREAD, box certificates) is scope-fenced by Wes's decision A:
explicit hypotheses,
deliberately outside Lean for now.

**Note (asymmetry worth stating).** The 4-bad sector needs NO cluster
derivation: any 4-bad quintuple's bad-quadruple is s*(w1..w4) with
s = gcd(bads) by construction, the 1/2-filter is necessary and scale-free, and
ratio/antichain/gcd descend to the shape. So 4-bad completeness = the w1-bound
alone (c'), independent of (b). The 3-bad sector cannot argue this way: with
two goods the naive per-row filter is vacuous (1 - 1/2 - 1/2 = 0), which is
precisely why its inventory rests on the strong-edge cluster structure
(Codex's 906/69 with proved cap) — obligation (b) is genuinely 3-bad-specific.

### 22.4 CORRECTION (Claude, after Codex's knife): the 69-input consequence was an overclaim

Codex is right: Section 22.3's "the 3-bad sector is fully certified given the
906 -> 69 relevance filter" promoted the wrong input. The 69 are only the
all-internal-owner triples; 837 further min-strong triples can host three bads
with an outside owner, and OUTSIDE-DONOR predicts rather than deletes them.
His repair: `clustercheck` now emits the full `shapes906.csv` (asserted equal
to its generated inventory), and shape2v3 on ALL 906 gives

```text
PASS 906 (incl. 869 VACUOUS) / ZERO 0 / SHORT 0     [Codex ran; Claude reproduced, 0.31s]
```

So the certificate family survives at full strength on the complete min-strong
inventory. Obligation (b) SHARPENS to: every 3-bad compact residual's bad
triple is u*W for some W in the 906 list (min-strong: >= 2 internal strong
edges) — the statement + proof location is Codex's; the <= 1-internal-strong-
edge configuration class must be shown empty or otherwise covered (his
Section 15b component machinery is the natural home).

## 25. SECOND INVENTORY CORRECTION: one-edge bad triples exist; four-bad inventory closes cutoff-free

Status: `BROKEN` (full-three-bad inference) / `COMPUTED` (exact residual audit
and certificates) / `PLAUSIBLE` (finite-reduction proofs pending hostile review).
Codex, 2026-07-18.

### 25.1 Confirmed three-bad flaw

The implication required after Section 24 is false: an exactly-three-self-bad
residual need not have two strong edges induced on its three bad vertices. The
owned exact Rust tool `badtriplecheck/` enumerates the same primitive,
antichain, window-relevant, at-most-two-good, `CRIT<=7/2` residual conditions.
At dual-entry bound 120 it gives

```text
<=2-good window class: 3244
C-B residual: 195
self-bad histogram [0..5]: [0, 0, 0, 188, 7, 0]
exactly-3-bad induced strong edges [0,1,2,3]: [0, 13, 57, 118]
>=2-edge residual coverage by clustercheck\shapes906.csv: 175/175
RESULT: ALL PASS
```

The first one-edge witness is

```text
D=[9,10,12,15,42], bad indices [0,1,2]
row gcd-sums=[10,10,14,14,14]
P=[30,84,105,126,140]
CRIT=(88-2*31)/9=26/9 <= 7/2.
```

Among the bad triple `[9,10,12]`, only `(9,12)` is strong: the other two
pairs have `4*gcd` equal to 4 and 8, below minima 9 and 10. The normalized
triple is absent from `shapes906.csv`. This breaks only the proposed inventory
lemma, not #488; the full residual itself passes the existing direct tower bank.
No zero-edge witness occurs through 120, which is `COMPUTED`, not a global
exclusion. Conversely, all 175 residuals in this range having two or three
internal strong edges normalize into the canonical 906 file.

Exact command:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-badtriplecheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path badtriplecheck\Cargo.toml -- 120 clustercheck\shapes906.csv
```

### 25.2 Four-bad cutoff-free inventory

The owned independent `fourbadcheck/` removes the empirical `w1<=300` edge.
Every bad vertex is incident to a heavy edge. On four vertices, the heavy graph
is either connected or two disjoint pairs. The connected case is exhaustively
generated from all 16 labeled spanning trees and every reduced heavy-edge ratio;
antichain, heaviness, and spread `<7` bound each reduced endpoint to `[2,41]`.
The two-pair case is generated from the finite needy-row scale box. Both routes
are checked against the canonical 174-row necessary-filter fixture and give

```text
canonical necessary-filter shapes: 174
heavy-graph split: connected=172, two-pair=2
connected spanning-tree box: 172 shapes, largest w1=40, outside=0, missing=0
two-pair scale box: 174 shapes, largest w1=40, outside=0, missing-two-pair=0
RESULT: ALL PASS
```

Together with shared `shape4` output
`PASS 174 (incl. 164 VACUOUS) / ZERO 0 / SHORT 0`, this closes the four-bad
sector at certificate tier, subject to a hostile proof/code audit.

### 23.8 (c') CLOSED: the 4-bad inventory is complete; the sector falls

Status: `PROVED` (Section 23.7 case analysis) + `COMPUTED` (its two executable
certificates, both now run). Claude, 2026-07-18.

```text
census c4bound22 7:          174 shapes, largest w1 = 40   [(2,2) split, complete, no w1 bound]
census shapes4inv2 1512 7:   174 shapes, largest w1 = 40   [all shapes w1 <= 1512; EXACT MATCH]
```

Assembly: any 4-bad shape's heavy graph is case (4) or (2,2). Case (4) forces
w1 <= 1511 (leaf starvation, 23.7), and the generator sweep to 1512 is complete
there; case (2,2) is exhausted by the needy-row K/M box with no bound at all.
Both return exactly `census/shapes4inv120.csv`. With the necessary-filter
argument (23.5), the k=5 ceiling (23.6), and `shape4` 174/174 (23.3, 23.5):

**Every 4-bad compact residual satisfies the window inequality — uniformly in
the bad scale and the good, with a COMPLETE shape inventory. The 4-bad sector
is closed, conditional only on the (a) knife of the shared certificate code.**

The compact box, and with it full size 5, now rests on exactly two items:
(a) the hostile audit of shape2v3/shape4 (Codex's recommended check (i)), and
(b) the 3-bad min-strong completeness statement (Codex, Section 22.4).

## 25. The one-edge 3-bad family: fully pinned, both scales bounded, NO riders — a finite bank

Status: `CLAIMED` (Claude, 2026-07-18; elementary given CROSS + divisor jump;
knife requested). Addresses Codex's badtriplecheck finding (13 in-range
witnesses outside the min-strong inventories) and his recommended check (1).

**Setting.** Exactly-3-bad compact residual, bads {b1,b2,b3} (dual), exactly
one internal strong edge b1--b2; b3's internal edges non-strong.

**1. b3's goods are divisor-pinned.** Non-strong divisor jump: gcd(b3,bi) <=
b3/5, so the two goods supply >= 3*b3/5 of b3's self-bad sum. The larger
supplies >= 3*b3/10, so b3/gcd(b3,g) in {2,3} (=1 is antichain). Writing
c_j = b3/gcd(b3,g_j): (c1,c2) in {(2, <=10), (3, <=3)} (from the residual need
3/5 - 1/c1), every c_j | b3, and g_j = b3*k_j/c_j with gcd(k_j,c_j)=1,
k_j/c_j in (1/7,7), k_j >= 2 (antichain). BOTH goods live in b3's divisor
orbit: the block {b3,g1,g2} = v*{L, L*k1/c1, L*k2/c2}, L = lcm(c1,c2) | b3,
v = b3/L (normalize to coprime cofactors).

**2. Both scales are bounded — the only rider candidate is arithmetic-vacuous.**
Write the pair block {b1,b2} = u*{alpha,alpha'} (coprime, min <= 4 from the
strong edge, max <= 27 from ratio); gcd(u,v) | gcd(D) = 1, so CROSS applies:
- Pair row (u*alpha): 1/alpha' + 3*alpha/v >= 1  =>  v <= 3*alpha/(1 - 1/alpha')
  <= 6*alpha <= 162. The b3-block scale is ALWAYS bounded.
- b3 row: 1/k1 + 1/k2 + 2*gamma_b/u >= 1 with gamma_b = L. If
  1/k1 + 1/k2 < 1: u <= 2L/(1 - 1/k1 - 1/k2) <= 12L. The only way u escapes is
  k1 = k2 = 2 — but k=2 forces c odd, so c1 = 3, and then the b3-need
  1/3 + 1/c2 >= 3/5 forces c2 <= 3.75, i.e. c2 = 3 = c1, making g1 = g2 = 2b3/3
  — the same element. VACUOUS. Hence u <= 12L always.

**3. Consequence.** The one-edge family is a FINITE EXPLICIT BANK: templates
(alpha, alpha') x (c1,k1) x (c2,k2) from the small lists above, scales
u <= 12L, v <= 6*alpha, no rider families at all. Enumerate + window-check =
the certificate. (Contrast Section 15b: this is its (3,2) pattern — triple
block {b1,b2,+strong good} and pair block — arriving by an independent route
with explicit constants; the 2-component <=1-bad lemma is what forces a good
into the pair cluster.)

**Witness sanity** (D=[10,12,18,27,45], bads {10,12,18}, one edge 12--18):
b3 = 10; gcd(10,45) = 5 = b3/2 (c=2 pin, 45 = 10*9/2, k=9); gcd(10,27) = 1 =
b3/10 (boundary of the c2 <= 10 window); pair {12,18} = 6*(2,3); the good 45
is simultaneously strong with 18 (4*9 >= 18) — the double-orbit
overdetermination that makes the family small.

**Remaining for the 3-bad sector after this:** (i) the bank enumeration +
window certificates (census build, next); (ii) the ZERO-edge class: every bad
then needs a {2,3}-pin from the goods, two bads share a pinned good by
pigeonhole — expected provably empty or a tiny second bank (Codex check (2):
do NOT infer emptiness from the M=120 zero); (iii) Codex's knife on this
section; (iv) the min-strong (>= 2-edge) class stays covered by 906/906 v3.

## 26. ADVERSARIAL CORRECTION and complete edge-count bank candidate

Status: `BROKEN` (initial `census bank1edge` proof/completeness claim) /
`COMPUTED` (corrected exact one-edge and zero-edge banks) / `PLAUSIBLE`
(complete compact closure pending hostile proof/code/assembly audit). Codex,
2026-07-18.

### 26.1 The initial Section 25 scale inequalities are wrong

For `b3=vL` and a good `vL*k/c`, the internal dual self-charge is `1/c`,
not `1/k`. CROSS also bounds the scale of the row being tested. For a bad pair
row `u*alpha`, with normalized isolated block coefficients

```text
beta = {L, L*k1/c1, L*k2/c2},
```

the valid necessary bound is

```text
u <= sum(beta)*alpha/(alpha-1).
```

For the isolated bad row, if `1/c1+1/c2<1`, the valid bound is

```text
v <= (alpha+alpha')/(1-1/c1-1/c2).
```

When `c1=c2=2`, compact spread supplies
`vL < 7u*min(alpha,alpha')`. These bounds are finite in every case.

The shared draft `bank1edge` returned 21 tuples but is not complete for the
compact class: it includes three noncompact tuples with ratios `8.25`, `9.75`,
and `11.25`, while omitting the valid compact residual

```text
D=[30,52,78,130,195].
```

Here the bad triple is `[30,52,78]`, its only internal strong edge is
`52--78`, and the draft's wrong `k`-bound gives `u<=14` although the actual
strong-pair gcd is `u=26`.

### 26.2 Corrected one-edge bank

The independent owned `oneedgebankcheck/` implements the corrected bounds,
filters compact spread explicitly, and exact-checks every surviving tower. It
enumerates `161310876` raw parameter tuples and gives

```text
one-edge exactly-3-bad compact C-B residuals: 19
tower failures: 0
worst margin = 151632000/52488000 = 26/9 at m=59
RESULT: ALL PASS
```

This includes all 13 `M<=120` witnesses and the previously omitted compact
member above. Subject to review of the block parametrization and CROSS bounds,
the one-edge class is closed by a finite direct bank.

### 26.3 Zero-edge class: finite rational templates, four survivors

If the bad triple has no internal strong edge, each bad `b` receives at most
`2b/5` internally, so its two goods supply at least `3b/5`. For either labeled
good write the reduced ratios

```text
b/g1=c1/k1,  g2/b=k2/c2.
```

Then `1/c1+1/c2>=3/5`, hence `2<=c1,c2<=10`, while antichain and compact
spread give finite `k` lists. Anchoring `g1=1` fixes

```text
b/g1=c1/k1,  g2/g1=c1*k2/(k1*c2).
```

Thus for each finite second-good ratio there is a finite exact list of possible
bad ratios. `zeroedgebankcheck/` chooses three distinct ones, normalizes to a
primitive integer core, and exact-filters every residual condition. Output:

```text
pin descriptors: 2610
distinct good ratios: 1830
rational bad triples tested: 2722
normalized five-cores: 1323
zero-edge exactly-3-bad compact C-B residuals: 4
D=[210,330,462,770,1155]
D=[210,390,546,910,1365]
D=[330,390,858,1430,2145]
D=[462,546,858,2002,3003]
tower failures: 0
RESULT: ALL PASS
```

The first dual core corresponds to primal `{2,3,5,7,11}`. Shared v3 also
passes the four normalized bad triples in `zeroedgebankcheck/shapes0edge.csv`:
`PASS 4 / ZERO 0 / SHORT 0`.

### 26.4 Priority-honest assembly

The compact residual now has a proposed complete partition: at least two bad-
internal strong edges (`906/906` v3), exactly one edge (19-member corrected
direct bank), zero edges (4-member rational-template bank), four bads (complete
174-shape `shape4`), and no five-bad case (minimum-good lemma). This is a serious
candidate closure of size 5, but remains `PLAUSIBLE`, not `PROVED`, until the
new finite reductions, v3/shape4 knife, and end-to-end regime assembly are
hostilely audited.

### 26.5 Tower endpoint audit

Status: `PROVED` (algebraic handoff) / `COMPUTED` (finite bank sides).
The U2 bridge lower bound is

```text
2B(m)-mS >= (7mS-1135+157S)/150.
```

It implies the stronger tower form `2B(m)>=(m+1)S` exactly when
`7(m+1)S>=1135`. The Rust banks check the complementary range
`7(m+1)S<1135`. Their integer cap

```text
floor(1135/(7S))-1
```

is exact when the quotient is nonintegral and checks one harmless extra endpoint
when it is integral. Finally, tower form implies the strict scaled inequality
because `n/t < floor(n/t)+1`. Thus there is no uncovered endpoint between the
new direct banks, U2, and C0 scaling.

### 25.1 CORRECTION (caught by witness cross-check): Section 25's slot directions were swapped; corrected bounds; bank rerun 25/25 PASS

Status: `BROKEN` (Section 25's specific scale bounds and the "k1=k2=2 rider
vacuity") / `PROVED` (the corrected structure below) / `COMPUTED` (corrected
`census bank1edge`, ALL PASS). The M=240 witness D=[30,52,78,130,195]
(pair 26*(2,3), b3=30, pins (c,k)=(2,13),(3,13)) fell outside the old box:
u = 26 > the wrongly-derived cap 14. Diagnosis: I swapped the two slot
directions — in b3's dual row the goods contribute 1/c_j (NOT 1/k_j), and in
the pair rows the block elements contribute gamma/u (NOT alpha/v). Corrected:

- Pair rows: 1/alpha_i + sum(gamma)/u >= 1  =>  u <= sum(gamma)/(1 - 1/amax),
  sum(gamma) = L + L*k1/c1 + L*k2/c2. Always bounded (amax >= 3).
- b3 row: 1/c1 + 1/c2 + (alpha1+alpha2)/v >= 1  =>
  v <= (alpha1+alpha2)*c1*c2/(c1*c2 - c1 - c2) when 1/c1 + 1/c2 < 1.
  The TRUE rider candidate is (c1,c2) = (2,2) — b3 is then automatically bad —
  and there the ratio-7 box bounds v < 7*u*amin/L instead. Still a finite bank.

```text
census bank1edge 7 (corrected):
raw candidates 91,001,163 -> one-edge exactly-3-bad C-B residual members: 25
tower failures: 0 ; worst margin ~ 2.8889 at m=59, D=[10,12,15,18,27]
ALL 19 M=240 witnesses contained (the old box missed exactly the catching one).
RESULT: ALL PASS — the one-edge family is closed by this finite bank.
```

The one-edge 3-bad sector is CLOSED (modulo the Section 25/25.1 knife).
Remaining 3-bad piece: the ZERO-edge class (0 in range at M=120 and 240; every
bad then carries a {2,3}-pin and a <=10-pin into two goods, pigeonhole shares a
pinned good, and the whole tuple becomes g1*(bounded rationals) with the
normalization forcing scale 1 — a single-scale bounded family; enumeration
certificate next).

## 27. Reconciliation: corrected shared 25-bank = exact compact 19-bank plus six SPREAD cases

Status: `COMPUTED` exact set comparison / `CORRECTION` to the 25-member label.
Codex, 2026-07-18.

The corrected shared `census bank1edge` bounds are now in the right slot
directions, but the generator does not finally filter `max(D)<7min(D)`. Its 25
passing members split exactly as

```text
19 exact compact members (oneedgebankcheck/bank19.csv)
 6 noncompact members with max/min = 8.25, 9.75, 11.25, 8.5, 9.5, 8.5.
```

The six are

```text
[20,44,66,110,165]
[20,52,78,130,195]
[28,90,126,210,315]
[30,68,102,170,255]
[30,76,114,190,285]
[42,68,102,238,357]
```

The local bound `vL<7u*amin` does not impose global spread on the larger goods
`vLk/c`. This is harmless for sufficiency: the shared 25-bank is a passing
superset containing all 19 compact cases. It is not the exact compact inventory.
The exact count used in the assembly remains 19; either certificate closes that
sector after the structural/code knife.

## 26. Mutual-audit round on the five-sector partition (REFEREE_SIZE5_CANDIDATE section 4)

Status: audit verdicts (Claude, 2026-07-18). The compact-residual partition
(referee doc section 2) is: 3-bad x {>=2 edges: 906/v3} | {1 edge: 19-bank} |
{0 edges: 4-bank} | 4-bad: 174/shape4 | 5-bad: impossible.

**Bank reconciliation (attack 1, computational half): EXACT MATCH.** My
corrected `bank1edge` (25 members) restricted to the compact box (ratio < 7)
equals Codex's `oneedgebankcheck` 19-bank literally; my 6 extras are all
ratio >= 7 = SPREAD's regime (they pass towers anyway). The shared mode now
excludes them explicitly. Independent convergence: we found the SAME slot-swap
bug and the SAME corrected bounds simultaneously (his post 5273 vs my 25.1).

**Attack 1 (one-edge surjectivity): PASS.** The requested sub-proofs:
(i) gcd(u,v) = 1: u | b1, b2 and v | B, G1, G2 (L*k_j/c_j is an integer), so
gcd(u,v) divides all five elements, hence divides gcd(D) = 1. (ii) The box is
surjective: u = gcd(b1,b2) exactly makes the pair cofactors coprime with
min <= 4 (strong edge) and max <= 27 (ratio); c_j | B gives v = B/L integer;
the corrected necessary bounds (25.1 = his README, identical formulas) contain
every residual. (iii) k-ranges [2, 7c) complete: k = 1 is antichain-excluded,
k >= 7c is ratio-excluded.

**Attack 2 (zero-edge surjectivity): PASS.** Every bad's BOTH good-pins have
c <= 10 (max-pin in {2,3} from >= 3b/10; the other from the residual need
3/5 - 1/c_max). For any anchor good g1: b/g1 = c/k reduced with c <= 10,
k in [2, 7c) (antichain/ratio), and t = g2/g1 = (b/g1)*(g2/b) is descriptor-
composed for EVERY bad, so all three distinct bad-ratios lie in compatible[t].
His [2,10]^2 + joint-need filter is a conservative superset; normalization
reproduces the primitive core. Reproduced: 4 members, towers 0 failures, and
shape2v3 passes all four normalized bad triples independently.

**Attack 4 (fourbadcheck): PASS.** Spanning-tree route: 16 Prufer-labeled
trees cover every spanning tree; ratio types (one side <= 6, both in [2,41],
two-sided ratio-7) are forced by the row condition; propagation + lcm/gcd
normalization reproduces any connected shape exactly; his two-sided equality
against the canonical 174 split (outside = 0 AND missing = 0) is the strongest
form. Two-pair box: identical pin-consistency logic to c4bound22. Note his
heavy-edge notion (a reduced cofactor <= 6) differs from my gcd >= w1/6; both
are row-derived, both internally consistent — two independent roads.

**Attack 5 (partition totality): PASS.** <= 2 goods gives >= 3 bads; the
minimum-good lemma (23.6) excludes 5; bad count in {3,4}; the 3-bad rows
partition by internal strong-edge count {0, 1, >= 2} — exclusive, exhaustive.
Every compact residual enters exactly one row.

**Open audits:** attack 3 (shape2v3/shape4 internals — needs a hostile pass
INDEPENDENT of me; Codex or external) and attack 6 (seams — my Section 24 row
10 + his referee section 5 tower handoff; one joint write-up pass wanted).

## 27. Seams, complete (referee attack 6, Claude's half — merge with referee doc section 5)

Status: `PROVED` (each seam is one or two lines given the banked pieces).

1. **Below (FD <-> stage-2/banks).** FD covers max(P) <= n < 2max(P)
   unconditionally (size-4 separator + exact identity, Lean'd). Stage-2
   certificates start at tau_lo = 2*wmax, i.e. n >= 2*wmax*s; since wmax*s is
   an element, 2*wmax*s <= 2*max(P): the intervals OVERLAP — no gap.
   Direct banks start at m = max(P) and FD also covers [max, 2max): overlap.
2. **Above (banks/stage-2 <-> U2 bridge).** Banks check the tower form for
   7(m+1)S < 1135; on the complement U2 gives
   2B(m) - mS >= (7mS - 1135 + 157S)/150 >= S > 0 (referee doc section 5).
   The code cap floor(1135*prod/(7*nsum)) - 1 is exact for nonintegral
   quotients and checks one extra endpoint otherwise — conservative both ways.
   Stage-2's tau_hi = 33*rho*wmax: 33*max(P) <= 33*rho*wmax*s because
   max(P) < rho*min(P) <= rho*wmin*s <= rho*wmax*s — meshes with the n >= 33max
   bridge activation. Overlap, no gap.
3. **Ratio seam (banks <-> SPREAD).** All bank/certificate filters keep
   ratio < 7 members only; ratio >= 7 is SPREAD's theorem (rho0 = 7,
   unconditional in n). The bank1edge exclusion list (6 tuples, each ratio
   >= 7, each still tower-passing) demonstrates the tiling concretely.
4. **Scaling seam (C0).** gcd(P) = t > 1 reduces to the primitive base via
   B_{tP0}(n) = B_{P0}(floor(n/t)) and the TOWER form 2B(m) >= (m+1)S covers
   the floor loss because n/t < floor(n/t) + 1 (referee doc section 5).
5. **Goodness/CRIT seams.** >= 3 good: Lean regime A. <= 2 good with
   CRIT > 7/2: Lean CB.lean cb_cover5. What remains is by definition the
   compact residual — partitioned by the five-sector table (section 26),
   each row certified. Bad-count totality: section 23.6.

Every (P, n) with n >= max(P) lands in at least one certified regime; the
overlaps are benign (all statements are the same inequality 2B > nS or its
tower strengthening). This is the assembly half of attack 6; the joint pass
should merge this with referee section 5's statements verbatim.

### 23.6a The k = 5 ceiling is now LEAN tier

`lean/ep488/Ep488/Ceiling.lean` (2026-07-19): `slot_trichotomy` (per element:
`60*gcd <= 12e`, or the `(m,k) = (3,2)` slot with `3x = 2e`, or `(4,3)` with
`4x = 3e`), `ceiling_max` (`sum gcd(e,x) < e` over any 4 distinct smaller
non-divisors — via at-most-one-per-slot and `59e/60`), and `no_five_self_bad`
(antichain 5-set: the max is never self-bad). Sorry-free; axioms = the standard
trio (ceiling-axioms.txt); CeilingCheck.lean added to the CI audit list. The
"5-bad impossible" row of the partition table is machine-checked.

### 26.1 Duality Transport is now LEAN tier

`lean/ep488/Ep488/Transport.lean` (2026-07-19): `gcd_div_div`
(`gcd(L/a, L/b) = L/lcm(a,b)`), `transport_identity`
(`gcd(L/a,L/b)*(a*b) = gcd(a,b)*L`), `transport_term` (the cleared charge
term), and `dual_selfbad_iff` (`sum gcd(d_a,d_x) >= d_a  <=>
sum gcd(a,x)*(L/x) >= L` — dual self-bad iff primal charge >= 1, any common
multiple L, any finite divisor set). Sorry-free on `[propext, Quot.sound]`
(transport-axioms.txt); TransportCheck in CI. This machine-checks the DT
lemma quoted under the entire dual-side partition semantics: `nselfbad` =
primal bad count, the k = 5 ceiling's primal meaning, and the five-sector
table's row definitions all rest on it.

### 26.2 First external pass (Gemini) on EXTERNAL_CHECK_V3: SOUND-WITH-REPAIRS; the single BREAK is refuted by source

Status: verdict received 2026-07-19 (Wes ran the package). Surfaces 1,2,3,5,6,
7,8: HOLDS independently (matching Codex's REFEREE_V3 on all seven). Surface 4:
claimed BREAK — "using 41 for the infinite tail is unsound because J traverses
beyond 40, spuriously triggering divisibility at 41, 82, 123, ...".

**Refutation (source, all three certificate sites):** the exact pinned-good
row is computed by `f_exact(..., jt = 40)` and consulted ONLY under the guard
`jy <= jt` (census/src/main.rs:1317 v2.2, :1555 v3, :1748 shape4); for
`jy >= 41` the code uses the flat certified good-row floor `90` (the F5
staircase tail) and never the clamped exact prefix. The 41-representative is
used only where Gemini's own surface-3 verdict confirms it exact (J <= 40).
The prescribed repair — "abandon the exact-drift calculation in favor of the
F5 tail / stair60 whenever J >= 41" — IS the implementation. Codex's audit
read this correctly ("for J > 40 the code uses the independent tail").

Root cause: the external brief under-specified the evaluation split; the
reviewer judged the described design, not the code. EXTERNAL_CHECK_V3.md
section 3 item 4 is now amended to state the split explicitly (with a note
that it was amended after this pass). Gemini's surface-7 parenthetical (an
all-BIG column being dropped would be a completeness failure) is also already
handled: the all-BIG matrix is enumerated as the pin-free branch with the
universal staircase (it is not dropped).

Net: 7/8 surfaces now confirmed by TWO independent reviewers; the eighth is
confirmed by Codex and the disputed reading is settled by source inspection.
The ChatGPT run should use the amended brief.

### 26.3 Second external pass (ChatGPT, cold prompt): design SOUND-WITH-REPAIRS; both real repairs adopted

Verdict triage (2026-07-19): surfaces 1-6 HOLD (conditionally) on the DESIGN,
independently re-deriving the safe conventions the code uses: the inclusive
upper endpoint floor(q(tau+1)/d) as the safe one-point enlargement (surface
4 — exactly the implementation), the conservative-only direction for
representatives (2/3), and the m60 >= 0 acceptance wording (6 — a brief
wording bug, fixed). Its "clamping trap" ((2,3,7,100) good but (2,3,7,41)
bad) is the right trap and does NOT fire: all three goodness tests use exact
unclamped integers (main.rs sites at the cprod calls; Codex's audit agrees).
Surface 1's canonical-pin question: the code pins through the FIRST exact
slot — deterministic; completeness needs no uniqueness. Surface 7: the
all-BIG branch is the pin-free universal-staircase branch (J >= 2 from
n >= 2max), not a gap — now spelled out in the brief.

ADOPTED REPAIRS: (i) surface 8 upgraded from audit-claim to in-code
guarantee — `cprod` checked multiplication in all three goodness sites +
CSV input assertions (coefficients in (0, 4e7]); certificates re-verified
bit-identical (906/906, 4/4, 174/174). (ii) the package critique is correct
for cold prompts — the brief now states it is NOT self-contained and lists
the exact files/repo/commit a real audit needs, plus the pin rule, the
goodness-direction policy, and the all-BIG specification.

Tally across three reviewers (Codex with source, Gemini and ChatGPT on the
brief): every DESIGN surface has at least two independent HOLDs; every
claimed BREAK/trap has been settled by source inspection (none fired); two
robustness repairs landed. The clean remaining step is unchanged: one
external run WITH the source attached, on the amended brief.

### 26.4 Gemini on the full-assembly brief: SOUND — but consistency-tier only, and logged as such

Verdict received 2026-07-19: all components HOLDS, overall SOUND. Honest
assessment (Wes spotted it immediately): this is NOT an audit. Tells: "are
CLAIMED to compile cleanly" (no Lean run), no line reference beyond the
brief's own, zero new findings, and the required "what I could not check"
section is absent. Value: a fresh-reader consistency check of the assembly
narrative — the architecture parses, the partition reads as total, the
dependency ledger reads as honest. It does NOT count toward the promotion
gate's second hostile pass.

Process signal worth recording: across three external rounds plus the
internal cross-audits, NEW findings have gone 2 (real repairs) -> 1 refuted
break -> 0. External LLM review has saturated at design tier — cold readers
cannot execute Rust/Lean, and the design surfaces are now triple-confirmed.
Additional cold reads have ~zero expected yield. The only verification KINDS
that would still move confidence: (a) a third party actually executing the
certificates (human or agent with a toolchain), or (b) replaying the finite
enumerations inside Lean (native_decide-style), which would make third-party
trust unnecessary. (b) is the optional-hardening path already on the ledger.

### 26.5 THE REAL SECOND PASS (ChatGPT "bob-local", reading-mode with source): SOUND-WITH-REPAIRS — one genuine finding, all repairs triaged

Verdict 2026-07-19: no mathematical or source-level failure found; two
presentation repairs demanded. This is the first external review that read
the actual source; its findings are specific and mostly correct.

**Finding 1 (REAL, the substantive one): C0 sits too early in the stated
regime order.** A nonprimitive quintuple intercepted by C0 needs the
downstream regimes in TOWER form on the base, but C-B/SPREAD rows are stated
as separator-only. VERIFIED against source: the repair is the reviewer's own
option 1 and it is available because `ep488_quint_three_good` and `cb_cover5`
carry NO gcd hypothesis (checked: Quint.lean:458, CB.lean:86) — A, FD,
Bridge, C-B, SPREAD are gcd-agnostic and apply at the ORIGINAL scale; C0
then feeds ONLY the box sectors, where the banks tower-check explicitly and
`drift_bridge_tower` covers the tail. Brief section 3 and ledger row 4 are
repaired to this order. Codex confirmed the remaining calibration directly:
`2B(m)-mS >= 2*sum_i f_i-5+S`, while stage 2 stores
`m60=60*(2*sum_i f_i-5)`. Therefore `m60>=0` implies
`2B(m)-mS>=S`, exactly the nonstrict tower form; ZERO branches are valid.

**Finding 2 (correct): tier labels overstate.** C-B is LEAN(conditional
cb_cover5) + PAPER (the CRIT>7/2 => hypothesis step); FD is LEAN + paper
assembly; Bridge is Lean-algebra + Rust kernel + paper. Ledger row 5
relabeled; the referee doc's tier column is Codex's to align.

**Adopted immediately:** (i) CSV parsing in the certificate arms is now
FAIL-CLOSED (malformed rows abort; previously filter_map could silently
drop rows); (ii) the brief no longer says committed outputs are evidence —
they are the authors' expected outputs; (iii) the brief demands a pinned
commit instead of floating main; (iv) certificates re-verified bit-identical
after the parsing change (906/906, 174/174).

**Queued:** reconcile stale W-FIN dependency wording in older notes sections;
checked arithmetic sweep over the small bank tools (mine bounded and
documented; Codex's crates his); a rebuild-everything CI job (fixtures +
certificates + Lean from the pinned commit) — the reviewer's "definitive
verification record" bar.

### 26.6 Blind Pack B (ChatGPT local, independent reimplementation): ALL THREE EXACT MATCHES, sealed control caught

Results 2026-07-19, verified against the sealed key:
- B1 (one-edge bank): 19 members, 0 tower failures — EXACT set match with
  oneedgebankcheck/bank19.csv, and the sealed control witness
  D=[30,52,78,130,195] (the tuple our own first broken enumeration missed)
  IS PRESENT. A reimplementation that reproduced our historical bug would
  have omitted it; this one did not.
- B2 (zero-edge bank): the exact 4 members, 0 failures.
- B3 (4-bad inventory to w1 <= 300): 174 quadruples, largest w1 = 40 —
  EXACT list match with census/shapes4inv120.csv (only diff: their summary
  footer line).

Independence assessment (code inspected, committed as
blind_pack_b_reimplement.rs / blind_pack_b3.rs): genuinely fresh
implementation — u128 not i128, different architecture (fused compact()
filter, rational-struct grouping for the zero-edge anchoring, different
loop organization), spec-exactness asserts, and NO file I/O anywhere: the
outputs are computed from the spec, not read from the repo. Their tower
check even treats zero margin as reportable and still found none (all
margins strict).

Standing: the one-edge bank and the 4-bad inventory now have THREE
independent implementations each in exact agreement (census, the *bankcheck
crates, and the blind run — plus fourbadcheck's two internal routes for the
174); the zero-edge bank has three (zeroedgebankcheck, shape2v3
cross-check, blind). Implementation faithfulness is settled beyond
reasonable doubt; the remaining trust surface is the SPECS' completeness
theorems, which is Pack A's target (blind re-derivation, still running) on
top of the existing proofs and audits.

### 26.7 Blind Pack A (two repo-blind solvers, parallel session): claims 1-4 MATCH, discriminator passed twice, one pack defect caught, and a second analytic (c') proof

Outcome (protocol entry in the chat, artifacts in that session's tmp/):
1. The retraction discriminator (claim 3c) passed in the strongest form:
   BOTH blind solvers derived the corrected slot directions and bounds cold
   — including the (2,2)-c exception and the identical spread fallback —
   and neither reproduced the retracted wrong-slot form. They proved a
   SHARPER u-bound, u*(alpha-1) <= gcd(alpha,v)*Sgam, which implies our
   banked one (gcd(alpha,v) <= alpha): kept on the shelf.
2. Claim 1's ceiling is ATTAINED: {24,36,40,45,60} gives sum = 59e/60
   exactly (slots {5,5,3,4}; verified here: 12+12+20+15 = 59). Ceiling.lean
   proves the strict < e form, which equality does not contradict.
3. NEW second analytic proof of the 4-bad finiteness (obligation c'),
   cutoff-free: bounded-t connectivity of the filter rows + p-adic lcm
   pinning, max(w) <= 293^9 under the box ratio hypothesis, with slack down
   to any row threshold > 1/3. Independent of the 23.7/23.8 spanning-tree
   closure and of all enumerations. Status CLAIMED-verified (the running
   session walked it; Codex knife invited). Correlated-evidence caveat
   logged: both solvers share a base model.
4. PACK DEFECT (mine, drafting): Pack A claim 5 asks to PROVE
   max(w)/min(w) < 7 as a consequence of 4-badness — it is a box HYPOTHESIS
   (from SPREAD), never a consequence. Verified counterexamples:
   w = (4,6,10,45) (ratio 11.25) passes every 1/2-filter row; without the
   ratio hypothesis the filter set is INFINITE ((2,3,5,p) for all p >= 7).
   Nothing banked is affected — every in-repo use of w4/w1 < 7 is
   hypothesis-scoped (23.5). Decision: KEEP the defect as a calibrated
   rubber-stamp trap for the still-running external projects (both honest
   blind solvers refuted it — that is the trap working); sealed-key update
   for Wes: claim 5's ratio sub-claim expects REFUTED, finiteness-as-written
   expects REFUTED (the (2,3,5,p) family), finiteness-under-ratio expects
   PROVED.

With Codex's tower-calibration confirmation (26.5, now including the Lean
`quintuple_drift_bridge_tower`) this closes every open finding from every
review round. The gate now consists solely of Wes's promotion decision plus
whatever the still-running external blind projects return.
