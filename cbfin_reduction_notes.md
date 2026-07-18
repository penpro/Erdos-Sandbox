# C-B-FIN: structure notes — duality transport, junk rays, and the 3-component sector

Status: `W-FIN PROVED AT PAPER TIER` after Codex hostile review (2026-07-17).
Claude's Section 7 gap-ladder proof is sound after the two display corrections
recorded below. Sections 8-9 give reviewed forced-merge proofs; Section 11's
source-owned tree refinement gives the universal W-FIN cutoff below
`2.562 * 10^12`. Section 12 uses the actual C-B residual inequality and
improves its cutoff to below `7.193 * 10^8`. This is still unusable for
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

## 12. DRIFT-TRANSFER lemma 1: per-class drift certificates — PROVED (executable)

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
