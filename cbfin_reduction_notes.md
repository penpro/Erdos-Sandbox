# C-B-FIN: structure notes — duality transport, junk rays, and the 3-component sector

Status: `W-FIN PROVED AT PAPER TIER` after Codex hostile review (2026-07-17).
Claude's Section 7 gap-ladder proof is sound after the two display corrections
recorded below. Section 8 gives a shorter threshold proof and a much smaller,
though still unusable, explicit cutoff. Full size 5 remains open because the
finite residual bank has not been extended to that cutoff.
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

## 9. Constant optimization v2 — the forced-merge process (CLAIMED: T ~ 10^22)

Status: `CLAIMED` (Claude/Fable, 2026-07-17; written concurrently with Codex's §8
review — same skeleton as §7/§8, different merge schedule). §8's three-level
stabilization gives `T ~ 10^102` (PROVED, reviewed). This section claims a further
drop to `T ~ 10^16–10^22` by tracking **per-edge qualities at merge time** (edges
merged early keep their good quality in the propagation product) instead of a
uniform level threshold. **Needs the same hostile review §7 received** — the
bookkeeping is more delicate than §8's. If it survives, the effective gap narrows
but remains: `10^22` is still beyond enumeration, so the honest endgame options at
the end of this section stand either way.

The ladder's tower came from an over-strong requirement: a single global heavy/light
threshold classifying all ten pairs at once (11-rung pigeonhole, quartic degradation
per rung). The merge process below never needs a global dichotomy — merges happen
only when *forced*, and the ceilings force them.

**Setup.** As in §7: `d := min(D)`, entries `≤ (R−4)d`, `R = 1135/7`, `≥ 3` self-bad
vertices, `gcd(D) = 1`. Write each edge quality as `g_e ≥ d/Y_e`. For a connected
component `C` assembled from tree edges `e_1, …, e_{k−1}` (attach order), the §7
propagation gives the common divisor

```
h_C ≥ d / Z_C,   Z_C := R^{k−2} · Π_i Y_{e_i}      (k = |C|).
```

**The process.** Maintain a partition of the 5 vertices into components, initially
built from the edges `≥ d/5` (every bad vertex has one, since its four gcds sum to
`≥ d_i ≥ d`; isolated vertices are self-good).

At each step, ask: *does every self-bad vertex `i` transfer* — i.e. is its
cross-component gcd-sum `< h_{C(i)}`? (Transfer = §7 Step 4: badness descends to the
cofactor antichain of `C(i)`.)

- **If yes (all transfer):** the ceilings (`k = 2,3,4` admit `≤ 0,1,2` self-bad,
  §1) cap the total self-bad count by the best partition value: `(4,1) → 2`,
  `(3,2) → 1`, `(3,1,1) → 1`, `(2,2,1) → 0`, `… → 0` — all `≤ 2 < 3`.
  **Contradiction; the process cannot in fact reach this branch with 3 bads, i.e.
  the alternative below is forced.** (Note the elegance: a bad vertex in a
  2-component can *never* transfer — the `k=2` ceiling is `0` — so 2-components
  holding bad vertices force merges automatically.)
- **If no:** some bad `i` has cross-sum `≥ h_{C(i)}`, so a single cross edge has
  `g ≥ h_{C(i)}/3`, i.e. quality `Y_new = 3·Z_{C(i)}`. **Merge** the two components
  it joins (all previously-used tree edges keep their qualities). The partition
  strictly coarsens.

Starting from `≤ 5` parts, at most **4 merges** occur before the partition is the
single component `{1..5}` — and then `h ≥ d/Z_{full}` divides `gcd(D) = 1`, forcing
`d ≤ Z_{full} =: T`. (Both terminal branches are contradictions for `d > T`, which
is the theorem.)

**The constant.** Tree-edge qualities compound as `Y_new = 3·R^{k−2}·ΠY_used`; the
worst merge chains (e.g. `{3,1,1} → {4,1} → {5}` or `{2,2,1} → {3,2} → {5}`) give

```
T = Z_full ≈ R³ · Π (4 tree-edge Y's)  ≈  10^16 – 10^22
```

depending on the chain (e.g. the `{3,1,1}` chain: `Y = 5, 5, 1.2·10⁴, 2.4·10¹⁰`,
`T ≈ 3·10²²`). Every step is explicit; the tower is gone (depth 4, not 11 rungs of
quartic decay).

**Honest endgame accounting.** With v2, if the proof survives review:
- `C-B-FIN` (and the stronger bounded-ratio statement) is **closed** — the class is
  finite with explicit `T ~ 10²²`.
- **Full size-5 is still not enumerable**: the bank must certify every residual core
  with `d ≤ T`, and `10²²` is beyond any census. The census evidence (all residual
  dual-mins `≤ 48` through `M = 240`) says the true `T` is tiny; the *proof* bound
  is the bottleneck. Two routes remain, either of which finishes size-5:
  1. **Shrink `T` to ~10³** — the slack is in the propagation loss `R` per tree edge
     (real cores have diameter-1 heavy graphs and near-uniform entry sizes; a
     size-aware propagation `h ≥ g²/d_u` on short paths, or replacing the generic
     `≥ d/5` seed by the bad vertex's `≥ d_i/4 ≥ d/4` with `d_i`-relative tracking,
     may cut each `R` factor to `O(1)`), or
  2. **A uniform residual window theorem**: prove directly that window + `≤2`-good +
     `CRIT ≤ 7/2` implies `2B(n) > nS` on `[2max, bridge)` — bank data (worst margin
     `22/9`, healthy across all 276 members) suggests real slack to work with; the
     `h_C` structure of residual cores (they are "almost `h·(small core)`") could
     feed the C0/tower reduction: a residual core with component divisor `h` behaves
     like a scaled small core plus `O(1)` junk, and scaled cores are already covered.
  Route 2 is the more promising mathematics: it would make the finiteness constant
  irrelevant entirely.

## 10. The effective gap: the DRIFT-TRANSFER program (route to closing size-5 without T)

Status: `PROGRAM` + one `PROVED` seed lemma (Claude/Fable, 2026-07-17). Goal: the
uniform residual window theorem — *window + `≤2`-good + `CRIT ≤ 7/2` ⟹ `2B(n) > nS`
on `[2·max, bridge)`* — which makes `T` (10^102 / claimed 10^22) irrelevant and
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
