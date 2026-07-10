# C-B-FIN: structure notes — duality transport, junk rays, and the 3-component sector

Status: `THEORY PASS` (Claude, 2026-07-10; no new computation — pure
lemma/reduction work expanding Codex's strong-gcd component reduction of the same
date, see his chat entry "C-B-FIN collapses to one three-component obstruction").
Tiers marked per claim. Companion to `quintuple_density_notes.md`
("The C-B reorganization") and `lean/ep488/Ep488/CB.lean`.

Throughout: `D = {d_1 < … < d_5}` is a **dual core** (divisibility antichain,
`gcd(D) = 1`; the primal is `P = lcm(D)/D`), `G_i := Σ_{j≠i} gcd(d_i,d_j)`,
element `i` **self-bad** iff `G_i ≥ d_i` (⟺ primal `charge(P_i) ≥ 1`),
`Sg := Σ_{i<j} gcd(d_i,d_j)`, `N := ΣD − 2Sg`, `CRIT = N/d_1`.
**Residual** := `≤2` co-good (`≥3` self-bad) + window (`7ΣD ≤ 1135·d_1`) +
`CRIT ≤ 7/2`. `C-B-FIN` = "the residual is finite" = the last open piece of
size-5 #488.

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
  `gcd(a,b)/a + gcd(a,c)/a + gcd(b,c)(1/b + 1/c) ≥ 2` (after dividing by `b`,`c`
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

**Scope gap (important, found this pass).** Lemma JR handles rays that scale
**one** element. It does **not** cover **shared-scale rays**: multiply a common
factor `g` into *two* components simultaneously (e.g. the block-scale `t₁` and a
singleton `t₂` both carry `g → ∞`, `g` coprime to the rest). Along such a ray
every pairwise gcd **inside the pair grows linearly with `g`**, so `N` and
`d_min` grow proportionally and `CRIT` tends to a **finite limit** — such rays
are *not* self-retiring by JR. This is precisely the structure that Codex's
strong-gcd components capture (a shared scale is a strong edge or a coupled
component pair), and it is why the component framework, not single-element
essentiality, must be the master frame for C-B-FIN. The "essential core"
reduction of the workflow is therefore **subsumed, not load-bearing**.

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
