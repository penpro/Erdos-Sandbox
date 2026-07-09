# Size-5 density inequality `2δ > S` — a (near-complete) proof structure

Status: `COMPUTED` / `PROOF-SKETCH` / `ONE-LEMMA-SHORT` (Claude, 2026-07-08).
This is the asymptotic backbone of Erdős #488 at `|core| = 5`. Companion to the
size-≤4 charge development in `lean/ep488` and to Codex's separator census in
`adversary_collab_chat.md`.

## The claim

For a primitive quintuple `P = {a,b,c,d,e}` (a `∣`-antichain of integers ≥ 2), let
`M(P)` be its set of multiples, `δ = δ(M(P))` the asymptotic density, `S = Σ 1/x`.
By inclusion–exclusion `δ = S − P₂ + T₃ − T₄ + T₅` where `Pₖ = Σ_{k-subsets} 1/lcm`.
So

```
2δ − S = S − 2P₂ + 2T₃ − 2T₄ + 2T₅.
```

**Target:** `2δ > S` for every primitive quintuple. (This is the large-`n` half of
`2B(n) > nS`, since `2B(n)/n → 2δ`; small `n` is a separate finite check.)

Why it's the right target: `2δ > S` is *not* universal for all sizes — it fails for
large cores (25-element `{2p : p ≤ 100}` has `2δ < S`). But computation says it holds
at size 5, and it is floor-free (pure reciprocals + lcms), so it is the clean
provable object.

## The proof structure (three moves)

**Move 1 — scale invariance.** `M(tP) = t·M(P)`, so both `δ` and `S` scale by `1/t`;
hence the **sign of `2δ − S` is scale-invariant**. It suffices to prove `2δ > S` for
`gcd(P) = 1` base shapes.

**Move 2 — the sparse regime (two-term Bonferroni).** The truncated
inclusion–exclusion is a lower bound: `δ ≥ S − P₂`. Therefore

```
S > 2P₂   ⟹   2δ ≥ 2(S − P₂) = 2S − 2P₂ > S.
```

Equivalently (a charge identity) `S − 2P₂ = Σ_x (1 − charge(x))/x`, where
`charge(x) = Σ_{y≠x} gcd(x,y)/y`. So the sparse regime is "weighted-average charge
< 1". **For quadruples this always holds; for quintuples it can fail** — the residual
is exactly the sets with `S ≤ 2P₂`.

**Move 3 — the residual is a finite list (the key computational finding).** Over
**all 1,986,944 gcd=1 primitive quintuples with entries ≤ 58**, the sets with
`S ≤ 2P₂` are **exactly three**:

| base shape | `S − 2P₂` | `2δ − S` (exact) |
|---|---|---|
| `{4, 6, 9, 10, 15}`   | −0.0389 | **7/36**  ≈ +0.194 |
| `{4, 6, 10, 14, 15}`  | −0.0024 | **11/60** ≈ +0.183 |
| `{12, 18, 20, 30, 45}`| −0.0111 | **4/45**  ≈ +0.089 |

Each has `2δ − S > 0` (the `+2T₃` triple-overlap correction beats the small `S−2P₂`
deficit). A cross-check within `{2,3,5,7}`-smooth numbers (elements up to 140 — which
covers the high-overlap candidates that could possibly be residual) also returns
**only these three**. No residual set appeared with max entry > 45.

**Conclusion (conditional):** every `gcd=1` primitive quintuple is either sparse
(`S > 2P₂`, Move 2 ⟹ `2δ > S`) or one of the three residuals (Move 3, checked
`2δ − S > 0`). With Move 1, `2δ > S` for **every** primitive quintuple. ∎ — *modulo
the one remaining lemma below.*

## The Boundedness Lemma — status: STRONGLY EVIDENCED, proof OPEN

> **Boundedness (conjecture).** The `gcd=1` primitive quintuples with `S ≤ 2P₂` are
> exactly the three above. Evidence: exhaustive over entries ≤ 58 (~2M sets) and all
> `{2,3,5,7}`-smooth quintuples with max ≤ 210 — nothing else appears.

**⚠ A clean proof is NOT in hand — the natural one fails.** The tempting argument
(below) bounds `max` using a positive lower bound `m₁` on `S−2P₂` over gcd=1
quadruples. **But `m₁ = 0`:** `min(S−2P₂)` over gcd=1 quads *decreases without
bound* — 1/30, 11/360, 1/42, 2/105, … — minimized by the "product-of-3-of-4-primes"
family `{60,70,84,105}, …`, whose `S−2P₂ → 0`. So `e ≤ 3/m₁` gives no bound. The
finiteness of the residual is therefore **empirical, not proved.**

Reassurance that it is nonetheless plausibly finite: the analogous
"product-of-4-of-5-primes" quintuples `{210,330,462,770,1155}` (primes 2,3,5,7,11),
`{1155,1365,2145,3003,5005}` (3,5,7,11,13), … — the natural candidates for an
*infinite* residual family — all have `S−2P₂ > 0` (they sit just inside the **sparse**
regime: +0.0035 → +0.0004) and `2δ−S > 0` (+0.0087 → +0.0005). So they are covered by
Bonferroni and are **not** residuals; the residual `S ≤ 2P₂` seems to require the
"extra-clustered" balance only small sets achieve. A real finiteness proof needs a
sharper argument than the `m₁` bound.

**Corollary for the density inequality:** `2δ > S` is asymptotically **tight on two
different families** — consecutive runs `{a,…,a+4}` and the product-of-primes
quintuples — both with margin `→ 0`, both in the sparse regime. Any eventual proof
must survive both.

<details><summary>The failed bound (kept for the record)</summary>

Write `P = Q ∪ {e}`,
`e = max(P)`, `Q` the four smaller elements (a primitive quadruple). Splitting off
`e`'s contribution to `S − 2P₂`:

```
S(P) − 2P₂(P) = [S(Q) − 2P₂(Q)]  +  (1/e)·(1 − 2·charge_Q(e)),
   charge_Q(e) := Σ_{y∈Q} gcd(e,y)/y.
```

By primitivity `y ∤ e`, so `y/gcd(e,y) ≥ 2`, i.e. each `gcd(e,y)/y ≤ 1/2`; over the
four `y∈Q`, `charge_Q(e) ≤ 2`. Let **`m₁ := min over gcd=1 primitive quadruples of
(S − 2P₂)`** — this is `> 0` and bounded below (only *clustered small* gcd=1 quads
minimize it; large-entry gcd=1 quads are near-coprime with `S − 2P₂ ≈ S > 0`).
Verified `m₁ = 1/42` over gcd=1 quads with entries ≤ 90.
*(NB — earlier draft mistakenly used the min over ALL quads, which is 0 by scaling;
the gcd=1 restriction is essential and is what makes the bound work.)*

Two cases.
- **`gcd(Q) = 1`.** Then `S(Q) − 2P₂(Q) ≥ m₁`, and `1 − 2·charge_Q(e) ≥ −3`, so a
  residual (`S(P)−2P₂(P) ≤ 0`) forces `m₁ ≤ S(Q)−2P₂(Q) ≤ 3/e`, i.e. `e ≤ 3/m₁ ≤ 126`.
- **`gcd(Q) = g ≥ 2`.** Since `gcd(P)=1`, necessarily `gcd(e,g)=1`; writing `y = g·y'`,
  `gcd(e, g·y') = gcd(e, y')`, so `charge_Q(e) = (1/g)·Σ gcd(e,y')/y' ≤ 2/g ≤ 1`. Also
  `S(Q) − 2P₂(Q) = (1/g)(S(Q/g) − 2P₂(Q/g)) ≥ m₁/g`. Residual then forces
  `m₁/g ≤ (1/e)(2·charge_Q(e) − 1) ≤ (1/e)(4/g − 1) ≤ 4/(g·e)`, i.e. `e ≤ 4/m₁ ≤ 168`.

Either way `max(P)` would be bounded. **The flaw:** the step "`m₁ > 0` and bounded
below" is FALSE — `m₁ = 0` (min gcd=1 quad `S−2P₂` decreases to 0 along
`{60,70,84,105},…`), so `3/m₁` is not a real bound. Kept only to show the natural
approach and where it breaks.

</details>

**The real open problem** is a correct proof that `S ≤ 2P₂` forces a gcd=1 primitive
quintuple to have `max ≤ 45` (equivalently: the residual is finite). Strongly
evidenced; mechanism not yet identified. The subtlety it must respect: `min(S−2P₂)`
over gcd=1 `k`-sets has **infimum 0** already for `k = 4` (product-of-3-of-4-primes),
yet `S−2P₂` is never `≤ 0` for `k ≤ 4`; at `k = 5` it does dip `≤ 0`, but (apparently)
only for finitely many small sets. So a proof cannot be a crude "`min > 0` ⟹ bounded"
argument — it must use the sign, not the size, of the deficit.

## What this does and does not give

- **Gives:** a clean *reduction* of the size-5 density inequality `2δ > S` (the
  large-`n` half of #488) to **one** open lemma — that the `S ≤ 2P₂` residual is
  finite (empirically = 3 sets). The sparse regime (`S > 2P₂ ⟹ 2δ > S`) is a
  theorem; the 3-set check is arithmetic. It also explains *why* the flat pointwise
  charge proof (the `Y_H` weight table) fails for `≤2`-good sets: the deficit
  `S − 2P₂ < 0` on the residual must be repaid by `T₃`, invisible to first-/second-
  order accounting.
- **Does not give (yet):** (i) the Boundedness Lemma (finiteness of the residual);
  (ii) the small-`n` bridge — `2δ > S` is large-`n`; full `2B(n) > nS` for all
  `n ≥ max` still needs a finite per-set (or uniform) small-`n` argument. The margin
  is not uniform (→ 0 on consecutive runs `{a,…,a+4}`), so the small-`n` bridge may
  stay per-set.

## Lean formalization plan

The `≥ 3`-good case is already Lean-proved (`ep488_quint_three_good`). For the
density inequality: formalizing `δ` (asymptotic density) is a larger new development
than the finite `B(n)` machinery used so far. A lighter path: prove the **finite**
analogue directly — for the three residual base shapes (and their scalings via a
shared-factor recursion `B_{tP}(x) = B_P(⌊x/t⌋)`), certify `2B(n) > nS` on one period
with the existing `ep488_of_window` engine; combine with the sparse/`three-good`
regimes. That keeps everything at the `B(n)` level and avoids formalizing limits.

## Reproduce

```bash
# exact-fraction search (scratch scripts): min(2δ−S) over gcd=1 quintuples,
# and enumeration of the S≤2P2 residual (finite: exactly 3 up to entries 58).
python residual_hunt.py 58        # -> S<=2P2 residual = 3 sets
```
