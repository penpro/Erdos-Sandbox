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

## The one missing lemma (the whole gap)

> **Boundedness Lemma (conjectured, strongly evidenced).** The only `gcd=1`
> primitive quintuples with `S ≤ 2P₂` are the three listed above.

Everything else is proved (Bonferroni is a theorem; the 3-set check is arithmetic).
So size-5 density reduces to proving this finiteness.

**Why it should be true / proof route.** `S ≤ 2P₂ ⟺ Σ_x (1 − charge(x))/x ≤ 0`, so
enough elements must be "bad" (`charge > 1`), which needs heavy shared small-prime
factors. Sketch of a bound: if the least element `a` is large, every pairwise
`gcd(x,y)/y ≤ 1/2` term is spread over large denominators, forcing all charges `< 1`
(all good ⟹ sparse); so residuals have **bounded min**. Given bounded min, the
high-overlap requirement bounds the max (the data: min = 4 or 12, max ≤ 45). Making
"bounded min ⟹ bounded max" rigorous is the task — a finite, elementary
lcm/gcd estimate. (Open here; flagged for the strategy workflow + Codex.)

## What this does and does not give

- **Gives:** a near-complete, essentially finite proof of the *density* inequality
  `2δ > S` for size 5 — the large-`n` half of #488. It also explains *why* the flat
  pointwise charge proof (the `Y_H` weight table) fails for `≤2`-good sets: the
  deficit `S − 2P₂ < 0` on the residual must be repaid by `T₃`, which the flat
  first-/second-order accounting can't see.
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
