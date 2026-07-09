# Size-5 density inequality `2δ > S` — PROVED (second-order charge)

Status: `PROVED` (`2δ > S`, the large-`n` half) / `NEEDS-REFEREE` / small-`n` bridge
open (Claude, 2026-07-08/09). This is the asymptotic backbone of Erdős #488 at
`|core| = 5`. The proof is the second-order-charge argument below (Strategy A of the
density workflow, Claude-verified end-to-end); it gives `2δ − S ≥ (7/150)·S` for
every primitive quintuple. Companion to the size-≤4 charge development in
`lean/ep488` and to Codex's separator census in `adversary_collab_chat.md`.

## Codex audit addendum (2026-07-09)

I rechecked the finite lemma driving the proof. The reduction to
`(2,2,3,5)` should be read as:

1. Replacing each modulus `m_i` by any prime divisor can only make the events
   `{m_i | N}` larger, so it can only decrease `E[1/(1+X)]`. Thus a minimizer is
   a 4-multiset of primes.
2. For a fixed prime multiplicity pattern, assign multiplicities to primes by
   pairing larger multiplicities with smaller primes. The exchange difference is
   `(alpha-beta)(h(Z+c)-h(Z+d)) <= 0` for `h(t)=1/(1+t)`, `c>=d`, and
   `alpha>=beta`.
3. The only five multiplicity patterns then give:

```text
(4)         -> (2,2,2,2):   3/5
(3,1)       -> (2,2,2,3):   8/15
(2,2)       -> (2,2,3,3):   8/15
(2,1,1)     -> (2,2,3,5):   157/300
(1,1,1,1)   -> (2,3,5,7):   6967/12600
```

So the minimum is exactly `157/300`, at `(2,2,3,5)`. Independent audit script:
`audit_quint_density_lemma.py`; `python audit_quint_density_lemma.py --brute 50`
also brute-forces all arbitrary 4-tuples of moduli up to 50 and finds no lower
value.

There is also a useful finite-`n` consequence. The density proof gives
`2delta-S >= (7/150)S`. Exact inclusion-exclusion for a quintuple has 16 positive
terms and 15 negative terms, hence `B(n) >= delta*n - 16`, so

```text
2B(n)-nS >= n(2delta-S)-32 >= (7/150)nS - 32.
```

Since `S >= 5/M` for `M=max(P)`, the raw separator `2B(n)>nS` holds uniformly
whenever `n >= 138M`. Thus the remaining size-5 separator work is confined to
the bounded relative window `M <= n < 138M`. This is not a size-5 proof; that
window still contains infinite families, including the consecutive-run
obstruction near `n=2a-1`.

The opposite end of the bounded window also has a simple proof. Let
`a=min(P)`. If `max(P) <= n < 2a`, then no generator has a second multiple yet.
Because `P` is primitive, the only counted multiples up to `n` are the five
generators themselves, so `B(n)=5`. Also

```text
nS < 2a * sum_{x in P} 1/x <= 10,
```

with strict inequality from `n<2a`. Hence `2B(n)=10>nS`. The consecutive
quintuples near `n=2a-1` are therefore the sharp model for this first window,
but not a counterexample source.

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

---

## THE PROOF (second-order charge) — `2δ > S` is settled

*This is the real proof (Strategy A of the density workflow, then verified by Claude
end-to-end with exact rationals). It is clean and uniform, and it supersedes the
"Bonferroni + finite residual" route below (which was stuck on an unproved
finiteness lemma). It gives the strict, quantitative bound `2δ − S ≥ (7/150)·S`.*

Think of `N` as ranging over the positive integers with natural density, and let
`R = R(N) = #{a ∈ P : a ∣ N}`. Then `δ = Pr(R ≥ 1)` and `S = E[R]`.

**Step 1 — the per-element identity.** Pointwise, `2·[R≥1] − R = Σ_{a∈P, a∣N} (2−R)/R`
(for `R=0` both sides are `0`; for `R≥1`, the RHS sums `R` copies of `(2−R)/R`).
Taking expectations and conditioning on `a ∣ N`:

```
2δ − S = Σ_{a∈P} Pr(a∣N) · E[(2−R)/R | a∣N] = Σ_{a∈P} (1/a) · (2·E[1/R | a∣N] − 1).
```

**Step 2 — reduction to four free moduli.** Condition on `a ∣ N` and write `N = a·M`
(`M` uniform). For any other `f∈P`, `f ∣ N ⟺ m_f ∣ M`, where `m_f := lcm(a,f)/a =
f/gcd(a,f)`; and `m_f ≥ 2` because `P` is a `∣`-antichain (`f ∤ a`). So, conditional on
`a∣N`, `R = 1 + X` with `X = #{f≠a : m_f ∣ M}`, and

```
E[1/R | a∣N] = E[ 1/(1+X) ]   over the 4 moduli m_f (each an integer ≥ 2).
```

**Step 3 — the finite lemma.** *For any four integers `m₁,…,m₄ ≥ 2`,
`E[1/(1+X)] ≥ 157/300`, where `X = #{i : mᵢ∣N}`.* Proof in four moves:
- **Explicit formula** (from `1/(1+X) = ∫₀¹ t^X dt`):
  `E[1/(1+X)] = Σ_{T ⊆ {1..4}} (−1)^{|T|} / ((|T|+1)·lcm(m_T))`. In particular
  `E ∈ [0,1]` and depends only on the divisibility structure.
- **Divisor-monotonicity.** If `m ∣ m'` then over any common period `{m'∣N} ⊆ {m∣N}`,
  so replacing `mᵢ` by a *multiple* only shrinks `X` pointwise and hence *raises* `E`.
  Replacing each `mᵢ` by a prime factor (a divisor `≥2`) can only *lower* `E`, so it
  suffices to prove the bound for **prime tuples**.
  *(Caution — this is the ONLY monotonicity available: it is divisibility-based, not
  size-based. "Smaller prime ⇒ smaller `E`" is FALSE, e.g. `E(2,2,2,5)=0.570 >
  E(2,2,3,5)=0.523`; the min is not all-2's.)*
- **Bounding the primes (independence).** For a prime `p` in the tuple coprime to the
  other entries (automatic when the others are different primes), `{p∣N}` is
  independent of the rest, giving
  `E = (1−1/p)·E[1/(1+X′)] + (1/p)·E[1/(1+μ+X′)]` (μ = multiplicity of `p`, `X′` counts
  the non-`p` entries) — **strictly increasing in `p`**. So a large prime in any slot
  only *raises* `E`; it cannot help the minimum. Concretely, **every prime tuple
  containing a prime `≥ 11` has `E ≥ 181/330 > 157/300`** (min at `(2,2,3,11)`), so the
  minimum lives among primes in `{2,3,5,7}`.
- **Finite check.** Over the 35 multisets of `{2,3,5,7}⁴`, `min E = 157/300` at
  `(2,2,3,5)`. ∎ (lemma)

  *Verified (`lemmaB.py`): (B1) min over `{2,3,5,7}` = 157/300; (B2) min over prime
  tuples containing a prime ≥11 (to 47) = 181/330; overall min over prime tuples
  (primes ≤47) = 157/300. Divisor-monotonicity: 0 counterexamples over 3000 trials.*

**Step 4 — conclusion.** By Steps 2–3, every element satisfies
`2·E[1/R | a∣N] − 1 ≥ 2·(157/300) − 1 = 7/150 > 0`. Plugging into Step 1,

```
2δ − S  =  Σ_{a∈P} (1/a)·(2·E[1/R|a∣N] − 1)  ≥  (7/150)·Σ_{a∈P} 1/a  =  (7/150)·S  >  0.
```

Hence `2δ > S` for **every** primitive quintuple. ∎

**Why exactly size 5.** The same argument at size `k` needs `min E[1/(1+X)]` over
`(k−1)`-tuples `> 1/2`. The minima are: size 4 → `41/72`, size 5 → `157/300` (both
`> 1/2`); size 6 → `49/100` at `(2,2,2,3,5)`, size 7 → `1931/4200` (both `< 1/2`). The
free-tuple minimum crosses `1/2` **precisely between `|P|=5` and `|P|=6`** — a crisp
explanation of why this method proves `2δ>S` for `|P| ≤ 5` and no further (and it
matches the pointwise `Y_H` weight going negative at size 6).

**Verified** by Claude with exact `Fraction` arithmetic: the identity holds on every
test quintuple; `min_e E[1/(1+X)] = 157/300` with **zero** violations over 399,230
primitive quintuples (entries ≤44); monotonicity has no counterexample; the finite
prime check gives `157/300`. Scripts in scratch (`verifyA.py`, `verifyLemma.py`).

**Honest scope.** This proves the *density* inequality `2δ > S` (the large-`n` half of
#488) rigorously and uniformly. The **full** `2B(n) > nS` for *all* `n ≥ max` still
needs the small-`n` bridge; the second-order charge is a statement about the limiting
average `E[1/R]`, and the finite averages dip below `157/300` for small ranges, so the
`s(n) > nS − 5` floor loss is not yet absorbed uniformly. Lean formalization needs the
asymptotic-density layer (new), but the finite lemma is directly formalizable now.

---

## (Superseded) Alternative route — Bonferroni + finite residual

*Kept for the record. This was the first route; it reduced `2δ>S` to a finiteness
lemma that remained unproved. Step 4's second-order charge above avoids it.*

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
