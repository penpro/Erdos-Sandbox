# Size-5 density inequality `2δ > S` — PROVED (second-order charge)

Status: `PROVED` (`2δ > S`, the large-`n` half; reduction machine-checked in
`lean/ep488/Ep488/Density.lean`, kernel banked) / small-`n` bridge reduced to the
bounded window `n ∈ [max, 33·max)` for `≤2`-good sets (`PROVED modulo U2`, see the
bridge section) / the `≤2`-good window **cover** is the one open piece (the class is
provably infinite — finiteness is dead). (Claude, 2026-07-08/09; adversarially
verified by two independent workflows.) This is the asymptotic backbone of Erdős
#488 at `|core| = 5`. The proof is the second-order-charge argument below; it gives
`2δ − S ≥ (7/150)·S` for every primitive quintuple. Companion to the size-≤4 charge
development in `lean/ep488` and to Codex's separator census in
`adversary_collab_chat.md`.

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

### Claude patch to the addendum (2026-07-09, verified exactly)

Two refinements to the above (found by an independent deep review, both re-verified):

1. **Step 2–3 gap (one clause).** The exchange argument assigns *multiplicities* to
   primes optimally, but does not by itself justify shrinking the prime *values* to
   the initial segment `{2,3,5,7}` — value-lowering into a **collision** can raise
   `E` (e.g. `E(2,2,3,3) = 8/15 > E(2,2,3,5) = 157/300`), and nothing in steps 1–2
   rules out, say, `(2,2,3,7)`. The fix is the collision-free lowering schedule
   ("Route B", now the canonical third step in THE PROOF below): the distinct prime
   values `q₁<⋯<q_k` satisfy `q_j ≥ p_j` (the `j`-th prime), so lowering them *in
   increasing order* to `2,3,5,7` never collides, and each step lowers `E` by the
   independence identity. Conclusion (min `= 157/300` at `(2,2,3,5)`) unchanged.
   Suggest extending `audit_quint_density_lemma.py` (currently primes ≤13) with the
   35-multiset `{2,3,5,7}⁴` check + the collision counterexamples.
2. **The `138M` window is now `33M`.** A drift lemma for the per-element partial sums
   (`f(J) ≥ (7/300)J − 7/30`, jointly optimal, equality on `(2,2,3,5)`) sharpens the
   window bound to `2B(n) > nS` whenever `7nS > 1135 − 157S`, in particular
   `n ≥ 33·max(P)` (exact `K = 227/7 ≈ 32.43`). See "The small-`n` bridge" section
   below. Your `B(n) ≥ δn − 16` route and this are the same idea family; the drift
   version pays the floor loss per element instead of per subset.

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
- **Lowering the prime values to `{2,3,5,7}` ("Route B" — the canonical argument).**
  For a prime `p` in the tuple that differs from the other prime values, `{p∣N}` is
  independent of the rest, giving
  `E = (1−1/p)·E[1/(1+X′)] + (1/p)·E[1/(1+μ+X′)]` (`μ` = multiplicity of `p`, `X′`
  counts the non-`p` entries) — **strictly increasing in `p`** (since
  `E[1/(1+X′)] ≥ E[1/(1+μ+X′)]` pointwise). So lowering a prime *value* lowers `E` —
  **but only if the new value stays distinct from the other prime values**: lowering
  *into a collision* can RAISE `E` (e.g. `E(2,2,3,3) = 8/15 > E(2,2,3,5) = 157/300`;
  `E(2,3,11,11) = 799/1320 > E(2,3,11,13) = 2359/3960`). The collision-free schedule:
  a prime 4-multiset has `k ≤ 4` distinct values `q₁ < ⋯ < q_k`, and necessarily
  `q_j ≥ p_j` (the `j`-th prime). Lower `q₁ → p₁ = 2`, then `q₂ → p₂ = 3`, … in
  increasing order, carrying multiplicities: at step `j` the already-lowered values
  `p₁ < ⋯ < p_{j−1}` are all `< p_j` and the untouched values `q_{j+1} < ⋯` are all
  `> q_j ≥ p_j`, so **no collision ever occurs** and every step lowers `E`. The
  minimum therefore lives among 4-multisets with values in `{2,3,5,7}`.
- **Finite check.** Over the 35 multisets of `{2,3,5,7}⁴`, `min E = 157/300` at
  `(2,2,3,5)`. ∎ (lemma)

  *Alternative third step (sound but heavier): the `f_μ(p)` retirement bound
  `E ≥ (1−1/p)·E_{4−μ}min + (1/p)·(1/5)`, increasing in `p`, beats `157/300` at
  `p = 11` for all `μ = 1..4` (`1061/1980, 593/990, 7/10, 51/55`), so primes `≥ 11`
  can't attain the minimum. It relies on the lower-size minima
  `E₁min = 3/4, E₂min = 23/36 (2,3), E₃min = 41/72 (2,2,3)` — themselves provable by
  the same Route B at their own size, so the recursion closes; but note the analogous
  retirement at the size-3 level fails at `p = 5` (`101/180 < 41/72`, needs `p ≥ 7`),
  so Route B, which needs no lower-size minima at all, is the canonical proof.
  (True min over prime multisets containing a prime `≥11`: `181/330` at `(2,2,3,11)`.)*

  *Verified (`lemmaB.py` + two independent adversarial workflows, exact rationals):
  global min over `[2..60]⁴` = 157/300, unique argmin `(2,2,3,5)`; min over the 4,810
  prime multisets (primes ≤60) containing a prime ≥11 = 181/330; divisor-monotonicity:
  0 counterexamples in 200k random + 234,256 exhaustive checks; independence identity
  exact in 30,000/30,000 cases; the collision counterexamples above exact.*

  *Role of primitivity, for clarity: Steps 1–2 are pure inclusion–exclusion algebra and
  hold for ANY five positive integers; primitivity enters ONLY to force every reduced
  friend `m_f = lcm(a,f)/a ≥ 2` (an element dividing another would give `m_f = 1`),
  which is the sole precondition of the finite lemma.*

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
needs the small-`n` bridge (see the next section: the bridge is now reduced to a
bounded window). **Lean status:** no asymptotic-density layer is needed —
`2δ − S = Q(P)` is floor-free, and `lean/ep488/Ep488/Density.lean` already
machine-checks the entire reduction (`sum_terms_eq_Q`, the decomposition identity,
and `Q_pos_of_E4_bounds`: the five per-element `E4 ≥ 157/300` bounds ⟹ `Q(P) > 0`),
sorry-free on the three standard axioms (`density-axioms.txt`, in CI). The one part
*outside* Lean, by design, is the finite kernel `E4 ≥ 157/300` itself — banked as
explicit hypotheses; it rests on the Route B paper proof + exhaustive computation.

---

## The small-`n` bridge: drift theorem + the `33·max` window

*Status: `PROVED modulo U2` (U2 is a finite-check lemma at the same tier as the `E4`
kernel: divisor-monotonicity + finite check; paper-sketch + exhaustive computation,
zero violations). Found by the Fable-5 deep review (2026-07-09), then independently
re-verified exactly (identity, constants, and 720 `(A,n)` spot checks, 0 violations).*

For four moduli `m₁,…,m₄ ≥ 2` let `f(J) = Σ_{j≤J} (1/(1+X(j)) − 1/2)`,
`X(j) = #{i : mᵢ ∣ j}` — the per-element *drift* (partial-sum) version of the kernel.

- **U1 (dip).** `inf_J f(J) = −1/12`, attained ONLY at moduli `(2,2,3,5)`, `J = 6`.
  For 1, 2, or 3 moduli, `f ≥ 0` universally. (The observed `−1/12` dip is a theorem.)
- **U2 (drift).** `f(J) ≥ (7/300)·J − 7/30` for all `J ≥ 0` — **jointly optimal**
  (equality at every `J ≡ 10 (mod 30)` on `(2,2,3,5)`). Reduction to a finite check:
  divisor-monotonicity raises `f` pointwise at every `J`, and one full period `L`
  advances `f` by `L·(E4 − 1/2) ≥ L·(7/300)` — exactly the `E4` kernel — so a
  per-period check suffices.

**Drift bridge theorem.** Summing `U2` at `J = ⌊n/a⌋` over the five elements (using
`⌊n/a⌋ = n/a − {n/a}` and `{n/a} ≤ 1 − 1/a`), for every primitive quintuple and
`n ≥ max(P)`:

```
2B(n) − nS  ≥  (7/150)·nS − 7/3 − (157/150)·(5 − S).
```

Hence `2B(n) > nS` whenever `7nS > 1135 − 157S` — in particular whenever `nS ≥ 163`,
and (since `nS ≥ 5n/max`) whenever **`n ≥ 33·max(P)`** (exact threshold
`K = 227/7 ≈ 32.43`). Both loss terms are individually unimprovable. This sharpens
the addendum's `138·max` window by `4.2×`. Corollaries:
- the window is empty unless `max·S ≤ 1135/7 ≈ 162.1` (so `max/min ≥ 159` ⟹ bridged
  for ALL `n`);
- every "4 fixed elements + X" family has an absolute cap on the `X` needing checks;
- scaling towers `tP` close via one base-shape check over
  `m ≤ 1135/(7S) + 150/7`.

**What full size-5 #488 now reduces to.** (i) `≥3`-good quintuples: covered for ALL
`n` by `ep488_quint_three_good` (Lean, sorry-free). (ii) `n ≥ 33·max`: covered by the
drift bridge (modulo U2). (iii) Remaining: **`≤2`-good gcd=1 quintuples on the finite
window `n ∈ [max, 33·max)`**.

**The `≤2`-good class is PROVABLY INFINITE** — finiteness is dead. Witness family:
`{12, 20, 30, 45, 15k}` for `k` odd, `3 ∤ k`, `k ≥ 5` has *exactly two* good elements
for every such `k` (charges: `7/15 + 1/(5k)`, `7/9 + 1/(3k)` good; `4/3 + 1/k`,
`1 + 1/k`, `4/3` bad — the base's two bad-within-base elements never flip). A second
two-parameter family: `{3, 4, 2q, 5q, qm}`. So the corrected open lemma is a **cover**
statement, not finiteness: *every `≤2`-good gcd=1 quintuple with `max·S ≤ 1135/7`
passes its finite window* — encouragingly, the infinite families' window margins GROW
in the free parameter (`{12,20,30,45,105}`: min `2B − nS ≈ 10.0`; at `15k = 735`:
`≈ 71.4`), so large members auto-bridge; what's missing is the uniform cover argument.

**Death certificate for the density program at large size** (replaces the 25-element
`{2p : p ≤ 100}` example): the 15-element semiprime layer `{pq ≤ 39}` =
`{4,6,9,10,14,15,21,22,25,26,33,34,35,38,39}` has

```
2δ − S = −380977/290990700 < 0        (exact; and δ ≈ 0.538 > 1/2)
```

and since `δ > 1/2`, padding with fresh large primes preserves failure — so `2δ > S`
fails at EVERY size `≥ 15`. Exhaustive/range-bounded search finds no failure at sizes
`≤ 8` (and none up to 14 by search); only `≤ 5` is *proved* safe. The minimal failing
size lies in `[6, 15]`. Realistic reach of the program: size 6 likely (the per-element
kernel fails — `E₅min = 49/100 < 1/2` — but the worst realizable per-element term is
only `−71/94500`, at `a = 15` in `{6,7,9,10,15,25}`, repaid ~287× by the forced small
co-elements; needs a cross-element transfer lemma), size 7 maybe, sizes 9–14 grim,
`≥ 15` impossible. General #488 remains open and needs `n`-dependent, multi-scale
control — the bridge machinery here is the only `n`-aware tool in the repo.

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

## Lean formalization status (updated 2026-07-09)

- **Done, sorry-free, CI-audited** (`Ep488/Density.lean` + `DensityCheck.lean`):
  the full second-order-charge *reduction* in floor-free form — `sum_terms_eq_Q`
  (the decomposition `Σ_x (2·brX − 1/x) = Q(P)`, pure `ring`) and
  `Q_pos_of_E4_bounds` (the five `E4 ≥ 157/300` bounds ⟹ `Q(P) = 2δ − S > 0`).
  No asymptotic-density layer was needed: `Q(P)` is an explicit rational.
- **Banked outside Lean (by decision):** the finite kernel `E4 ≥ 157/300` — enters as
  explicit hypotheses; Route B paper proof + exhaustive computation. Formalizing it
  is a well-scoped follow-up (I–E/average over one period, divisor-monotonicity
  coupling, Route B lowering, 35-multiset check).
- **Also already Lean-proved:** `ep488_quint_three_good` (≥3-good ⟹ #488, all `n`).
- **Not yet formalized:** U1/U2 and the drift bridge (same machinery tier as the
  kernel), and the `≤2`-good window cover (open mathematics first).

## Reproduce

```bash
# exact-fraction search (scratch scripts): min(2δ−S) over gcd=1 quintuples,
# and enumeration of the S≤2P2 residual (finite: exactly 3 up to entries 58).
python residual_hunt.py 58        # -> S<=2P2 residual = 3 sets
```
