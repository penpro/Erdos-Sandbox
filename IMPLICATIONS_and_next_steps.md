# Implications of the elementary sorry‑free proof of Erdős #488 for `|P| ≤ 3`

> **Curation note (Claude-main, 2026-07-07).** Authored by an implications
> subagent, then reviewed and fact-checked by me. Two of its concrete leads were
> computationally tested after the fact:
> - **§B worked examples confirmed:** the charge method does handle "spread"
>   quadruples (`{2,5,7,9}`, `{3,4,5,7}` — all four charges `≥ 1`). This is now a
>   proved general result, **Proposition 8''** (charge-positive sets of any
>   size), in `triples_writeup.md` §5A and the standalone note.
> - **§B "candidate rescue lemma" FALSIFIED:** the conjecture "largest-element
>   charge sum `= 1` ⇒ covered zone `1/b+1/c+1/d ≤ 1/a`" is **false** — 37 of 49
>   primitive quadruples (`a ≤ 25`) with charge-sum 1 violate it; smallest
>   witness `{6,10,15,25}`. So the size-4 boundary has no Lemma-4 analogue of
>   this form; treat §B step (iii)/candidate-lemma as a dead conjecture, not a
>   lead. The rest of the analysis (esp. §A Lean feasibility) stands.

---

# Implications of the elementary sorry‑free proof of Erdős #488 for `|P| ≤ 3`  (subagent analysis)

*Scope: `triples_writeup.md` (charge decomposition → `2B(n) > nS` on the uncovered zone; Theorem 6 on the covered zone), cross‑read against Chojecki's note (Cor 4.7 via Thm 4.5 + block split; Conj 4.8 pair‑vs‑tail; Remark 7.7 frontier) and the AI‑methods catalog. Novelty caveat carried throughout: the **result** `|P| ≤ 3` is publicly claimed (Chojecki Cor 4.7, Lean modulo one `sorry`); our contribution is an independent **elementary, sorry‑free route** plus an **ordering‑free strengthening**.*

---

## Executive summary

The proof's value is not that it re‑derives a claimed result. It is three concrete, separable things:

1. **It is exactly the gap‑closer for the public Lean bundle.** Chojecki's Cor 4.7 is Lean‑complete *except* for `exact_one_count_ge_four`, which is precisely the "four exact‑one points" count `E₁(n) ≥ 4` in the proof of Theorem 4.5 (scratch lines 847–883). Our route never needs `E₁(n) ≥ 4`. It replaces that single nested case analysis with **three trivial applications of one arithmetic lemma** (`X_i ≥ 1`) plus **one parity lemma**. Every one of our load‑bearing steps is `omega`/`gcd`‑elementary. So a full sorry‑free Lean proof of `|P| ≤ 3` is realistic on our route and would close the exact hole the public artifact leaves open (§A).

2. **It exposes the right invariant.** The separating constant is the **union‑bound density `S = Σ 1/d`** (not the true inclusion–exclusion density `δ` the transport note centers on), and the mechanism is a **per‑generator local surplus** `X_i ≥ 1` ("every generator pays for itself"). This reframes #488‑for‑small‑cores from a global transport balance into a local counting statement, and it pinpoints — with a one‑line inequality `1/2 + 1/2 ≥ 1` — exactly why `|P| = 4` is different (§B, §D).

3. **It sharpens one rung of the public program to sorry‑free, and says precisely why the next rung is hard.** Our `X_i ≥ 1` and Chojecki's `E₁(n) ≥ 4` prove *the same slack*; we distribute it into three easy pieces where he bundles it into one hard one. This is a simplification of the pair‑vs‑one‑tail rung, and it makes transparent that the pair‑vs‑two‑tail bottleneck (Remark 7.7) stalls for the **same reciprocal‑budget reason** our method stalls at `|P| = 4` (§C).

---

## A. Lean formalization — the single most concrete deliverable

**Verdict: a full, sorry‑free Lean proof of `(★)` for `|P| ≤ 3` is realistic on our route, and it is the natural way to close `exact_one_count_ge_four`.** Estimated effort ≈ 300–500 lines of Lean 4 / Mathlib, no new mathematics, no `sorry`. The only infrastructure lift is the three‑set Bonferroni count; everything else is `omega` and `Nat.gcd`.

### Why our route formalizes and Chojecki's stalls

Chojecki's size‑≤3 proof (Cor 4.7) runs: block‑decompose `B_G = B_{g₁,g₂} \ B_{g₃} ⊔ g₃ℕ` (Prop 4.6), apply **Theorem 4.5** to the first block and Theorem 3.1 (singleton) to the second. Theorem 4.5's proof turns on establishing `E₁(n) ≥ 4` — four "exact‑one" points below `n` (lines 863–883): a case split on `k = 2b/a ∈ {3, ≥4}`, sub‑cases `da = 3a` vs `4a ≤ n`, each discharging a divisibility contradiction. That nested integer case analysis is the `sorry` (`exact_one_count_ge_four`), and it gates Thm 4.5, Cor 4.7, **and** Cor 5.3. A prover trips on it because the "there exist four distinct non‑generator points, none a generator, none a double" bookkeeping is a fiddly existence‑with‑distinctness argument over `Finset`s.

Our route produces the identical surplus (`s(n) − 2P(n) ≥ 3`) but as **three independent `≥ 1` facts**, each an instance of the same one‑line lemma. There is no existence/distinctness combinatorics anywhere.

### Lemma‑by‑lemma Lean map

| Our lemma | Lean statement | Tooling | Cost |
|---|---|---|---|
| **1(i)** nested floor `⌊n/(qd)⌋ = ⌊⌊n/d⌋/q⌋` | `n / d / q = n / (d*q)` | **`Nat.div_div_eq_div_mul`** (Mathlib, exact) | free |
| **1(ii)** `t − ⌊t/q⌋ − ⌊t/q'⌋ ≥ 1`, `q≥2, q'≥3, t≥1` | `1 ≤ t - t/q - t/q'` | `Nat.div_mul_le_self` + **`omega`** | ~4 lines |
| **3** ratio bounds | `3 ≤ y / gcd x y`, `2 ≤ x / gcd x y` | `Nat.le_of_dvd`, `Nat.gcd_dvd_*`, `Nat.div_dvd…` | ~30 lines |
| **4** parity dichotomy | `¬(a/gcd a c = 2 ∧ b/gcd b c = 2)` under `a*c+a*b > b*c` | divisibility + parity + `omega` | ~40 lines |
| **2** Bonferroni 3‑set | `s(n) - P(n) ≤ B(n)` | `Finset.Ioc` filter‑card + inclusion–exclusion | ~120 lines (the real lift) |
| **5, Thm 8, Cor 8′** | assembly | `omega` / `ℚ` casts | ~60 lines |

**Lemma 1(ii)** is the crux and it is genuinely trivial in `Nat`. Feed `omega` the two facts `Nat.div_mul_le_self t 2 : 2*(t/2) ≤ t` and `Nat.div_mul_le_self t 3 : 3*(t/3) ≤ t` (treating `t/2`, `t/3` as opaque), plus `1 ≤ t`; the goal `1 ≤ t - t/2 - t/3` is then a true Presburger statement (`⌊t/2⌋+⌊t/3⌋ ≤ t−1` for all `t ≥ 1`), which `omega` decides. The `(q,q') = (2,3)` worst case dominates `(≥2,≥3)` monotonically (`Nat.div_le_div_left`), so one lemma covers all six charge cases.

**Lemma 3** is pure `Nat` divisibility: `g = gcd x y ∣ y`; set `k = y/g`; `k=1 ⇒ g=y` contradicts `g ≤ x < y`; `k=2 ⇒ g=y/2 ∣ x` with `y/2 ≤ x < y ⇒ x=y/2 ⇒ x∣y`, contra primitivity; so `k ≥ 3`. The `x/g ≥ 2` half is `g ∣ x`, `g=x ⇒ x∣y` contra.

**Lemma 4** clears denominators once: `1/b + 1/c > 1/a ⟺ a*c + a*b > b*c` (a single `Nat`/`Int` inequality, no rationals). Assuming both ratios `= 2` gives `c = k*(a/2) = l*(b/2)`, `k,l` odd `≥ 3`, `k > l ⇒ k ≥ l+2`, hence `a*c + a*b ≤ b*c` — an `omega`‑closable contradiction once the divisibility/parity facts are in hand.

**Bonferroni (Lemma 2)** is the only nontrivial piece and it is standard: `B(n) = |(aℕ ∪ bℕ ∪ cℕ) ∩ Ioc 0 n|`, `|dℕ ∩ Ioc 0 n| = n/d` (Mathlib's `Nat.Ioc_filter_dvd_card_eq_div` / `Nat.card_multiples`), pairwise `dℕ ∩ eℕ = lcm(d,e)ℕ`, and the truncated‑Bonferroni bound `|X∪Y∪Z| ≥ |X|+|Y|+|Z| − |X∩Y| − |X∩Z| − |Y∩Z|` from `Finset.card_union_le` / `card_union_add_card_inter`.

### Keep it rational‑free

The whole theorem can be stated and closed over `ℤ` — no `ℝ`/`ℚ` `Nat.floor` friction. The two integer statements are:

- **Valley (`n ≥ c`, uncovered):** `2 * B(n) * (a*b*c) > n * (b*c + a*c + a*b)` — from Bonferroni + `s−2P ≥ 3` + the three Euclidean identities `n = d*(n/d) + n%d`.
- **Peak (all `m`):** `B(m) * (a*b*c) ≤ m * (b*c + a*c + a*b)` — the union/floor bound `d*(m/d) ≤ m`.

Multiply, cancel `a*b*c > 0`, and `(★)` `n*B(m) < 2*m*B(n)` drops out in two lines. (If one prefers, `S : ℚ` with `Nat.floor_le` and `Nat.lt_floor_add_one` also works; the integer form avoids casts entirely and is friendlier to `omega`.)

**Bottom line for A:** this is a *finishing* formalization, not a research formalization. It plausibly resolves the open status of the public Lean bundle (community currently treats `|A| ≥ 3` as open precisely because of the `sorry` + the checker flag). Highest‑value, lowest‑risk next step.

---

## B. Does the method extend to `|A| ≥ 4`?

**Short answer: not as a flat per‑element charge — and the reason is a sharp, one‑line reciprocal‑budget obstruction. But a hybrid (charge on spread/coprime cores) ⊕ (recursion on shared‑factor cores) ⊕ (dense half) covers two well‑characterized ends and isolates the genuinely hard middle.**

### The exact obstruction

For a primitive quadruple `{a<b<c<d}`, truncated Bonferroni is `B(n) ≥ s(n) − P(n)` with `P` summing over all `C(4,2)=6` pairs, and

```
s(n) − 2P(n) = X_a + X_b + X_c + X_d ,   X_e = t_e − Σ_{f≠e} ⌊n/L_{ef}⌋ ,
```

each pair‑term appearing in exactly two `X`'s. Now **every element `e` accrues one lcm‑ratio from each of its partners**, and Lemma 3 pins those ratios only from below:

- partner **below** `e` (say `f < e`): `L_{fe}/e = f/gcd(f,e) ≥ 2`  ← the weak side;
- partner **above** `e` (`f > e`): `L_{ef}/e = f/gcd(f,e) ≥ 3`.

`X_e > 0` needs `Σ_{partners} 1/ratio < 1`. Tally the guaranteed reciprocals:

| element | ratios (below | above) | worst guaranteed reciprocal sum |
|---|---|---|
| `a` (min) | — \| b,c,d (all ≥3) | `≤ 1/3+1/3+1/3 = 1` → borderline, but coprime gives `1/b+1/c+1/d < 1` easily |
| `b` | a (≥2) \| c,d (≥3) | `1/2 + 1/3 + 1/3 = 7/6 > 1` |
| `c` | a,b (≥2,≥2) \| d (≥3) | `1/2 + 1/2 + 1/3 > 1` |
| `d` (max) | a,b,c (≥2,≥2,≥2) | `1/2 + 1/2 + 1/2 = 3/2 > 1` |

So the writeup's stated `1/2 + 1/3 + 1/3 > 1` is actually the *mildest* failure (`X_b`). The real killer is that **the top element collects three weak‑side ratios and just two of them already sum to `1/2 + 1/2 = 1`.** Worse, even if primitivity could upgrade *all three* of `X_d`'s ratios from 2 to 3 (it generically cannot), you land at `1/3·3 = 1` exactly — `X_d ≥ 0`, never `≥ 1`. **`(3,3,3)` sits precisely on the boundary.** There is no ratio‑lower‑bound rescue for the largest element of a quadruple. A four‑element analogue of Lemma 4 cannot manufacture strict positivity from below.

This is also *consistent* with the known global obstruction: the per‑`n` criterion `2B(n) > nS` is **false** for `A = {2p : p ≤ 100}` (25 elements, fails at every large `n`). That family is the shared‑factor extreme — every element shares the factor 2, gcd's are maximal, weak‑side ratios collapse to their floor.

### The hybrid, and exactly which quadruples each regime owns

**(i) Shared‑factor recursion.** If `gcd(P) = g > 1`, write `P = g·P'`. Then `B_P(x) = B_{P'}(⌊x/g⌋)`, and since `⌊x/g⌋` is monotone with `B_{P'}(⌊x/g⌋)/x ≍ (1/g)·B_{P'}(⌊x/g⌋)/⌊x/g⌋`, the sup/inf ratio of `g_P` equals that of `g_{P'}` up to controlled boundary terms — `(★)` for `P` **reduces to `(★)` for the smaller‑`max` set `P'`** (this is the *third mechanism* that rescues `{2p}`). Induction on `max` closes every core with a nontrivial common factor. Clean, and formalizable (`B_{gP'}(x) = B_{P'}(x/g)` is a `Nat.div` identity).

**(ii) Charge on the coprime/spread part.** The charge method proves all four `X_e ≥ 1` **iff** for every `e`, `Σ_{f≠e} gcd(f,e)/f < 1`, the binding constraint being the largest element: `Σ_{x<d} gcd(x,d)/x < 1`. In the pairwise‑coprime case this is `1/a + 1/b + 1/c < 1` on the *three smallest*. So the charge‑handleable family is the **"spread" cores**: pairwise‑coprime (or gcd‑light) quadruples in which every non‑max pair `{x,y}` has `1/x + 1/y < 1/2`.

*Worked example the method already handles:* `{2,5,7,9}` (pairwise coprime).
`X_d(=9): 1/2+1/5+1/7 = 0.843 < 1`; `X_c(=7): 1/2+1/5+1/9 = 0.811`; `X_b(=5): 1/2+1/7+1/9 = 0.754`; `X_a(=2): 1/5+1/7+1/9 = 0.454`. All four positive → `s−2P ≥ 4`, and the size‑4 Theorem‑8 analogue (`2B(n) ≥ 2s−2P > nS + (s−2P) − 4 ≥ nS`) closes it directly. Contrast `{2,3,5,7}`: `X_d = 1/2+1/3+1/5 = 31/30 > 1`, method fails, and this is exactly a "clustered small factors" set.

This substantially enlarges Theorem 6's covered zone (which for a quadruple demands the very tight `1/b+1/c+1/d ≤ 1/a`): the charge zone `1/a+1/b+1/c < 1` (three smallest) is far larger.

**(iii) Dense half.** Whenever `B(n) ≥ n/2` (Chojecki Prop 6.1 / our Theorem 3), `(★)` holds at that `n` regardless of `|P|`.

**The residual hard middle.** What neither charge (needs spread) nor recursion (needs a common factor) owns: cores with **partial / clustered small factors** — e.g. `{2,3,4,9}`, `{2,3,5,7}`, `{4,6,9,…}` — where two or three weak‑side `1/2`‑ratios pile up on one element but no factor is shared by *all*. This is the same locus as Chojecki's **two‑tail bottleneck** (Remark 7.7) and the layer‑10 `|Amin| = 4` cases (Remark 5.4).

### Candidate rescue lemma (worth testing, not yet a theorem)

A quadruple analogue of Lemma 4's *boundary* phenomenon: **when `Σ_{x<d} gcd(x,d)/x = 1` exactly (the `(3,3,3)`, `(2,4,4)`, `(2,3,6)` configurations), primitivity forces the set into the covered zone `1/b+1/c+1/d ≤ 1/a`** — just as `{6,10,15}` (with `L_{ac}/c = L_{bc}/c = 2`, i.e. the triple boundary) fell to Theorem 6. If true, the boundary sets are handed off and the charge zone becomes the *open* inequality's interior. **First check:** enumerate primitive quadruples, flag those with largest‑element reciprocal sum `= 1`, and test whether all satisfy `1/b+1/c+1/d ≤ 1/a`. (The triple analogue held on all 13 336 configs in Part E; the quadruple version is a clean, falsifiable conjecture.)

---

## C. Relation to the public program (pair‑vs‑tail)

**Structurally orthogonal; mechanistically identical at the sticking point.**

Chojecki's route (Prop 4.6 → Conj 4.8 → Prop 4.9) is a **recursive peeling**: pair the bottom two generators `{g₁,g₂}` against the forbidden *tail* `{g₃,…,g_r}`, prove pair‑vs‑tail split doubling `F_{a,b|V}(m)/m < 2F_{a,b|V}(n)/n`, and induct. Our charge method is **flat and symmetric**: one Bonferroni pass over the whole union giving `2B(n) > nS` in a single shot, no ordering, no tail. In that sense the two are orthogonal decompositions of the same counting function.

But look at what the pair‑vs‑tail proof actually *needs*. Theorem 4.5 (pair vs **one** forbidden modulus = the `|P| ≤ 3` rung) closes exactly when `E₁(n) ≥ 4`, and **`E₁(n)` is the pair‑version of our charge**: the count of points hitting exactly one of `a,b` and avoiding `c`. Chojecki needs that surplus `≥ 4` (via nested cases → the `sorry`); we obtain the equivalent surplus as `X_a + X_b + X_c ≥ 3` via three one‑liners. **Same slack, redistributed.** So on the pair‑vs‑one‑tail rung, our method is not orthogonal — it is a *strictly simpler proof of the same surplus*, and that is why it formalizes where his `sorry` sits.

Go up one rung — pair‑vs‑**two**‑tails (Remark 7.7, "the first unresolved local transport layer") — and both stall for the **same reason**: forbidding a length‑2 tail forces the surplus count to survive two simultaneous `1/2`‑weight subtractions, i.e. the identical `1/2 + 1/2 ≥ 1` budget failure that sinks `X_d` in §B. The charge method does not rescue pair‑vs‑two‑tail; it *explains why nobody's method does yet.*

**The ordering‑free strengthening, and whether it propagates.** Corollary 8′ proves more than `(★)`:

```
sup_{m≥1} B(m)/m  ≤  S  <  2 · inf_{n≥c} B(n)/n .
```

This pins the separator to the explicit invariant `S = ΣB 1/d` and removes the `m > n` ordering entirely. The thread's triple results (periodicity certificates; Chojecki's block + Thm 4.5) prove the ordered `(★)` but do **not** exhibit this clean sup/inf gap with an explicit rational separator. The strengthening *could* propagate as a **cleaner target for Conjecture 4.8**: instead of the ordered pair‑vs‑tail inequality, aim for the block‑wise ordering‑free bound `sup F_{a,b|V}(m)/m ≤ ρ_{a,b|V} < 2 inf F_{a,b|V}(n)/n` with `ρ` the block's raw density. That implies 4.8 and is more symmetric to attack. Honest caveat: it is a *stronger* statement, so proving it is at least as hard — the strengthening buys clarity and a Bonferroni handle (via Chojecki's own §8 quotient‑tail inclusion–exclusion), not a free lunch on the two‑tail bottleneck.

---

## D. What "simpler" unlocks

**1. Formalizability (the concrete win).** Elementary + `omega`‑closable ⇒ sorry‑free Lean is in reach (§A). A 27‑page signed‑transport note with a `sorry` on its central combinatorial count is not something you hand a prover and get green. Two pages of `Nat.gcd` and floor identities is. This converts "claimed modulo `sorry`, community treats as open" into "proved."

**2. Teachability / refereeability.** Every step is checkable by hand in one sitting: a divisor‑of‑`y` argument, a parity contradiction, and "a positive integer that is `≥ t/6` is `≥ 1`." No transport theory, no signed measures, no 42‑lemma Lean file to trust. That is the difference between a result the community *absorbs* and one it *cites warily* (cf. the note that MalekZ and Blair kept treating `|A| ≥ 3` as open through mid‑2026).

**3. It reveals the right invariant — and the transport machinery obscured it.** Two clarifications the elementary proof makes visible:

- **The separating constant is the union‑bound density `S = Σ 1/d`, not the true density `δ`.** The transport note works with `δ_A` (full inclusion–exclusion). Our proof shows that in the uncovered zone you never need `δ`: the *raw* reciprocal sum `S` already separates sup and inf. That is a genuinely simpler invariant, and it is the correct one for small cores.
- **`#488`‑for‑small‑cores is a per‑generator local surplus, not a global balance.** The charge `X_e = ⌊n/e⌋ − (its pairwise‑lcm floors)` is "the multiples of generator `e` not absorbed by overlaps with the others" — Bonferroni made *local*. The whole theorem becomes: **each generator pays for itself, `X_e ≥ 1`.** The transport formulation spreads this across a signed measure and hides it. Once you see it, `|P| = 4` is transparent: three generators can gang up on one (`X_d` underwater, §B), and *that single picture* predicts both the `{2,3,5,7}` failure and the `{2p}` global counterexample.

**4. Community value is bankable.** An independent sorry‑free elementary proof settles the status of Cor 4.7 outright. Per protocol and Wes's Law 6, whether to post to the #488 thread is Wes's call — but the deliverable exists and is defensible as "independent sorry‑free verification + ordering‑free strengthening + the local‑surplus reframing."

---

## E. Ranked next steps

**1. Formalize `|P| ≤ 3` in Lean, sorry‑free (closes `exact_one_count_ge_four`).**
   *First action:* stub the five lemmas of §A in Lean 4/Mathlib — `Nat.div_div_eq_div_mul` (free), `sub_two_floors_pos` (`Nat.div_mul_le_self` + `omega`), the two gcd‑ratio lemmas, the parity lemma, then the three‑set Bonferroni via `Nat.Ioc_filter_dvd_card_eq_div`. Assemble over `ℤ` (rational‑free form).
   *Difficulty:* moderate; the only real lift is Bonferroni counting (~120 lines). ~2–4 focused days.
   *Type:* **formalization task.** Highest value — it plausibly closes the public bundle's open gap. Consider farming the assembly to Aristotle after the lemma stubs exist (the #650 pattern: provers repair exactly this kind of finite arithmetic).

**2. Nail the quadruple charge subfamily + test the size‑4 boundary lemma.**
   *First action:* enumerate primitive quadruples (elements ≤ 40, full period), classify by whether all four `X_e ≥ 1`; separately test the rescue conjecture "`Σ_{x<d} gcd(x,d)/x = 1 ⇒ 1/b+1/c+1/d ≤ 1/a`" exhaustively.
   *Difficulty:* moderate.
   *Type:* **mixed** — the enumeration is computation; the boundary lemma is a genuine (small) open problem. If it holds, it converts the charge zone into a clean open‑inequality interior and gives the first honest chunk of `|P| = 4`.

**3. Prove the shared‑factor recursion as a clean lemma; assemble the three‑regime quadruple theorem.**
   *First action:* prove `B_{gP'}(x) = B_{P'}(⌊x/g⌋)` and its sup/inf‑ratio preservation; state the partition (charge‑spread ∪ shared‑factor ∪ dense‑half) and characterize the residual "clustered‑small‑factor" middle explicitly.
   *Difficulty:* recursion is easy and formalizable; the residual characterization is open.
   *Type:* **genuine open problem** for the residual; the recursion itself is a writeup/formalization task. This is where the `{2p}`‑style counterexamples get absorbed and the true hard core of `|P| = 4` is isolated.

**4. Two‑sided Bonferroni finite reduction for quadruples (#690 template).**
   *First action:* compute the exact two‑sided constants (`|B(x) − δx| ≤ K` from the 10‑term 4‑set inclusion–exclusion) and the resulting threshold "`(★)` holds whenever `nδ > K′`," reducing `|P| = 4` to a bounded `n`‑window plus a finite certified check; verify against existing sweep data.
   *Difficulty:* moderate; mechanical constant bookkeeping with an open small‑`nδ` residue.
   *Type:* **mostly writeup/computation** with a possibly‑open window. Complements #2/#3 (the Bonferroni bound is tight exactly where charge overlaps are small).

**5. Package the ordering‑free `|P| ≤ 3` note + reduction map; one targeted literature pass.**
   *First action:* draft the 2‑page elementary note (lead with `S` and the local surplus `X_e`), and run a Deep‑Research pass on the classical sets‑of‑multiples circle (Davenport–Erdős 1936, Behrend, Hall's *Sets of Multiples*, Halberstam–Roth Ch. V) to confirm the local‑surplus framing isn't already classical — the #281 precedent (that neighborhood contained a "solved" open problem) makes this due diligence mandatory before any novelty claim.
   *Difficulty:* low.
   *Type:* **writeup / diligence.** Posting to the thread is Wes's call (Law 6); the note and the lit‑pass are worth doing regardless.

---

*Files read: `triples_writeup.md`, `proof_attempt.md`, `adversary_collab_chat.md`, `tmp/wf_result_a0184db1f36725190.md`, `scratch_chojecki_488.txt` (Thm 4.5 lines 749–883, Cor 4.7 line 917, Conj 4.8/Prop 4.9 lines 923–944, Prop 5.1/Thm 5.2 lines 950–1210, Remark 7.7 line 2081). No files written.*