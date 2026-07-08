# Fresh adversarial referee report (opus-4-8, independent)

> Produced by a fresh subagent that had NOT seen the derivation, tasked to BREAK the proof and adjudicate the simplicity claim. Script: referee_triple_check.py; log: scratch_referee_out.txt. Verdict: ALL CHECKS PASS; no gaps.

---

All checks reconcile: dropping my `a∤b` primitivity filter reproduces the writeup's exact Part E count of 13,336 (0 violations either way). Everything passes. Here is my referee report.

---

# REFEREE REPORT — Erdős #488, `|A_min| ≤ 3`

Script: **`D:\Erdos Sandbox\referee_triple_check.py`** (exact integer/`Fraction` arithmetic; runs in ~116 s; full log at `D:\Erdos Sandbox\scratch_referee_out.txt`). **OVERALL: ALL CHECKS PASS.**

## JOB 1 — Attempt to break the proof

| Claim | Verdict | Brute-force scope | Tightest margin / note |
|---|---|---|---|
| **Lemma 1(ii)** `t−⌊t/q⌋−⌊t/q'⌋ ≥ 1` | **CONFIRMED** | all admissible `t≤3000`, `q,q'≤120` | min value **= 1** (attained, e.g. `t=1,q=2,q'=3`); `≥ t/6` bound never violated. Control: `(q,q')=(2,2),t=2` gives **0** — so the hypothesis `max(q,q')≥3` is load-bearing and correctly stated. |
| **Lemma 3** `L/x=y/g≥3`, `L/y=x/g≥2` | **CONFIRMED** | all primitive pairs `x<y≤3000` | min `L/x = 3`, min `L/y = 2` (both attained at `(2,3)`); zero violations. |
| **Lemma 4** (crux: not both `L_ac/c=L_bc/c=2` in uncovered zone) | **CONFIRMED** (two independent code paths) | (A) all **8 893** primitive both-ratio-2 configs, `c≤3000`; (B) all **48 830 641** uncovered primitive triples, `a≤300` | (A) every both-ratio-2 config satisfies `1/b+1/c ≤ 1/a` (461 sit exactly on the `=` boundary → covered zone, handled by Thm 6); (B) **no** uncovered triple has both ratios 2. Independently re-derived by hand (parity: `c=k·a/2, c=l·b/2`, `k,l` odd `≥3`, `a<b ⇒ k≥l+2 ⇒ 1/a ≥ 1/b+1/c`) — matches. |
| **Lemma 5** `s(n)−2P(n)=X_a+X_b+X_c` and each `X≥1`, sum `≥3` for `n≥c` | **CONFIRMED** | 1 186 uncovered triples `a≤12`, **full lcm-period** each, incl. `n=c` | identity exact everywhere; **min X = 1**, **min(s−2P) = 3** — i.e. the bound `≥3` is *sharp*, not loose. No breakage at `n=c` (all `t_a,t_b,t_c≥1` there). |
| **Theorem 8** `2B(n) > nS` strict | **CONFIRMED** | all **6 945** uncovered primitive triples `a≤20`, **full period**, **110 151 272** `(triple,n)` points | tightest **`2B(n)−nS = 647/1540 ≈ 0.4201 > 0`** at `(a,b,c,n)=(20,21,22,39)`. Strict with comfortable margin — not razor-thin. |
| **Cor 8′ / Thm 9** (`B(m)/m ≤ S` + per-`n` bound ⇒ ★; small-core reduction) | **CONFIRMED** | union bound over `m∈[1,3c]` incl. `m<c` (`a≤15`); direct `B(m)n<2B(n)m` (`a≤6`, `n` over period, `m∈(n,n+L]`); small-core sets | No `m<c` subtlety: `B(m)≤mS` holds for **all** `m≥1` (it is the union bound, independent of the `n≥c` restriction). Small-core cases (e.g. `{4,6,8,9,12}→core{4,6,9}`, `{2,3,4,6}→core{2,3}`) all satisfy ★ on `n≥max(A)`. |
| **(bonus) Covered zone** `2B(n)>nS`? | holds too | 38 554 covered triples sampled | min sampled `2B−nS = 32/15 ≈ 2.13 > 0`, consistent with the writeup's remark that Thm 6's route gives `2B(n)>2n/a≥nS`. |

**No gaps found.** The two sharp points worth flagging (not defects): Lemma 1(ii) and Lemma 5 are *tight* (`=1` and `=3` attained), so the proof has no slack to spare there — but Theorem 8's actual margin (`≈0.42`) shows the composition is not tight, so the strictness is safe.

## JOB 2 — Simplicity adjudication

**Dependency trees for `|A_min| ≤ 3`:**

*Ours (Theorem 9):* Prop 1 (sharp singleton) · Lemma 1(i) nested-floor · **Lemma 1(ii)** one-line floor slack · Lemma 2 (3-set Bonferroni) · Lemma 3 (gcd ratios) · **Lemma 4** (parity dichotomy) · Lemma 5 (charge sum) · Theorem 8 (per-`n` `2B(n)>nS`) · Cor 8′ · Thm 6 (reciprocal-sparse, for `|P|≤2` and covered `|P|=3`). Crux = **Lemma 1(ii) + Lemma 4**.

*Chojecki (Cor 4.7):* Thm 3.1 (singleton) · Thm 3.2 (two-generator) · Lemma 4.3 (refined one-tail transport) · **Theorem 4.5** (pair vs one forbidden modulus) · Prop 4.6 (two-block decomposition) · signed lcm-transport identity (§2). Crux = **Theorem 4.5**, whose core is `E₁(n) ≥ 4` with nested `2b=ka` divisibility cases (`k≥4` vs `k=3`, and within `k=3` an `n`-dependent hunt for `4a ≤ n`).

**The Lean `sorry`.** Chojecki's Lean set is explicitly (lines 164, 2664): *singleton (3.1), singleton-vs-one-tail (4.4), dense case, union-bound reduction*. **Theorem 4.5 is absent** — that is where the `sorry` sits (the `E₁(n)≥4` pair case-analysis). Our proof has exactly one case split (Lemma 4), it is a 4-line parity argument, and it is **`n`-independent** — a one-time structural fact about the triple, not a per-`n` point count. So ours avoids the analogue of his hard case.

**Are they secretly the same?** No. Chojecki proves the *order-based ratio* statement `F(m)/m < 2F(n)/n` by transport (comparing `m` against `n`) using split-counts `F_{a,b|{c}}` and locating "exact-one" points `≤ n`. Ours proves an *order-free absolute* statement `2B(n) > nS` per `n` (no `m`), then closes with the trivial `B(m) ≤ mS`. Different mechanism; and the tight cases are unrelated (his `2b=ka` is an `a–b` relation feeding an `n`-dependent count; our `c=k·a/2, c=l·b/2` is an `a–c`/`b–c` relation checked once). They are not the same proof in disguise.

**Verdict a hostile referee would accept:** *Genuinely simpler for the size-3 statement — defensible, under one precise qualification.* Our proof of `|A_min| ≤ 3` is objectively lighter: no split-count calculus, no block decomposition, no refined transport lemma, and its sole case-analysis (Lemma 4) is a short, `n`-free parity fact, yielding a fully elementary, `sorry`-free route where Chojecki's has a `sorry` on the pair crux. **But the simplicity is bought by narrowness, not by finding a shorter road to the same destination.** Our engine is the per-`n` criterion `2B(n) > nS`, which is **provably false** for larger cores (`A={2p : p≤100}`: `S=0.9014 > 2δ=0.8797`, fails at every large `n`), so the method cannot reach `|A|≥4`. Chojecki's Theorem 4.5 is deliberately a building block of a general pair-vs-tail program (Conj. 4.8; his Prop 4.9 shows that program would settle all of #488). Thus the honest one-line claim is: **"For the size-3 statement in isolation, our proof is strictly simpler and formally cleaner; it is not a simpler proof of a more general theorem, and it does not extend — Chojecki's heavier machinery is the price of a framework that scales."**