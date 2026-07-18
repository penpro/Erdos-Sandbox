# Size-5 density inequality `2δ > S` — PROVED (second-order charge)

Status: density half `2δ > S` **PROVED** (reduction machine-checked in
`lean/ep488/Ep488/Density.lean`, kernel banked; margin `2δ − S ≥ (7/150)·S`). Full
size-5 `2B_P(n) > nS_P` is **NOT closed**. The older `G3′ + C4` formulation has
been superseded by the C-B reorganization below. **UPDATE (2026-07-17):**
W-FIN now proves the C-B residual is finite at paper tier. Its universal
source-owned cutoff is below `2.562 * 10^12`; the residual-specific cutoff is
below `2.494 * 10^6`, still far beyond the current exact bank. Thus full size 5
remains open at the effective coverage step, not at soft finiteness. The audited
SPREAD certificate covers `max/min >= 7`, leaving only the compact box
`min < 3054109696/1225`, `max/min < 7`, `max < 17452056`. **CORRECTION (2026-07-10):** an earlier claim here — "reduced to
ONE lemma G3: min(P) ≤ 54, zero counterexamples in ~12.5M sets" — was **WRONG**, a
census-range artifact (the enumeration stopped at entries ≤ 120). **G3 is FALSE:**
there are window-relevant `≤2`-good gcd=1 quintuples with `min > 54` — confirmed
`{108,140,210,315,378}` (min 108), `{216,232,348,522,783}` (min 216), and a family
with `min` bounded only by the window (`≤ 4968`), *unbounded* without it. #488 itself
**holds on all of them** (margins ≥ 5) — this refutes the proposed closing lemma, not
the problem. (Claude, 2026-07-08/10; the refutation is adversarially verified +
independently re-confirmed.) Companion to the size-≤4 charge development in
`lean/ep488`, the size-6 result in `sextuple_density_notes.md`, and Codex's separator
census in `adversary_collab_chat.md`.

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
   **Codex follow-up:** done. The audit script now checks all 35 multisets over
   `{2,3,5,7}`, all 126 prime multisets with primes `<=13`, and records the two
   collision warnings above; `python audit_quint_density_lemma.py --brute 50`
   returns `RESULT: PASS`.
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

## Full size-5 #488: the regime decomposition (open gate: C-B-FIN)

*Current status (2026-07-10): the decision tree below is valid on its stated
regimes, but the old G3 min-bound and the claimed C1/C2/C3 completeness are false.
The C-B covering theorem later in this note replaces most of `G3′ + C4`. Full size 5
is reduced to the still-open universal statement `C-B-FIN`, plus a finite tower bank
once a genuine bound is proved. Range saturation is computation, not finiteness.*

**The decision tree** (first matching regime wins; charges are scale-invariant):

- **A (`≥3` good charges)** — all `n`, any gcd: `ep488_quint_three_good` (Lean).
- **FD (first doubling, `max ≤ n < 2·max`)** — UNCONDITIONAL. With `P' = P∖{max}` (a
  primitive 4-antichain) and `n < 2·max`, `max` is the only new multiple and (by
  primitivity) is uncounted in `B_{P'}`, so `B_P(n) = B_{P'}(n) + 1` and
  `2B_P(n) − nS_P = (2B_{P'}(n) − nS_{P'}) + (2 − n/max)`; the first term is `> 0` by
  the **size-4 separator** `2B_Q(n) > nS_Q` (any primitive quad, `n ≥ max Q`; verified,
  Quad.lean internals), the second `> 0` since `n < 2·max`. *(Identity verified exact
  0/9839; separator 0 violations.)*
- **B (bridge, `7nS > 1135 − 157S`, incl. all `n ≥ 33·max`)** — now UNCONDITIONAL via
  the drift theorem U2 below.
- **C0 (gcd `= g ≥ 2`)** — reduce to the base shape `P₀` via `B_{tP₀}(n) = B_{P₀}(⌊n/t⌋)`;
  it suffices to prove the **tower form** `2B_{P₀}(m) ≥ (m+1)S₀` on
  `m ∈ [max P₀, cap]`, `cap =` largest `m` with `7(m+1)S₀ < 1135`. (Tower form also
  gives the strict raw form at `g = 1`.)
- **C (`≤2`-good, gcd `= 1`, window `n ∈ [2·max, bridge)`; nonempty only if
  `max·S ≤ (1135−157S)/14 ≈ 81`)** — covered by three interlocking pieces:
  - **C1 (finite bank):** a machine-verified tower-form check over **22,693** sets
    (all window-relevant `≤2`-good gcd=1 quintuples with 4 smallest `≤ 120`, plus
    family continuations), **zero failures**; global worst margin `638/255 ≈ 2.502` at
    `{76,114,153,171,285} = {153} ∪ 19·{4,6,9,15}`, `n = 303` (reproduced exactly).
  - **C2 (Master 4+X theorem, uniform, U2-free):** for a fixed primitive quad `Q` and
    admissible `X`, `c_Q·X ≥ D_Q + 1 + 2γ + S_P` ⟹ #488 for `Q∪{X}` and all scalings,
    all `n` (`c_Q = 2δ_Q−S_Q > 0`, `D_Q < 16`, `γ = charge_Q(X) ≤ 2`). Generic
    corollary via `E₃ ≥ 41/72`: `X > 36(22+S_Q)/(5S_Q)` suffices — so every 4+X family
    has an explicit finite residual (banked).
  - **C3 (Master e+tQ theorem, uniform, U2-free):** for `P_t = {e} ∪ t·Q₀`, closes all
    `t ≥ t₀` (exact rational threshold); flagship `{45} ∪ t·{4,6,9,10}` has `t₀ = 85/4`.

**The open piece — `G3′ + C4` (NOT a min-bound).** *Every window-relevant
(`7·max·S ≤ 1135`) `≤2`-good gcd=1 primitive quintuple lies in the inventory.* This is
what size-5 still needs, and it is genuinely open.

**⚠ CORRECTION (2026-07-10) — the min-bound form G3 is FALSE.** An earlier version here
claimed the sufficient form "`min(P) ≤ 54`, all ~12.5M enumerated sets satisfy it,
extremal `{54,80,90,120,135}`." That was a **census-range artifact** (the enumeration
stopped at entries ≤ 120). Confirmed counterexamples (gcd=1, antichain, exactly-2-good,
window-relevant, `min > 54`; #488 holds on each with margin ≥ 5):

| `P` | `min` | `max·S` |
|---|---|---|
| `{108,140,210,315,378}` | 108 | 51/5 |
| `{116,117,174,261,435}` | 116 | 657/52 |
| `{216,232,348,522,783} = {216} ∪ 29·{8,12,18,27}` | 216 | 47/4 |
| `{2376,2392,39468,59202,88803}` | 2376 | 317/4 |

- **`min` is unbounded *without* the window** (e.g. `{60q,12p} ∪ qp·{6,10,15}` = dual of
  `{4,6,10,5q,p}`, `min = 60q → ∞`). With the window it is bounded, sharpest candidate
  **`≤ 4968`** — but that is `PROVED-MODULO-UNBOUNDED-REGION` (verified-complete only for
  dual cores `min(D) ≤ 24`), and even if proved gives `max < (1135/7)·4968 ≈ 8·10⁵`, so
  the "finite ⟹ one enumeration" pipeline is numerically dead. The claim "two
  loosely-coupled goods are impossible" is also refuted (goods 216 & 232 in the table
  have cross-terms `1/27, 1/29`).
- **Root cause — "rider junk":** on the *dual* side (`P ↦ lcm(P)/P`), a coprime factor
  `r` multiplies an element (hence `min(P) = lcm(D)/max(D)`) while changing **no charge**
  and preserving gcd=1. Charge conditions are scale-blind on the dual side, so every
  charge-based lemma bounds only *shapes*, never integer values — which is exactly why no
  `min`-bound closes it.
- **The C1/C2/C3 inventory is provably INCOMPLETE:** C1 excludes these (4th-smallest
  `> 120`), and the two-junk-parameter shapes `{8r₅, 216r₄} ∪ r₄r₅·{12,18,27}` fit
  neither C2 (needs 4 fixed elements) nor C3 (needs a fixed base quad).

**Corrected open problem (both open):**
- **G3′ (inventory, the hard core):** every window-relevant `≤2`-good gcd=1 quintuple is
  `{scaled core} ∪ {rider w₄·r₄} ∪ {coupler w₅·r₅}` with `(core, w₄, w₅)` in a finite
  explicit list and `r₄, r₅` free coprime junk. (Done only for dual cores `min(D) ≤ 24`.)
- **C4 (a new 2-junk-parameter Master theorem):** `2B(n) > nS` uniform in coprime
  `(r₄, r₅)` per listed shape — believed provable at U2 tier (worst observed window
  margin `5.0495`, machinery is `n`-aware), the recommended next attack.

*(Codex independently spotted early instances of this — the `{56,72,84,126,189}`,
`{56,84,108,126,189}` C3-continuation candidates below — which the full refutation
now subsumes.)*

### The C-B reorganization (2026-07-10) — a 3-line theorem replaces most of G3′+C4

**Theorem (C-B, finite-`n` Bonferroni window bound; PROVED — now Lean-verified).** For
any primitive quintuple and any `n`:

```
2B(n) − nS  ≥  Σ_a (1 − charge(a))·⌊n/a⌋ − 5,     and cleaner:  2B(n) ≥ 2s(n) − 2P₂(n),
```

so `s(n) ≥ 2P₂(n) + 5 ⟹ 2B(n) > nS` (the covering criterion). *Proof.* Two-term
Bonferroni `B(n) ≥ s(n) − P₂(n)` (pointwise `singles − pairs ≤ [union]`, i.e.
`d − C(d,2) ≤ [d≥1]`) + the floor bound `nS < s(n) + 5`. ∎ *(986 exact spot checks, 0
violations.)* **`lean/ep488/Ep488/CB.lean` machine-checks this, sorry-free** on the
three standard axioms (`cb-axioms.txt`, in CI): `cb_bonferroni5` (`B ≥ s − P₂` via the
32-case `bonf_bool`), `floor_bound5`, and `cb_cover5` (`s ≥ 2P₂ + 5 ⟹ 2B(n) > nS`,
division-free). This is the covering theorem for regime C, now at the same tier as the
`|core|≤4` result.

Since FD covers `n ∈ [max, 2max)` and the drift bridge covers the top, regime C closes
for `P` outright whenever `Φ(n) ≥ 5` on `[2max, bridge)`. For the `≤2`-good class,
the following floor-error estimate gives the clean sufficient **criterion**

```
CRIT(P) := max(P) · (S − 2P₂)  >  7/2.
```

Here is the missing derivation of the constant `2`. Put
`c_a = 1 − charge(a)` and `t_a = ⌊n/a⌋`. With
`q_{a,f} = f/gcd(a,f)`, the nested-floor identity gives

```
X_a = t_a − Σ_{f≠a} ⌊t_a/q_{a,f}⌋ ≥ t_a c_a,
Φ(n) = Σ_a X_a.
```

Therefore

```
Φ(n) ≥ n(S−2P₂) − Σ_a {n/a} c_a > n(S−2P₂) − 2.
```

The last step is **specific to the `≤2`-good class**: at most two coefficients
`c_a` are positive, each is at most `1`, and every nonpositive coefficient makes
the fractional-part error favorable. Thus `n ≥ 2max(P)` and `CRIT > 7/2` imply
`Φ(n) > 5`, hence the Lean-checked C-B covering criterion. The C-B theorem itself
is unconditional; only this `7/2` corollary uses the `≤2`-good hypothesis.

**Dual-side identity (exact, verified):** with `D = lcm(P)/P` (involution on gcd=1
antichains), `CRIT = (ΣD − 2·Σ_{i<j} gcd(d_i,d_j)) / min(D)` — all small numbers. Under
junk multiplication (any element, any direction) the numerator grows linearly while the
denominator is eventually fixed (≤ the second-smallest element), so **every junk ray
exits the residual after finitely many steps** — junking a co-bad element eventually
flips it good (exits the class to regime A), junking anything else drives CRIT up. This
is why C-B retires *every* rider-junk family uniformly (the G3-refutation sets have
CRIT `= 4, 4.97, 4.5` — all covered), where G3′+C4 needed per-shape Master theorems.

**Census (`census cb`, exact i128, `std::thread`-parallel, dual cores ≤ M; the whole
enumerate + tower-form bank runs in one Rust pass):**

| M | class | residual (CRIT ≤ 7/2) | largest primal max in residual | bank fails / worst margin |
|---|---|---|---|---|
| 40 | 141 | 50 | 513 | 0 / — |
| 60 | 549 | 125 | 513 | 0 / — |
| 120 | 3244 | 195 | 513 | 0 / `22/9` |
| 180 | — | 261 | 513 | 0 / `22/9` |
| 240 | — | 276 | 513 | 0 / `22/9` |

The **primal max saturates at 513 from M=40 through M=240** (a 6× range of dual
entries) while rider maxes reach ~2·10⁵ — the residual growth is entirely inside a
bounded primal box, and every residual set passes its tower-form window (worst margin
`22/9` at `{104,156,216,234,351}`, `m=415`, stable). *(Rust; do NOT read saturation as
proof — see C-B-FIN below.)* The negative-CRIT
sublist is *exactly* the classic `S ≤ 2P₂` residual (`{4,6,9,10,15}`, `{12,18,20,30,45}`,
`{4,6,10,14,15}` — the third visible only at `M ≥ 105`, a live demonstration of the
range-trap this census is built to avoid).

**Bank (COMPUTED, exact):** all **195** residual sets pass their full window in the
tower form `2B(m) > (m+1)S` (covers all gcd scalings via C0) — **0 failures**, worst
margin `22/9` at `{104,156,216,234,351}`, `n=415`.

**Updated endpoint (2026-07-17):** W-FIN proves that the C-B residual
(`≤2`-good, gcd=1, window-relevant, `CRIT ≤ 7/2`) is finite. Codex's hostile
review found no fatal gap. The universal source-owned audit gives a cutoff below
`2.562 * 10^12`, and its residual-specific cofactor refinement gives
`2.494 * 10^6`; see `cbfin_reduction_notes.md` and
`REFEREE_WFIN.md`. This **supersedes G3′+C4 as the soft finiteness argument**.
Honest tier: C-B theorem PROVED; C-B-FIN PROVED at paper tier; census/bank
COMPUTED only through dual entries `≤240`. Full size 5 remains **OPEN** because
the effective cutoff is nowhere near the bank. Do not infer bank completeness
from saturation; that is the exact trap that produced the G3 overclaim.

### C4-canonical theorem + G3′ scope findings (2026-07-10, workflow + verified)

**C4-canonical (PROVED, U2 tier — the one shape family with a full uniform theorem).**
`P(m,p) = {8p, 72m, 4mp, 6mp, 9mp}`, valid iff `m` odd `≥ 3`, `gcd(p,6)=1`,
`gcd(m,p)=1`, `p ≥ 5`. Exact collapse (verified):
`B(n) = ⌊n/8p⌋ + ⌊n/72m⌋ + w̃(⌊n/mp⌋)` with
`w̃(q) = ⌊q/4⌋+⌊q/6⌋+⌊q/9⌋−⌊q/8⌋−⌊q/12⌋−⌊q/18⌋−⌊q/72⌋ ≥ 5` for `q ≥ 18`
(one-period check; `w̃(q+72) = w̃(q)+18`). Uniform margin `> 197/36` for every valid
`(m,p)` except `(3,5), (3,7)` — closed by exact scans (raw minima `487/108` @ `n=239`,
`71/21` @ `n=223`, both in the FD strip; verified to the digit). With FD, **every
member closed for all `n ≥ max`**. *(In-workflow overclaim caught by its own verifier:
the first "exact pin-down" missed the `v₃=2` riders — e.g. `P(5,7) = {56,140,210,315,360}`
— and was extended before proving.)* Splice into C-B: the canonical members in the C-B
residual are exactly `P(3,r₅)`, `r₅ ∈ {5,7,11,13,17,19}` (CRIT `12/5, 2, 9/4, 5/2, 3,
13/4`; `r₅=23` exits at `15/4`) — **including the census saturation point
`P(3,19) = {152,216,228,342,513}`**. These 6 are now theorem-covered, not just banked.
CE1-shape (dual `{10,12,18,·,·}`): pinned sub-family proved, full class NOT — do not
bank "shape retired". CE2 (`{9r} ∪ s·{4,6,9,15}`): reduced to finitely many C3
one-parameter families (`r ≤ 20`, `s ≤ 19`), per-`r` closures not executed.

**G3′ scope corrections (all verified):** the `min(D) ≤ 24` completeness boundary is
**refuted** (irreducible dual cores up to `min(D)=210` = dual of `{2,3,5,7,11}`); the
shape-canonicalizer is non-confluent, so all prior core *counts* are greedy artifacts;
the core list is **not converged** — extending the smooth probe 1400→6000 produced new
window-relevant exactly-2-good gcd=1 sets outside the old C1 bank, e.g.
`{6,21,98,245,343}` and `{6,14,147,245,343}`. **No threat to the C-B frame:** both have
`CRIT = 266/5, 301/5` (C-B-retired) and *empty* C-windows (`2max > N*`), so FD+bridge
alone closes them — but they demonstrate again that only C-B's uniform coverage, not
any enumerated inventory, is trustworthy. Supporting lemma "(A)" for the anchor
route is in fact **PROVED** by the existing size-4 theorem, with no new enumeration
needed. For an antichain `D={d_i}_{i=1}^4`, put `L=lcm(D)` and `P_i=L/d_i`, then
divide `P` by its gcd. This is a primitive quadruple, and

```
charge(P_i) = (1/d_i) Σ_{j≠i} gcd(d_i,d_j).
```

The size-4 theorem says at least two `P_i` are good, so at most two `d_i` satisfy
`d_i ≤ Σ_{j≠i} gcd(d_i,d_j)` (the dual "self-bad" condition). This hereditary
four-subset constraint is available for the C-B-FIN attack, although it does not
by itself prove finiteness.

### Strong-gcd block reduction (2026-07-10) — C-B-FIN reduced to three components

**Theorem (PROVED).** Let `D={d_1<...<d_5}` be a gcd-1 divisibility antichain
corresponding to a window-relevant `≤2`-good primal quintuple, so

```
7ΣD ≤ 1135 d_1,
```

and at least three indices are dual self-bad:
`d_i ≤ Σ_{j≠i}gcd(d_i,d_j)`. Form the **strong-gcd graph** on `D`, joining `d_i`
and `d_j` when

```
4 gcd(d_i,d_j) ≥ min(d_i,d_j).
```

Then:

1. the graph has at most three connected components;
2. every component belongs, up to one integer scale factor, to a finite effective
   library of primitive integer block shapes;
3. the one- and two-component cases form a finite set. Consequently **C-B-FIN is
   reduced to the three-component case alone**.

*Proof of 1–2.* If `d_i` is self-bad, one of its four gcd terms is at least
`d_i/4`, so `d_i` is incident to a strong edge. At least three vertices are
self-bad, hence at least three vertices are nonisolated; a graph on five vertices
with that property has at most three components.

For a strong edge, write `x=min(d_i,d_j)`, `y=max(d_i,d_j)`, and
`g=gcd(d_i,d_j)`. The reduced edge label `(r,s)=(x/g,y/g)` satisfies

```
r ∈ {2,3,4},   2 ≤ s ≤ 632,   gcd(r,s)=1.
```

Indeed, antichainness gives `r,s≥2`, strongness gives `r≤4`, and the window gives
`y≤(1135/7−4)d_1=(1107/7)d_1`. Since `x≥d_1`,
`s/r=y/x≤1107/7`, hence `s≤⌊4·1107/7⌋=632`. Thus there are only finitely many
edge-labelled graphs. Along each connected component the edge ratios determine
all entries up to a common rational scale; after clearing denominators and making
the weight vector primitive, integrality makes that scale an integer. This gives
a finite block library and at most three integer scale variables.

*Proof of 3.* One component has the form `D=tW` with primitive `W`; gcd(`D`)=1
forces `t=1`.

For two components write `D=tW ∪ uV`, with `W,V` primitive. Then gcd(`t,u`)=1,
and for every cross pair

```
gcd(t w_i, u v_j) ≤ w_i v_j.
```

The component sizes are `(1,4)` or `(2,3)`. A size-1 or size-2 antichain has no
self-bad element; a size-3 antichain has at most one (two self-bad indices would
force the same pairwise gcd to equal half of two distinct entries); and a size-4
antichain has at most two by the proved dual size-4 anchor. Since the full set has
at least three self-bad indices, some full-self-bad element is internally good in
its own block. If it is `t w_i`, put

```
a_i = w_i − Σ_{w_k∈W, k≠i} gcd(w_i,w_k) > 0.
```

Its full badness and the cross-gcd bound give

```
t a_i ≤ Σ_{v_j∈V} gcd(tw_i,uv_j) ≤ w_i Σ_j v_j,
```

so `t` is bounded by the fixed block shapes. The window bounds `u/t` in terms of
the same shapes, hence `u` is bounded too. Since the block library is finite, all
one- and two-component cases are finite. ∎

**Former canonical open sublemma (`C-B-3COMP`).** Prove that the three-component
strong-gcd case is finite (or empty). Its component-size pattern is only `(3,1,1)`
or `(2,2,1)`. The hereditary four-subset anchor adds critical-edge inequalities:
if `h_i=d_i−Σ_{j≠i}gcd(d_i,d_j)≤0`, then deleting a vertex `k` makes `i` good
exactly when `h_i+gcd(d_i,d_k)>0`. This forces the isolated good vertices to pay
for several bad vertices in the nontrivial blocks.

**COMPUTED evidence (not proof):** among the 195 exact `census cb 120` residuals,
the strong-gcd component counts are

```
one component:   156
two components:   39
three components:  0
```

There were 188 residuals with exactly three self-bad indices and 7 with four;
the largest observed reduced strong-edge label was `(r,s)` with `r≤4`, `s≤35`.
Thus every currently banked residual lies in one of the two sectors proved finite
above. This does not establish `C-B-3COMP` universally. W-FIN now bypasses this
sublemma for qualitative finiteness, though the strong-component route may still
be useful for obtaining a practical cutoff.

---

## The drift theorem U2 and the `33·max` bridge (regime B)

*Status: U2 **PROVED** at the `E4`-kernel tier (elementary induction + executed
one-period finite checks; prover + independent verifier). Independently re-verified
(constants, thresholds, equality set, `(A,n)` spot checks — 0 discrepancies).*

For four moduli `m₁,…,m₄ ≥ 2` let `f(J) = Σ_{j≤J} (1/(1+X(j)) − 1/2)`,
`X(j) = #{i : mᵢ ∣ j}` — the per-element *drift* (partial-sum) version of the kernel.

- **U1 (dip).** `inf_J f(J) = −1/12`, attained ONLY at moduli `(2,2,3,5)`, `J = 6`.
  For 1, 2, or 3 moduli, `f ≥ 0` universally. (Verified; not load-bearing.)
- **U2 (drift), PROVED.** `f(J) ≥ (7/300)·J − 7/30` for all `J ≥ 0` — **jointly optimal**
  (equality iff moduli `(2,2,3,5)` and `J ≡ 10 (mod 30)`). Proof: a 4-lemma induction
  (M pointwise / P peel / R six rational comparisons / F periodic propagation) up the
  size chain with exact optimal constants `(c,d) = (1/4,0), (5/36,1/18), (5/72,1/9),
  (7/300,7/30)` and retirement thresholds `m ≥ 5, 8, 11`; 58 one-period kernel checks.
  (`c₃ = 41/72 − 1/2 = 5/72`.) Divisor-monotonicity raises `f` pointwise at every `J`,
  and one full period advances `f` by `L·(E4 − 1/2) ≥ L·(7/300)` — the `E4` kernel — so
  a per-period check suffices; a byproduct is a second independent proof of
  `E4 ≥ 157/300`.

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

**Drift bridge theorem** (regime B, unconditional). Summing U2 at `J = ⌊n/a⌋` over the
five elements (`⌊n/a⌋ = n/a − {n/a}`, `{n/a} ≤ 1 − 1/a`), for every primitive quintuple
and `n ≥ max`: `2B(n) − nS ≥ (7/150)nS − 7/3 − (157/150)(5 − S)`, so `2B(n) > nS`
whenever `7nS > 1135 − 157S` — in particular `nS ≥ 163`, hence `n ≥ 33·max`
(`K = 227/7`). The window is empty unless `max·S ≤ 1135/7 ≈ 162.1`.

**Why the `≤2`-good class being infinite does not by itself block the cover.** The
class is infinite (`{12,20,30,45,15k}` is exactly-2-good for every valid `k`; also
`{3,4,2q,5q,qm}`). The old claim that G3 bounded `min(P)` and made C1/C2/C3 complete
is false. The replacement is C-B: every member with `CRIT > 7/2` is retired
uniformly, including the known rider-junk families. What remains is precisely the
`CRIT ≤ 7/2` residual. W-FIN proves this class is finite, but only with an
impractical cutoff; the current bank covers only the residuals actually enumerated.

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
