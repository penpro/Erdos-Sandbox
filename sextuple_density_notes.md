# Size-6 density inequality `2δ > S` — PROVED (cross-element transfer)

Status: `2δ > S` for **every primitive sextuple** is PROVED at the kernel tier (paper
proof + executed exact finite checks), with a uniform margin `2δ − S ≥ (1009/37800)·S`.
(Fable workflow `size6:transfer`, 2026-07-09; independently re-verified by Claude —
every load-bearing constant and structural claim reproduced exactly, 0 discrepancies.)
This realizes the "size 6 likely closable" prediction for the **density half**. Full
size-6 `2B(n) > nS` is NOT closed (its window/cover lemma `G6`, and its dependence on
size-5's `G3`, remain open). Companion to `quintuple_density_notes.md`.

The per-element kernel that drove size 5 **fails** at size 6 (the free 5-moduli minimum
`E₅ = 49/100 < 1/2`, and it is *realizable*: `a = 105` in the primitive sextuple
`{30,42,63,70,105,175}` has reduced friends exactly `(2,2,2,3,5)`, `E_a = 49/100`, term
`−1/5250 < 0`). So `2δ − S = Σ_a (1/a)(2E_a − 1)` genuinely has negative terms; size 6
needs a **cross-element transfer** that pays for each deficient element out of the small
co-elements its deficiency forces.

## The proof

For element `a` of a primitive sextuple `P`, `E_a := E[1/(1+X_a)]` over its five reduced
friends `m_f = f/gcd(a,f) ≥ 2`; and `2δ − S = Σ_{a∈P} (1/a)(2E_a − 1)` (same
size-independent identity as size 5, verified exact).

**Three certified minima** (finite check with peel-retirement; box `[2..25]` ⊇ all
argmins, all reproduced by Claude):
- `W0 :=` min `E₅` over 5-multisets of integers `≥2` `= 49/100` at `(2,2,2,3,5)`.
- `W1 :=` min with **no entry `= 2`** `= 7423/12600 ≈ 0.58913` at `(3,3,4,5,7)`.
- `W2 :=` min with **at most one entry `= 2`** `= 1087/2100 ≈ 0.51762` at `(2,3,3,5,7)`
  — crucially `W2 > 1/2`.

**Peel inequality.** `1/(1+X+I) ≥ 1/(1+X) − I/2` pointwise (`I∈{0,1}`, since
`1/((1+X)(2+X)) ≤ 1/2`); taking densities, `E_k(t∪{m}) ≥ E_{k−1}(t) − 1/(2m)`. (This
drives the retirement bound that makes the three minima finite checks, and en route
independently **reproves** the size-5 `157/300`.)

**2-friend lemma.** If `a ∤ f` and `f/gcd(a,f) = 2` then `f ≤ (2/3)a`. *Proof:* write
`g = gcd(a,f)`, `f = 2g`; then `gcd(a/g, 2) = 1` so `a/g` is odd; `a/g = 1` would give
`a ∣ f`, excluded, so `a/g ≥ 3`, whence `f = 2g ≤ (2/3)·g·(a/g) = (2/3)a`. (0
counterexamples for `a,f ≤ 3000`.)

**Structure + pairing** (`P = {a₁<…<a₆}`):
- `a₁`'s reduced tuple is **2-free** (a 2-friend `f ≤ (2/3)a₁ < a₁` is impossible), so
  `E_{a₁} ≥ W1`, i.e. its term `≥ (2/a₁)·ε₁`, `ε₁ = W1 − ½ = 1123/12600`.
- `a₂`'s tuple has **≤ one 2** (only `a₁ < a₂` can be a 2-friend), so `E_{a₂} ≥ W2 > ½`,
  term `≥ (2/a₂)·ε₂`, `ε₂ = W2 − ½ = 37/2100`.
- **The pairing.** If `a` is *deficient* (`E_a < ½`) then (contrapositive of `W2 > ½`) its
  tuple has **≥ two** entries `= 2`, i.e. two distinct co-elements `f₁ ≠ f₂` with
  `m = 2`, each `≤ (2/3)a`. Since only `a₁` lies below `a₂`, at least one `fᵢ ≥ a₂`,
  forcing `a ≥ (3/2)a₂`. Hence every deficient `a ∉ {a₁,a₂}` (so `|D| ≤ 4`) and
  `1/a ≤ 2/(3a₂)`.
- Every element has `E_a ≥ W0`, so any term `≥ −(1−2W0)/a = −(1/50)/a`.

**Assembly.**
```
2δ − S ≥ (2/a₁)ε₁ + (2/a₂)ε₂ − (1/50)·Σ_{a∈D} 1/a
       ≥ (2/a₁)ε₁ + (2/a₂)(ε₂ − 2/75)          [|D|≤4, 1/a ≤ 2/(3a₂)]
       ≥ (2/a₁)(ε₁ + ε₂ − 2/75)                 [ε₂−2/75 = −19/2100 < 0, 1/a₂ ≤ 1/a₁]
       = (2/a₁)·(1009/12600) = 1009/(6300·a₁) ≥ (1009/37800)·S     [S ≤ 6/a₁].  ∎
```
Strict, uniform, scale-covariant. Needs only `W0,W1,W2` and the 2-friend lemma — **no
realizability analysis, no enumeration of deficient tuples**.

## Independent verification (Claude, exact `Fraction`)

- `W0 = 49/100`, `W1 = 7423/12600`, `W2 = 1087/2100` — exact, argmins as claimed;
  `2ε₁ − 19/1050 = 1009/6300` ✓, `W2 > ½` ✓.
- 2-friend lemma: 0 counterexamples (`a < 600`). Peel: 0 violations. Identity: exact.
- `2δ > S`: **0 violations** over 83,401 primitive gcd=1 sextuples (entries ≤ 30); the
  bound `2δ − S ≥ 1009/(6300·a₁)`: **0 violations**. Min ratio `(2δ−S)/S = 8179/40361`
  at `{2,3,5,7,11,13}` (7.6× headroom over the proven `1009/37800`).
- Structural claims (a₁ 2-free, a₂ ≤ one 2, deficient `a ≥ 1.5·a₂ ∉ {a₁,a₂}`, `|D|≤4`):
  0 violations on every deficient-element set in range.
- (Workflow's own scope, not re-run here: exhaustive to entries ≤ 48, ~3.17M antichains,
  0 violations; deficiency-targeted enumeration to `a ≤ 630`, 0 violations; worst
  realizable per-element term `−71/94500` at `a=15` in `{6,7,9,10,15,25}`, repaid ~285×.)

**Codex audit (2026-07-10).** Added `audit_sext_density_lemma.py` as an independent
exact-rational backstop for the boxed kernels and arithmetic. The run

```text
python audit_sext_density_lemma.py --bound 25 --friend-limit 3000 --peel-bound 16
```

reproduces `W0 = 49/100` at `(2,2,2,3,5)`, `W1 = 7423/12600` at `(3,3,4,5,7)`,
and `W2 = 1087/2100` at `(2,3,3,5,7)`, checks the 2-friend lemma through `3000`,
checks the peel inequality through `16`, and verifies
`eps1 + eps2 - 2/75 = 1009/12600`. Scope caution: this audits the finite boxed
checks and algebra, not the retirement proof that makes `[2..25]` sufficient.

## The size-6 skeleton (from `size6:lift`, PARTIAL)

With `2δ > S` proved, size-6 gets the same regime tree as size-5:
- **A′ (≥4 good charges):** `2B(n) > nS` all `n`, any gcd — the size-6 analog of
  `ep488_quint_three_good`. Threshold is 4: the flat pointwise weight table has its one
  negative cell `w(p=3,q=0) = −1` at every size `k ≥ 4`, so the flat argument yields
  exactly `g = k−2` goods at every size. (Paper tier.)
- **FD′ (first doubling, `max ≤ n < 2max`):** `2B_P(n) − nS_P = (2B_{P′}(n) − nS_{P′}) +
  (2 − n/max)`, `P′ = P∖{max}` a 5-antichain; **lifts for free once size-5 lands** (uses
  the size-5 separator `2B_{P′}(n) > nS_{P′}`).
- **Bridge B′:** **activated** by the proven margin — `2δ − S ≥ r₆·S` with
  `r₆ = 1009/37800 > 0` gives `2B(n) > nS` for `n ≥ K₆·max` (some explicit `K₆`, via
  `B(n) ≥ δn − 32`). *(The empirical optimal `r₆ = 8179/40361` would sharpen `K₆`.)*
- **Window + `G6`:** the residual `≤(k−2)`-good sets on the bounded window — the size-6
  analog of `G3`, OPEN.

**Open pieces:** (i) `G3′ + C4` (size-5 inventory/cover — **NOT** a min-bound; the
"min ≤ 54" form was refuted 2026-07-10, see `quintuple_density_notes.md`) — inherited
via `FD′`, still the gate for size 5; (ii) `G6` (size-6 window cover, subject to the
same "rider junk" scale-blindness, so also an inventory statement, not a min-bound);
(iii) Lean for the size-6 identity + W-chains (not attempted; same shape as the size-5
files). Size 7: the 2-friend lemma is size-free and `a₁` stays 2-free, but with six
reduced friends the payer minima drop and deficits grow — needs the `E₆` chains, not
attempted.

**Note (2026-07-10):** the size-6 *density* result `2δ > S` above is UNAFFECTED by the
size-5 G3 refutation — it is a standalone, independently-verified inequality (no
min-bound, no cover). Only the *full* size-6 closure inherits the (now harder) size-5
gate.
