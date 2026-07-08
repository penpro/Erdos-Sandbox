# Lean formalization of Erdős #488 (|primitive core| ≤ 3) — COMPLETE, sorry-free

Lean 4 + Mathlib project. Toolchain: `leanprover/lean4:v4.31.0`, Mathlib
`v4.31.0` (see `lean-toolchain`, `lakefile.toml`).

**Status: the full `|primitive core| ≤ 3` case of Erdős #488 is machine-verified,
sorry-free.** The top theorem is `Erdos488.ep488_core` in `Ep488/Reduction.lean`:
for every finite set `A` of positive integers whose primitive core has ≤ 3
elements, and all `m > n ≥ max A`,

```
n * (Bgen A m).card < 2 * m * (Bgen A n).card      -- i.e. B_A(m)/m < 2·B_A(n)/n
```

where `Bgen A n = {k ∈ (0,n] : some element of A divides k}`.

Every lemma in the chain is `#print axioms`-clean — it depends only on
`propext, Classical.choice, Quot.sound`, with **no `sorryAx` and no literal
`sorry`**. The audits are committed: [`axioms-check.txt`](axioms-check.txt)
(Basic), [`counting-axioms.txt`](counting-axioms.txt) (Counting),
[`reduction-axioms.txt`](reduction-axioms.txt) (Reduction),
[`certificate-axioms.txt`](certificate-axioms.txt) (Certificate) — 21 theorems.

Build & check:
```
lake exe cache get         # once: downloads prebuilt Mathlib oleans
lake build Ep488           # compiles the whole development clean
lake env lean Ep488/ReductionCheck.lean   # prints the axiom audit for the top theorems
```

## The three files

### `Ep488/Basic.lean` — arithmetic core

- **`floor_bound`** (Lemma 1(ii)): for `t ≥ 1`, `q ≥ 2`, `q' ≥ 3`,
  `1 ≤ t − t/q − t/q'`. The one input to each per-generator charge.
- **`ratio_bounds`** (Lemma 3): for primitive `x < y`,
  `y/gcd(x,y) ≥ 3` and `x/gcd(x,y) ≥ 2`.
- **`parity_dichotomy`** (Lemma 4): in the uncovered zone `b·c < a·(b+c)`,
  `lcm(a,c)` and `lcm(b,c)` cannot both equal `2c`. **This is the single
  substantive step of the whole proof** — the thing that forces every charge
  positive, and (in the transport route) exactly the case that carries Chojecki's
  Lean `sorry`. Here it is a ~40-line elementary `gcd`/parity argument.

### `Ep488/Counting.lean` — the ordered primitive triple (both zones)

- **`bonferroni`** (Lemma 2): `s(n) ≤ B(n) + P₂(n)` — the finite-`n` two-term
  inclusion–exclusion (density-level = classical Heilbronn–Rohrbach 1937), via
  `Nat.Ioc_filter_dvd_card_eq_div` (count of multiples `= n/d`) and the 3-set
  `Finset.card_union_add_card_inter` chain.
- **`charge`** (Lemma 5): `2·P₂(n) + 3 ≤ s(n)` for `n ≥ c` — the charge
  decomposition, using `floor_bound`, `ratio_bounds`, and `parity_dichotomy`.
- **`two_B_gt_nS`** (Theorem 8): `n·(bc+ac+ab) < 2·B(n)·abc`, i.e. `2B(n)/n > S`.
- **`ep488_uncovered_triple`**: the **uncovered** zone `b·c < a·(b+c)`.
- **`B_ge_floor_add_one`** + **`ep488_covered_triple`**: the **covered** zone
  `a·b + a·c ≤ b·c` (pure union bound).
- **`ep488_triple`**: the two zones combined — EP488 for every ordered primitive
  triple `a < b < c` (`Bset` form).

### `Ep488/Reduction.lean` — general `A`, singleton/pair, and the reduction

- **`Bgen`** and `mem_Bgen`: `B` over an arbitrary `Finset ℕ`, plus the
  reconciliations `Bgen_singleton`, `Bgen_pair_eq`, `Bgen_triple`.
- **`ep488_singleton`** (`A = {a}`) and **`ep488_pair`** (`A = {a,b}`, primitive):
  pure union-bound proofs (`a·B(n) > n`, upper bounds on `B(m)`), no charge/parity.
- **`core`**, `exists_core_dvd`, **`Bgen_core_eq`**: the primitive core
  (`∣`-minimal elements) and the invariance `B_A = B_{core A}` (every element of
  `A` is a multiple of the smallest element of `A` dividing it — `Finset.min'`).
- **`core_antichain`**: distinct core elements never divide one another.
- **`ep488_primitive`**: EP488 for *any* positive `∣`-antichain of size ≤ 3,
  dispatched by `card_eq_one/two/three` with a `min' < middle < max'` extraction.
- **`ep488_core`**: the final theorem (above).

### `Ep488/Certificate.lean` — the per-set certificate engine

Turns the "compute exact ratio bounds and check `β < 2α`" strategy into rigorous
Lean:

- **`ep488_of_certificate`**: if `c/d ≤ B_A(x)/x ≤ e/d` for all `x ≥ N ≥ 1` and
  `e < 2c` (i.e. `β < 2α`), then EP488 holds for `A`. The clean interface between
  a finite computation and the theorem.
- **`Bgen_add_period`** / **`Bgen_add_mul_period`**: `B_A(x + L) = B_A(x) + B_A(L)`
  (and the `q`-fold version) whenever every element of `A` divides `L`. This is
  *why* the infinite check collapses to one period — proved by induction on the
  one-step count increment plus `L`-periodicity of "divisible by some element",
  with no residue-bijection machinery.

Together these are the sorry-free core of the finite-window / periodicity
principle: for any fixed `A` (including open `|core| ≥ 4` sets), an exact
one-period computation yields the `[c/d, e/d]` bounds that `ep488_of_certificate`
consumes. (Automating the extraction of those bounds from one period is the next
step; the two pieces here are the load-bearing lemmas.)

## Honest scope

This formalizes the `|primitive core| ≤ 3` case only. The general Erdős #488
(**arbitrary** finite `A`, i.e. `|core| ≥ 4`) **remains open** — it is not proved
here or, to our knowledge, anywhere. The result is Chojecki's claimed Cor 4.7
(his Lean bundle gates it behind one `sorry`); the method backbone is the
classical **Heilbronn–Rohrbach inequality (1937)**. This development is an
independent, sorry-free machine verification of that sub-case, not a new theorem
and not a resolution of #488. See `../../literature_notes.md`,
`../../triples_writeup.md`, `../../writeup/erdos488_triples.pdf`, and the novelty
ledger in `../../adversary_collab_chat.md`.
