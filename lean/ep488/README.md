# Lean formalization of Erdős #488 (|primitive core| ≤ 4) — COMPLETE, sorry-free

Lean 4 + Mathlib project. Toolchain: `leanprover/lean4:v4.31.0`, Mathlib
`v4.31.0` (see `lean-toolchain`, `lakefile.toml`).

**Status: the full `|primitive core| ≤ 4` case of Erdős #488 is machine-verified,
sorry-free.** The `≤ 3` case (`Erdos488.ep488_core`, Chojecki's Cor 4.7) and the
`= 4` case (`Erdos488.ep488_core_le_four`, formalizing the internal charge
addendum `../../quadruple_charge_notes.md` — novelty pending human/literature
review) share the same statement shape: for every finite set `A` of positive
integers whose primitive core has ≤ 4 elements, and all `m > n ≥ max A`,

```
n * (Bgen A m).card < 2 * m * (Bgen A n).card      -- i.e. B_A(m)/m < 2·B_A(n)/n
```

where `Bgen A n = {k ∈ (0,n] : some element of A divides k}`.

Every lemma in the chain is `#print axioms`-clean — it depends only on
`propext, Classical.choice, Quot.sound`, with **no `sorryAx` and no literal
`sorry`**. The audits are committed: [`axioms-check.txt`](axioms-check.txt)
(Basic), [`counting-axioms.txt`](counting-axioms.txt) (Counting),
[`reduction-axioms.txt`](reduction-axioms.txt) (Reduction),
[`certificate-axioms.txt`](certificate-axioms.txt) (Certificate),
[`quad-axioms.txt`](quad-axioms.txt) (Quad — incl. `ep488_core_le_four`,
`ep488_quad_prim`, and the Lemma B chain), [`quint-axioms.txt`](quint-axioms.txt)
(Quint — the size-5 three-good proposition),
[`density-axioms.txt`](density-axioms.txt) (Density — the size-5 `2δ>S`
reduction), [`cb-axioms.txt`](cb-axioms.txt) (CB — the C-B covering criterion),
[`ceiling-axioms.txt`](ceiling-axioms.txt) (Ceiling — the k=5 self-bad
ceiling: no antichain quintuple has five bad elements),
[`transport-axioms.txt`](transport-axioms.txt) (Transport — the Duality
Transport identity: dual self-bad ⟺ primal bad),
[`drift-bridge-axioms.txt`](drift-bridge-axioms.txt) (DriftBridge — the U2
bridge algebra, the concrete quintuple bridge, and the tower-form seam), and
the drift-kernel audits ([`drift-kernel-reduction-axioms.txt`](drift-kernel-reduction-axioms.txt),
[`drift-retirement-axioms.txt`](drift-retirement-axioms.txt) — the U2 kernel
ladder port, in progress). The root CI regenerates all of these on every push and enforces a
**positive allowlist** — it fails if any checked theorem depends on *any* axiom
outside `{propext, Classical.choice, Quot.sound}` (not just a `sorryAx` grep),
which also rules out a stray `native_decide` (`Lean.ofReduceBool`).

Build & check:
```
lake exe cache get         # once: downloads prebuilt Mathlib oleans
lake build Ep488           # compiles the whole development clean
lake env lean Ep488/ReductionCheck.lean   # prints the axiom audit for the top theorems
```

## The files

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
- **`ep488_of_window`**: the full finite reduction. To prove EP488 for a fixed
  `A` it suffices to check, over ONE period `L`, the two density slopes
  `c·L ≤ d·B(L) ≤ e·L`, the ratio bounds `c·x ≤ d·B(x) ≤ e·x` on the single window
  `[N, N+L)`, and `e < 2c`. Writing `x = x₀ + q·L`, the window value plus the slope
  propagates the bound to every `x ≥ N`, so no monotonicity argument is needed.

Together these are the sorry-free finite-window / periodicity principle: for any
fixed `A` (including open `|core| ≥ 4` sets), a one-period computation feeding
`ep488_of_window` gives a machine-checked proof of EP488 for that set. This does
NOT prove the general `|core| ≥ 4` case (infinitely many sets, unbounded `L`) — it
makes each individual set rigorously certifiable.

### `Ep488/Quad.lean` — the `|primitive core| = 4` case (charge method)

Formalizes the two-good-charge argument of `../../quadruple_charge_notes.md`
(Codex-authored, Claude-audited) end-to-end, sorry-free:

- **`card_ie4`** / **`two_B_eq`**: exact 4-set inclusion–exclusion in ℤ
  (`2B = s − 2P₂ + 2T₃ − 2T₄` route), via a pointwise Boolean identity.
- **`ep488_quad_two_good`**: if two of the four generators have good charge, the
  pointwise weight table gives `Y_H ≥ 2`, hence `2B(n) > nS`, hence #488 for the
  quadruple.
- **`least_good`** (Lemma A): the least element is always good.
- **`aterm_case32`**, **`b_bad_five_shapes`**, **`c_good_of_b_bad`** (Lemma B):
  if `b` is bad then `q = 2`, the reduced ratios `c/b`, `d/b` fall into exactly
  five shapes (`interval_cases` on the cofactors), and `c` is good in each — so
  every primitive quadruple has ≥ 2 good charges.
- **`ep488_quad_prim`**: EP488 for any sorted primitive quadruple `a<b<c<d`.
- **`ep488_primitive_le_four`** / **`ep488_core_le_four`**: the size-≤4 antichain
  and the general-`A` core reduction (the named theorem).

### `Ep488/Example.lean` — the engine, exercised

- **`ep488_example_4_6_10_15`**: EP488 for `A = {4,6,10,15}` — a `∣`-antichain of
  size 4 (the smallest-lcm size-4 primitive core, `lcm = 60`), so it is **outside**
  the `|core| ≤ 3` theorem. Proved end-to-end by `ep488_of_window`: slopes
  `4·60 ≤ 12·B(60) ≤ 6·60` and the ratio bounds on the window `[15, 75)`, all
  discharged by **kernel `decide`** (not `native_decide`) — so the theorem depends
  only on `propext, Classical.choice, Quot.sound`. This is the certificate engine
  verified by using it: a real, machine-checked #488 instance for a size-4 set.

### `Ep488/Quint.lean` — size 5, the three-good-charge proposition (PARTIAL)

Mechanical 4→5 lift of `Quad.lean`. **`ep488_quint_three_good`**: a primitive
quintuple with **≥ 3 good charges** satisfies #488 — via `card_ie5` (exact 5-set
inclusion–exclusion), the 4-partner charge bound, and the `H=2, G=3` pointwise
weight table (`yh_raw_nonneg5`, a 32-case check). **Coverage, not closure**: it
covers ~99.996% of primitive quintuples (entries ≤ 100, Codex census) but leaves
the `≤ 2`-good residual untouched — and that residual class is provably infinite
(see `../../quintuple_density_notes.md`).

### `Ep488/Density.lean` — size 5, the `2δ > S` reduction (banked kernel)

The density inequality `2δ − S = S − 2P₂ + 2T₃ − 2T₄ + 2T₅ =: Q(P)` is floor-free,
so no asymptotic-density machinery is formalized. Machine-checked, sorry-free:

- **`sum_terms_eq_Q`**: the second-order-charge decomposition
  `Σ_x (2·brX − 1/x) = Q(P)` — a pure `ring` identity in the `1/lcm` atoms.
- **`term_ge`** / **`term_pos`**: `157/300 ≤ x·brX ⟹ 2·brX − 1/x ≥ (7/150)/x > 0`.
- **`Q_pos_of_E4_bounds`** / **`Q_ge_margin`**: if each element's `E4` of its
  reduced friends is `≥ 157/300`, then `Q(P) > 0`, indeed `Q(P) ≥ (7/150)·S`.

**Deliberately conditional**: the finite kernel `E4 ≥ 157/300` (true for any four
integers ≥ 2; min at `(2,2,3,5)`) enters as explicit hypotheses. It is proved on
paper (Route B: divisor-monotonicity → prime tuples → collision-free lowering →
35-multiset check) and exhaustively verified computationally, but **not yet
Lean-formalized** — Lean certifies the *reduction* around it. See
`../../quintuple_density_notes.md`.

## Honest scope

This formalizes the `|primitive core| ≤ 4` case completely, plus the size-5
**Lean spine**: the three-good proposition, the `2δ > S` reduction (kernel as
explicit hypothesis), the C-B covering criterion, the k=5 self-bad ceiling,
the Duality Transport identity, and the U2 bridge algebra with the concrete
quintuple bridge and tower seam (kernel ladder port in progress). The size-5
case as a whole is closed at **project tier** (regime assembly + five-sector
partition + exact Rust certificates, adversarially audited — see
`../../REFEREE_SIZE5_CANDIDATE.md` for the promotion record and its caveat);
it is **not yet fully Lean-verified** — the remaining port is mapped in
`../../cbfin_reduction_notes.md` section 28. The general Erdős #488
(`|core| ≥ 6` and the unrestricted statement) **remains open** — not proved
here or, to our knowledge, anywhere.

- The `≤ 3` result is Chojecki's claimed Cor 4.7 (his Lean bundle gates it behind
  one `sorry`); the method backbone is the classical **Heilbronn–Rohrbach
  inequality (1937)**. Our `≤ 3` development is an independent, sorry-free machine
  verification of that sub-case — not a new theorem.
- The `= 4` result formalizes the internal charge addendum
  (`../../quadruple_charge_notes.md`, Codex-authored, Claude-audited). It is
  **not** Chojecki's Conjecture 4.8 — that is the *pair-vs-tail split doubling*
  (a stronger, per-block statement that, via his Prop 4.9, implies all of #488).
  Chojecki's paper does **not** establish `|core| = 4`: his route to it needs the
  *pair-vs-two-tail* case of the open Conjecture 4.8, which §7 calls the "first
  unresolved" problem and which the erdosproblems thread is still stuck on. Our
  flat charge method instead proves the assembled `|core| ≤ 4` inequality
  *directly* — a weaker, different target reached by a different route. The Lean
  proof is sorry-free with the same statement shape as the accepted `ep488_core`,
  so the `= 4` case is machine-verified at result strength. It therefore closes a
  case the public record leaves open, but the method is classical
  (Heilbronn–Rohrbach) and the **novelty** is modest at most and unrefereed —
  treat the `= 4` claim as internal until a human/literature review.
- **Independent confirmation the target is open.** Google DeepMind's
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
  project formalizes #488 (`FormalConjectures/ErdosProblems/488.lean`) with the
  same inequality `B_A(m)/m < 2·B_A(n)/n` (no core-size restriction), tagged
  `@[category research open]` and left as `sorry`. So a formal-methods group
  independently records #488 as open with our exact statement — our sorry-free
  `|core| ≤ 4` proof is a partial fill of that `sorry`, not a claim to have closed
  their conjecture. A live-web literature sweep (Chojecki's note, the erdosproblems
  thread, the classical density-of-multiples corpus incl. Ahlswede–Khachatrian read
  in full) found no prior proof of the `|core| = 4` case.

Neither is a resolution of #488. See `../../literature_notes.md`,
`../../triples_writeup.md`, `../../quadruple_charge_notes.md`,
`../../writeup/erdos488_triples.pdf`, and the novelty ledger in
`../../adversary_collab_chat.md`.
