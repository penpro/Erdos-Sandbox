# Lean formalization of Erdős #488 (|primitive core| ≤ 3) — status

Lean 4 + Mathlib project. Toolchain: `leanprover/lean4:v4.31.0`, Mathlib
`v4.31.0` (see `lean-toolchain`, `lakefile.toml`).

## What is machine-verified (sorry-free)

`Ep488/Basic.lean` — the **self-contained arithmetic core** of the proof, checked
sorry-free (each lemma is `#print axioms`-clean: depends only on
`propext, Classical.choice, Quot.sound`, no `sorryAx`, no literal `sorry`):

- **`floor_bound`** (Lemma 1(ii)): for `t ≥ 1`, `q ≥ 2`, `q' ≥ 3`,
  `1 ≤ t − t/q − t/q'`. The one input to each per-generator charge.
- **`ratio_bounds`** (Lemma 3): for primitive `x < y`,
  `y/gcd(x,y) ≥ 3` and `x/gcd(x,y) ≥ 2`.
- **`parity_dichotomy`** (Lemma 4): in the uncovered zone `b·c < a·(b+c)`,
  `lcm(a,c)` and `lcm(b,c)` cannot both equal `2c`. **This is the single
  substantive step of the whole proof** — the thing that forces every charge
  positive, and (in the transport route) exactly the case that carries Chojecki's
  Lean `sorry`. Here it is a ~40-line elementary `gcd`/parity argument, fully
  verified.

The `#print axioms` audit (each lemma depends only on
`propext, Classical.choice, Quot.sound` — no `sorryAx`) is committed as
[`axioms-check.txt`](axioms-check.txt); regenerate it with
`lake build Ep488.Check`.

Build & check:
```
lake exe cache get      # once: downloads prebuilt Mathlib oleans
lake build Ep488.Basic  # compiles clean
```

## What is NOT yet formalized (honest)

### The counting half is now formalized too (`Ep488/Counting.lean`, sorry-free)

The hard case — **EP488 for an uncovered primitive triple** — is now fully
machine-verified (axiom audit in `counting-axioms.txt`: only
`propext, Classical.choice, Quot.sound`):

- **`bonferroni`** (Lemma 2): `s(n) ≤ B(n) + P₂(n)` — the finite-`n` two-term
  inclusion–exclusion (density-level = classical Heilbronn–Rohrbach 1937), via
  `Nat.Ioc_filter_dvd_card_eq_div` (count of multiples `= n/d`) and the 3-set
  `Finset.card_union_add_card_inter` chain.
- **`charge`** (Lemma 5): `2·P₂(n) + 3 ≤ s(n)` for `n ≥ c` — the charge
  decomposition, using `floor_bound`, `ratio_bounds`, and `parity_dichotomy`.
- **`two_B_gt_nS`** (Theorem 8): `n·(bc+ac+ab) < 2·B(n)·abc`, i.e. `2B(n)/n > S`.
- **`ep488_uncovered_triple`**: `n·B(m) < 2·m·B(n)` for all `m > n ≥ c`.

### What still remains (all elementary)

Only the *easy* cases are left before the full `|P| ≤ 3` theorem: the covered
zone `1/b+1/c ≤ 1/a` (union bound `B(n) ≥ ⌊n/a⌋+1 > n/a`, `B(m) ≤ 2m/a`), the
singleton and pair cases, and the primitive-core reduction to a general finite
set `A`. These need no charge/parity machinery — just the union bound already in
`B_le_s`. The mathematically substantive content (the parity dichotomy + charge +
Bonferroni) is done.

## Provenance

Paper proof and priority discussion: `../../writeup/erdos488_triples.pdf`,
`../../triples_writeup.md`. The result is Chojecki's claimed Cor 4.7; the method
backbone is the classical Heilbronn–Rohrbach inequality; see
`../../literature_notes.md` and `../../adversary_collab_chat.md`.
