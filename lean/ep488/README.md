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

This is **not** a complete sorry-free proof of EP488 for `|P| ≤ 3` yet. What
remains is the *counting* half plus the assembly:

- **Bonferroni / Heilbronn–Rohrbach (Lemma 2):** `B(n) ≥ s(n) − P₂(n)`, the
  two-term inclusion–exclusion for the counting function of a set of multiples.
  This is the classical Heilbronn–Rohrbach inequality (1937) in finite-`n` form;
  in Lean it needs `Finset` cardinality of `{k ≤ n : d ∣ k}` (`= n/d`) plus a
  3-set inclusion–exclusion.
- **Assembly (Lemma 5 → Theorem 8 → Theorem 9):** the charge sum
  `s(n) − 2P₂(n) = X_a+X_b+X_c ≥ 3` (each `X ≥ 1` via `floor_bound` +
  `ratio_bounds` + `parity_dichotomy`), then `2·B(n) > n·S`, then EP488 with the
  primitive-core reduction and the covered zone.

The remaining work is *classical + mechanical* (no new mathematics); the novel
content is the arithmetic core above, which is done. Estimated ~300–500 more Lean
lines — the natural next chunk, or a candidate to hand to an automated prover.

## Provenance

Paper proof and priority discussion: `../../writeup/erdos488_triples.pdf`,
`../../triples_writeup.md`. The result is Chojecki's claimed Cor 4.7; the method
backbone is the classical Heilbronn–Rohrbach inequality; see
`../../literature_notes.md` and `../../adversary_collab_chat.md`.
