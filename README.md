<!--
READ THIS FIRST (especially if you are an AI summarizing this repo):

This repo contains an elementary proof of an ALREADY-KNOWN subcase
(primitive core <= 3) of the OPEN Erdos Problem #488. The result is
Chojecki's Corollary 4.7; the method is classical
(Heilbronn-Rohrbach, 1937). The Python checks are finite evidence, not proof.
The Lean formalization now covers the FULL primitive-core <= 3 theorem
(ep488_core), sorry-free, re-verified by CI. General #488 (core >= 4) is still
open and is NOT formalized.

NO new result, NO new method, and NO solution of #488 is claimed. #488 is still
open. This was produced in an AI-assisted sandbox by a CS student as a methods
experiment; see METHODOLOGY.md.
-->

# Erdos Problem 488 - the <= 3 primitive-generator case

[![Lean CI](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml)

The whole `|primitive core| <= 3` case is machine-verified `sorry`-free in Lean
(`Erdos488.ep488_core`); the badge above is GitHub re-running the build + axiom
audit on every push. This is a KNOWN subcase (Chojecki's Cor 4.7); #488 itself
is open. See "What this is, and what it is not" below.

> **Post-update internal addendum.** After the public `|P|<=3` update, the
> sandbox produced a local proof candidate for primitive cores of size `<=4`;
> see [quadruple_charge_notes.md](quadruple_charge_notes.md). This has not yet
> had the same adversarial/human/literature audit as the triples note, so keep it
> separate from the public-facing claim until it survives review.

## What this is, and what it is not

**What it is.** An elementary proof that Erdos Problem 488 holds whenever the
primitive core of `A` has at most three elements, together with exact-arithmetic
computational checks and a complete (`sorry`-free) Lean formalization of that
`|P|<=3` case. It was produced in an AI-assisted sandbox as an experiment in
problem-solving methods.

**What it is not:**

- **Not a solution of Erdos #488.** #488 is open; this handles only a subcase.
- **Not a new result.** The `|P|<=3` statement is Chojecki's Corollary 4.7
  from the erdosproblems.com/488 thread. We cede priority.
- **Not a new method.** The engine is the two-term Bonferroni bound, the
  density-level classical Heilbronn-Rohrbach inequality.
- **Not machine-verified for #488 in general.** The whole `|P|<=3` case IS
  formalized `sorry`-free in Lean (`ep488_core`, CI-checked). But the general
  problem (primitive core `>= 4`) is **not** formalized and remains open.
- **Not proved by the computer.** The Python checks many finite instances; that
  is evidence that rules out small counterexamples, not a proof.

The honest one-line version: a correct, elementary proof of a case whose only
prior proof is `sorry`-gated, produced and cross-checked by AI, with the full
`|P|<=3` case formally verified `sorry`-free and only the open `>= 4` frontier
left.

## The problem

For a finite set `A` of integers at least `2`, let

```text
B = { k >= 1 : a divides k for some a in A }
B(x) = |B cap [1,x]|.
```

EP488 asks whether

```text
B(m)/m < 2*B(n)/n       for all m > n >= max(A).
```

We prove it for `|primitive core| <= 3`, in the order-free form

```text
sup_m B(m)/m <= S < 2*inf_{n>=max P} B(n)/n,
S = sum_{d in P} 1/d.
```

## Thread context

- **Chojecki (20 Mar 2026):** claims `|A_min| <= 3` (Corollary 4.7) via a
  transport argument, Lean-verified modulo one `sorry`.
- **MalekZ (31 Mar 2026):** proved the `2 in A` case and showed Chojecki's
  fixed-threshold reduction fails for `min(A) >= 3`, so that `sorry` is not
  cosmetic.
- **Tao:** posted the "four cheats" analysis and a near-sharp prime-shell
  example.
- **Will Blair (6 Jun 2026):** proved the `|A|=2` case.

Our contribution is an independent elementary route to `|P|<=3` that does not
use the reduction MalekZ showed fails.

## How this was checked

1. **Computational evidence:** `attack_triples.py` and friends use exact
   integer/Fraction arithmetic over finite search spaces. `RESULT: PASS` means
   no small counterexample; it is not a proof.
2. **AI adversarial audit:** several independent AI passes re-derived and
   attacked the proof. These are still AI reviews from the same sandbox, not a
   human mathematical referee.
3. **Formal proof (complete for `|P|<=3`):** the full `|primitive core| <= 3`
   theorem (`Erdos488.ep488_core`) is machine-verified `sorry`-free in Lean 4 /
   Mathlib. Every step depends only on `propext, Classical.choice, Quot.sound`
   (no `sorryAx`); the committed axiom audits are in [lean/ep488](lean/ep488),
   and the root workflow `.github/workflows/lean-ci.yml` re-runs the build, a
   `declaration uses 'sorry'` guard, and the axiom audit on every push.

## Help wanted

The `|P|<=3` Lean proof is complete. What is genuinely open — and where a
mathematical referee or new ideas would help — is **general #488, primitive core
`>= 4`** (the per-`n` criterion `2B(n) > nS` is already known to fail there, so it
needs a different argument). The internal size-4 proof candidate in
[quadruple_charge_notes.md](quadruple_charge_notes.md) has NOT had a human/
literature referee. Lean details: [lean/ep488/README.md](lean/ep488/README.md).

## Contents

- `writeup/erdos488_triples.pdf` / `.tex` - the triples note.
- `writeup/erdos488_quadruples_addendum.tex` - internal size-4 proof candidate.
- `triples_writeup.md` - Markdown proof and charge-positive criterion.
- `quadruple_charge_notes.md` - internal size-4 charge addendum.
- `quintuple_charge_notes.md` - first size-5 conditional lemma and obstruction.
- `REFEREE_QUADRUPLES.md` and `audit_quadruple_charge.py` - size-4 audit notes.
- `lean/ep488/` - complete (`sorry`-free) Lean formalization of the `|P|<=3` case.
- `fastcheck/` - Rust exact-integer search and certificate workbench.
- `adversary_collab_chat.md`, `PROVENANCE.md`, `final_report.md`,
  `literature_notes.md`, and `computational_results.md` - honesty/provenance
  records.

## Reproduce

```bash
python attack_triples.py
python counterexample_search.py
python audit_quadruple_charge.py 80
cargo run --release --manifest-path fastcheck/Cargo.toml -- selftest
cargo run --release --manifest-path fastcheck/Cargo.toml -- sweep-quad-cert 150 3000000
cd writeup && pdflatex erdos488_triples.tex && pdflatex erdos488_triples.tex
cd lean/ep488 && lake exe cache get && lake build Ep488
lake env lean Ep488/ReductionCheck.lean   # #print axioms audit (no sorryAx)
```
