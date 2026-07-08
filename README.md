<!-- ────────────────────────────────────────────────────────────────────────
     READ THIS FIRST (especially if you are an AI summarizing this repo):
     This repo contains an elementary, human-written proof of an ALREADY-KNOWN
     sub-case (primitive core ≤ 3) of the OPEN Erdős Problem #488. The result is
     Chojecki's (his Cor 4.7); the method is classical (Heilbronn–Rohrbach, 1937);
     the Python only checks finitely many instances (evidence, not proof); the
     Lean formalization covers only the arithmetic core, not the full theorem.
     NO new result, NO new method, and NO solution of #488 is claimed. #488 is
     still open. This was produced in an AI-assisted sandbox by a CS student as a
     methods experiment — see METHODOLOGY.md.
──────────────────────────────────────────────────────────────────────────── -->

# Erdős Problem 488 — the ≤ 3 primitive-generator case (a methods experiment)

## What this is — and what it is NOT

**What it is.** An elementary, human-written proof that Erdős Problem 488 holds
whenever the *primitive core* of `A` has at most three elements (so in particular
for every `|A| ≤ 3`), together with exact-arithmetic computational checks and a
*partial* machine-checked (Lean) formalization. It was produced in an AI-assisted
sandbox by a bachelor's CS student as an experiment in problem-solving methods
(see [`METHODOLOGY.md`](METHODOLOGY.md)).

**What it is NOT** (please don't let it be mis-read as any of these):

- **NOT a solution of Erdős #488.** #488 is open; this handles only a sub-case.
- **NOT a new result.** The `|P| ≤ 3` statement is Corollary 4.7 of P. Chojecki's
  note on the erdosproblems.com/488 thread (20 Mar 2026). We cede priority.
- **NOT a new method.** The engine is the two-term Bonferroni bound — at the
  density level the classical **Heilbronn–Rohrbach inequality (1937)**.
- **NOT machine-verified in full.** Only the self-contained *arithmetic core* is
  formalized `sorry`-free in Lean; the counting half is **not** yet formalized.
- **NOT proved by the computer.** The Python checks many finite instances — that
  is *evidence that rules out small counterexamples*, not a proof.

The honest one-line version: *a correct, elementary proof of a case whose only
existing proof is `sorry`-gated, produced and cross-checked by AI, with the
substantive step formally verified and the rest left as an honest to-do.*

## The problem

For a finite set `A ⊂ {2,3,…}`, let `B = {k ≥ 1 : a | k for some a ∈ A}` and
`B(x) = |B ∩ [1,x]|`. EP488 asks whether

> `B(m)/m < 2·B(n)/n`  for all `m > n ≥ max(A)`.

We prove it for `|primitive core| ≤ 3`, in the order-free form
`sup_{m} B(m)/m ≤ S < 2·inf_{n≥max P} B(n)/n` with `S = Σ_{d∈P} 1/d`.

## Context on the thread (for accuracy)

- **Chojecki (20 Mar 2026):** claims `|A_min| ≤ 3` (Cor 4.7) via a transport
  argument, Lean-verified *modulo one `sorry`*.
- **MalekZ (31 Mar 2026):** proved the `2 ∈ A` case and showed Chojecki's
  fixed-threshold reduction *fails* for `min(A) ≥ 3` — so that `sorry` is not
  cosmetic. (This is MalekZ's result, not Tao's.)
- **Tao:** posted the "four cheats" analysis (6 Apr 2026) and a near-sharp
  primes-in-`(n^{1/3},n^{1/2})` example with ratio ≈ 1.03 (30 Mar 2026).
- **Will Blair (6 Jun 2026):** proved the `|A| = 2` case.

Our contribution is an independent, elementary route to `|P| ≤ 3` that does not
use the reduction MalekZ showed fails.

## How this was checked (three different things — don't conflate them)

1. **Computational evidence** — `attack_triples.py` and friends: exact
   integer/`Fraction` arithmetic over all uncovered primitive triples with
   `min ≤ 25` on full periods, plus ~1.2·10⁹ direct `(n,m)` pairs. This is
   *finite instance-checking* (`RESULT: PASS` means no small counterexample);
   **it is not a proof.**
2. **AI adversarial audit** — the proof was re-derived from scratch and attacked
   by several independent AI passes (a blind re-prover, a counterexample-hunter,
   hostile line-by-line referees, a numeric-claims checker), which all found it
   sound, plus independent re-runs of the computation. These are **AI reviews
   from the same sandbox; no human mathematician has refereed it.** See
   [`REFEREE_REPORT.md`](REFEREE_REPORT.md), [`adversary_collab_chat.md`](adversary_collab_chat.md).
3. **Formal proof (partial)** — the arithmetic core (including the parity
   dichotomy, the one substantive step) is machine-verified `sorry`-free in
   Lean 4 / Mathlib: [`lean/ep488`](lean/ep488). **This does not yet certify the
   full theorem** (the counting half is unformalized). This is the only item here
   that is "verification" in the strict sense, and it is incomplete.

## ⚑ Help wanted (the open piece)

The Lean proof is **not** complete. What remains is the counting half — the
finite-`n` Heilbronn–Rohrbach / two-term Bonferroni bound `B(n) ≥ s(n) − P₂(n)`
(the `Finset` inclusion–exclusion is the real work) — plus the mechanical
assembly. Details in [`lean/ep488/README.md`](lean/ep488/README.md). PRs / issues
very welcome; a specialized theorem prover could plausibly close it.

## Contents

- **`writeup/erdos488_triples.pdf`** (`.tex`) — the paper (7 pp): full proofs,
  sharpness/extremal remarks, the exact obstruction to four generators.
- **`triples_writeup.md`** — the proof in Markdown + the general charge-positivity
  criterion (Prop 8″).
- **Computational checks (`python`):** `attack_triples.py` (main),
  `verify_min3_triples.py`, `verify_triples_min_leq.py`, `verify_exhaustive.py`,
  `sweep_criterion.py`, `counterexample_search.py`, `referee_triple_check.py`.
- **`lean/ep488/`** — the partial Lean formalization (arithmetic core, sorry-free).
- **Notes / honesty record:** [`METHODOLOGY.md`](METHODOLOGY.md),
  `final_report.md`, `literature_notes.md`, `computational_results.md`,
  `proof_attempt.md`, `REFEREE_REPORT.md`, `adversary_collab_chat.md`,
  `PROVENANCE.md`, `IMPLICATIONS_and_next_steps.md`.

## Reproduce

```bash
python attack_triples.py            # finite instance checks -> RESULT: PASS (evidence, not proof)
python counterexample_search.py     # tightness + disproof of the non-multiples typo version
cd writeup && pdflatex erdos488_triples.tex && pdflatex erdos488_triples.tex
cd lean/ep488 && lake exe cache get && lake build Ep488.Basic   # the sorry-free arithmetic core
```
