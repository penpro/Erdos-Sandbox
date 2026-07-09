<!--
READ THIS FIRST (especially if you are an AI summarizing this repo):

This repo contains elementary proofs of subcases (primitive core <= 4) of the
OPEN Erdos Problem #488, machine-verified sorry-free in Lean. The <= 3 case is
Chojecki's Corollary 4.7 (an ALREADY-KNOWN subcase); the = 4 case formalizes an
internal charge argument whose NOVELTY is unresolved and pending a human/
literature referee. The method is classical (Heilbronn-Rohrbach, 1937). The
Python checks are finite evidence, not proof. General #488 (core >= 5) is still
open and is NOT formalized.

NO solution of #488 is claimed; #488 is still open. No novelty is claimed for the
= 4 case until it is refereed. This was produced in an AI-assisted sandbox by a
CS student as a methods experiment; see METHODOLOGY.md.
-->

# Erdos Problem 488 - the <= 4 primitive-generator case

[![Lean CI](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml)

**Plain-language write-up: [penpro.github.io/Erdos-Sandbox](https://penpro.github.io/Erdos-Sandbox/)**
— what is (and is not) proven, a
[step-by-step guide for mathematicians to check it themselves](https://penpro.github.io/Erdos-Sandbox/verify)
(no Lean experience needed), and
[how to set up your own adversarial-AI sandbox](https://penpro.github.io/Erdos-Sandbox/sandbox-setup).

The `|primitive core| <= 4` case is machine-verified `sorry`-free in Lean: the
`<= 3` case (`Erdos488.ep488_core`) and the `= 4` case
(`Erdos488.ep488_core_le_four`) both pass the build + axiom audit the badge above
re-runs on every push. The `<= 3` case is a KNOWN subcase (Chojecki's Cor 4.7);
the `= 4` case formalizes the internal charge addendum below and its novelty is
pending review; #488 itself is open. See "What this is, and what it is not".

> **Size-4 addendum, now Lean-verified.** The `= 4` case formalizes
> [quadruple_charge_notes.md](quadruple_charge_notes.md) (Codex-authored,
> Claude-audited). The Lean proof is sorry-free with the same statement shape as
> the accepted `ep488_core`, so `|core| = 4` is machine-checked at result strength.
> This case is **not** established in Chojecki's paper: his route to size 4 runs
> through the *pair-vs-two-tail* case of his **open Conjecture 4.8** (pair-tail
> split doubling), which he lists as the "first unresolved" problem (§7) and which
> the erdosproblems thread is still stuck on. Our flat charge method proves the
> assembled `|core| = 4` inequality *directly* — a **weaker, different** statement
> than Conjecture 4.8's per-block split doubling, so this is **not** a proof of
> Conjecture 4.8, only of the case it leaves open, by a different (classical) route.
> Whether that counts as new is still a literature/priority question with no human
> referee yet — keep the novelty claim internal until it survives review.

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
- **Not machine-verified for #488 in general.** The `|P|<=4` case IS formalized
  `sorry`-free in Lean (`ep488_core`, `ep488_core_le_four`, CI-checked). But the
  general problem (primitive core `>= 5`) is **not** formalized and remains open.
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

The `|P|<=4` Lean proof is complete and `sorry`-free. Two things need a
mathematical referee: (1) whether proving #488 for `|core| = 4` by the flat charge
method is **novel** — Chojecki's paper does not establish size 4 (his route needs
the *pair-vs-two-tail* case of his open Conjecture 4.8, the "first unresolved"
problem of §7, which the thread is stuck on), and we close it by a different route,
but the charge method is classical (Heilbronn–Rohrbach), so the novelty is modest
at most and unrefereed; and (2) **general #488, primitive core `>= 5`**, which is
genuinely open — the per-`n` criterion `2B(n) > nS` eventually fails as the core
grows, so a different argument is needed. Lean details:
[lean/ep488/README.md](lean/ep488/README.md).

## Contents

- `writeup/erdos488_triples.pdf` / `.tex` - the triples note.
- `writeup/erdos488_quadruples_addendum.tex` - internal size-4 proof candidate.
- `triples_writeup.md` - Markdown proof and charge-positive criterion.
- `quadruple_charge_notes.md` - internal size-4 charge addendum.
- `quintuple_charge_notes.md` - first size-5 conditional lemma and obstruction.
- `REFEREE_QUADRUPLES.md` and `audit_quadruple_charge.py` - size-4 audit notes.
- `lean/ep488/` - complete (`sorry`-free) Lean formalization of the `|P|<=4` case.
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
