# Erdős Problem 488 — the ≤ 3 primitive-generator case

An elementary, self-contained, exact-arithmetic-verified proof that **Erdős
Problem 488** holds whenever the *primitive core* of `A` has at most three
elements (in particular for every `|A| ≤ 3`).

> **If you came from the erdosproblems.com/488 thread — start here.**
> - **Paper (7 pp):** [`writeup/erdos488_triples.pdf`](writeup/erdos488_triples.pdf).
> - **Verify the math in ~2 min:** `python attack_triples.py` → `RESULT: PASS`
>   (exact integer arithmetic; all uncovered primitive triples `a ≤ 25` over full
>   periods + ~1.2·10⁹ direct `(n,m)` pairs).
> - **Lean:** the arithmetic core — including the parity dichotomy that is the
>   single substantive step — is formalized **sorry-free** against Mathlib
>   v4.31.0: [`lean/ep488`](lean/ep488). See its README for the `#print axioms`
>   check.
> - **⚑ Help wanted (open):** the Lean proof is *not* complete. The remaining
>   piece is the counting half — the finite-`n` Heilbronn–Rohrbach / two-term
>   Bonferroni bound `B(n) ≥ s(n) − P₂(n)` — plus mechanical assembly (~300–500
>   Lean lines, no new mathematics). Details in
>   [`lean/ep488/README.md`](lean/ep488/README.md). PRs / issues very welcome.
> - **Honesty:** the *result* is Chojecki's claimed Cor 4.7 (still `sorry`-gated
>   on the thread); the *method* backbone is the classical Heilbronn–Rohrbach
>   inequality (1937). We claim neither a new result nor a new method — only a
>   correct, elementary, formally-clean proof of the case the frontier is stuck on.
>   Produced in an AI-assisted sandbox (see `PROVENANCE.md`).

For a finite set `A ⊂ {2,3,…}`, let `B = {k ≥ 1 : a | k for some a ∈ A}` and
`B(x) = |B ∩ [1,x]|`. EP488 asks whether

> `B(m)/m < 2·B(n)/n`  for all `m > n ≥ max(A)`.

We prove it for `|primitive core| ≤ 3`, in the order-free form
`sup_{m} B(m)/m ≤ S < 2·inf_{n≥max P} B(n)/n` with `S = Σ_{d∈P} 1/d`.

## Honest status (please read)

- **The result is not new.** It is Corollary 4.7 of P. Chojecki's note (linked
  from [erdosproblems.com/488](https://www.erdosproblems.com/488), 20 Mar 2026),
  there proved by other means but Lean-verified only *modulo one `sorry`*; Tao
  (Apr 2026) showed the reduction underlying that step fails for `min(A) ≥ 3`, so
  the case is effectively still open in practice. EP488 itself is Erdős's, and
  the site still lists it as open.
- **The method is not new either.** The two-term Bonferroni backbone is the
  finite-`n` form of the classical **Heilbronn–Rohrbach inequality (1937)**
  (Halberstam–Roth, *Sequences*, Ch. V; Hall, *Sets of Multiples*).
- **What this repo offers:** a *correct, elementary, self-contained* proof of the
  stuck `|P| = 3` case — no restricted counting function, no split on `n`, no
  transport machinery; its one substantive step is a two-line `gcd`/parity
  dichotomy — plus exact-arithmetic verification at scale, and (planned) a
  `sorry`-free Lean formalization.

This work was produced in an AI-assisted sandbox (Claude + Codex); see
`PROVENANCE.md` for who/what did which part.

## Contents

- **`writeup/erdos488_triples.pdf`** (`.tex`) — the paper (7 pp), with full
  proofs, the sharpness/extremal remarks, and the exact obstruction to four
  generators.
- **`triples_writeup.md`** — the same proof in Markdown, plus the general
  charge-positivity criterion (Prop 8″).
- **Verification (exact integer/`Fraction` arithmetic; run with `python`):**
  - `attack_triples.py` — the main proof, checked over all uncovered primitive
    triples with `min ≤ 25` on full periods and ~1.2·10⁹ direct `(n,m)` pairs.
  - `verify_min3_triples.py`, `verify_triples_min_leq.py` — exact periodicity
    certificates (superseded by `attack_triples.py`, kept for cross-checks).
  - `verify_exhaustive.py`, `sweep_criterion.py`, `counterexample_search.py`,
    `referee_triple_check.py` — exhaustive small-domain checks, criterion sweeps,
    the alternate-version disproof, and an independent referee re-run.
- **Notes:** `final_report.md`, `literature_notes.md`, `computational_results.md`,
  `proof_attempt.md`, `REFEREE_REPORT.md`, `adversary_collab_chat.md`,
  `IMPLICATIONS_and_next_steps.md`.

## Reproduce

```bash
python attack_triples.py            # main proof verification -> RESULT: PASS
python counterexample_search.py     # tightness + disproof of the non-multiples typo version
cd writeup && pdflatex erdos488_triples.tex && pdflatex erdos488_triples.tex
```

Correctness has been checked by five independent adversarial passes (see
`adversary_collab_chat.md` / `REFEREE_REPORT.md`).
