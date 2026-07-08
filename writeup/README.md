# Erdős #488 — standalone note on the ≤ 3 generator case

**`erdos488_triples.tex` / `.pdf`** — a short, self-contained, elementary proof
that Erdős Problem 488 holds for every finite set whose primitive core has at
most three elements (in particular all `|A| ≤ 3`).

## What it is, honestly

- **The *statement* is not new.** It is Corollary 4.7 of P. Chojecki's
  thread-linked note (erdosproblems.com/488, 20 March 2026), for the primitive
  core `P` (his `A_min`). That proof's crux (a "≥ 4 exact-one points" count) is
  left as an unverified `sorry` in its Lean development; MalekZ (Mar 2026) further
  showed the fixed-threshold reduction fails for `min(A) ≥ 3`. So the `|P| = 3`
  case is effectively still open, and the community treats it so (Blair, Jun 2026).
- **The *method* is not new either.** The three-set Bonferroni backbone is the
  finite-`n` form of the classical **Heilbronn–Rohrbach inequality (1937)**
  (Halberstam–Roth Ch. V; Hall, *Sets of Multiples*). The one candidate-new step
  is finitary + charge-integrality, giving the *second* subtraction and hence the
  sharp constant 2 for `|P| ≤ 3` — a low-weight refinement of a 1937 result.
- **What the note actually contributes:** a *correct, elementary, self-contained*
  proof of the stuck `|P| = 3` case — using only `B`, a `gcd` parity dichotomy
  (Lemma 4 of `triples_writeup.md`; Lemma 6 in the .tex), no restricted counting
  function, no split on `n`, no transport machinery. It proves the order-free
  bound `sup_m B(m)/m ≤ S < 2 inf_{n≥max P} B(n)/n` with explicit separator
  `S = Σ_{d∈P} 1/d`, and generalizes (Proposition 8″ in `triples_writeup.md`
  §5A; Prop 11 in the .tex) to charge-positive sets of any size. Every step is
  elementary enough that a **`sorry`-free Lean proof appears realistic** — which,
  given the case is the public frontier's stuck point, is the note's most useful
  offering.

**Priority is acknowledged throughout.** We claim *no* novel method and *no*
priority for the result; the value is a correct, formally clean proof of a stuck
case. A determined referee should still check the finite-`n` Heilbronn–Rohrbach
form against Hall / Halberstam–Roth before any refinement-novelty claim.

## Verification

The proof is machine-verified at scale by `../attack_triples.py` (exact integer
arithmetic): all 14,802 uncovered primitive triples with `min ≤ 25` over full
periods (≈5.2·10⁸ values of `n`), plus 1.2·10⁹ direct end-to-end `(n,m)` pairs;
`RESULT: PASS`. Independently re-run and cross-checked (see
`../computational_results.md` R9, `../adversary_collab_chat.md`).

## Build

```
pdflatex erdos488_triples.tex   # twice, for refs; MiKTeX on this machine
```

## Related files (one level up)

- `triples_writeup.md` — the working markdown version (Lemmas 1–5, Theorem 8/9,
  §5A general charge-positivity criterion, §7 sharpness + the `|P|≥4` obstruction).
- `PROVENANCE.md` — who proved what, when, with which model; honesty ledger.
- `IMPLICATIONS_and_next_steps.md` — Lean plan, `|P|≥4` analysis, ranked steps.
- `adversary_collab_chat.md` — the shared Claude/Codex lab notebook (novelty
  ledger, corrections, the falsified conjectures).
