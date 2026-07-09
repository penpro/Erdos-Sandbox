# Methodology — adversarial AI collaboration ("the frenemy loop")

**What this repository actually is.** A bachelor's CS student's experiment in
AI-assisted mathematical problem-solving. The point of the exercise was to test a
*process*, not to prove a hard theorem. The math output (below, and in the rest of
the repo) is deliberately modest and is stated at exactly its true strength. If
you take one thing from this repo, take the process; the theorems are small
sub-cases used as a test target (the `|core| ≤ 3` part already known; the
`|core| = 4` part a modest, not-yet-refereed extension).

## The process: adversarial collaboration

The setup is what Daniel Kahneman called **adversarial collaboration** — parties
who do *not* trust each other's conclusions work together specifically to try to
break them — applied to two **rival** large language models plus a human referee:

- **Two different vendors' models** (Anthropic's Claude and OpenAI's Codex/GPT)
  take turns proposing arguments and then *attacking* each other's arguments.
  Using rival systems is deliberate: a model is far more likely to rubber-stamp
  its own reasoning than a competitor's.
- **A shared adversarial notebook** ([`adversary_collab_chat.md`](adversary_collab_chat.md))
  records every claim with a status tag (`PROVED`, `COMPUTED`, `PLAUSIBLE`,
  `BROKEN`, `PUBLIC`, `NOVEL?`), every correction, and every failed idea. Nothing
  is deleted; disagreements are replied to underneath.
- **A human (a CS student) is the referee.** The human is not a mathematician and
  cannot check the proofs directly — so the human's job is to force the *process*:
  demand independent re-derivation, demand the literature be checked, demand the
  result be reduced to something machine-checkable, and stop anything that reads
  as hype. (The ground rules are in [`AGENTS.md`](AGENTS.md).)

Because neither the models nor the human can be trusted individually, the design
leans on **redundancy and escalating rigor** rather than on any single verdict.

## Verification, from weakest to strongest

Claims in this repo are labeled by *how* they were checked. In increasing order of
what they actually establish:

1. **Computational evidence** (`attack_triples.py`, etc.): exact-integer checks
   over a large but *finite* range. This is **evidence, not proof** — it rules out
   small counterexamples, nothing more. (Erdős conjectures are designed to survive
   small searches.)
2. **Independent adversarial AI passes:** the central proof was re-derived from
   scratch and/or attacked by **five** independent AI reviewers (a blind
   re-prover, a computational counterexample-hunter, two hostile line-by-line
   referees, a numeric-claims checker); all agreed it is sound. Stronger than a
   single opinion — but still opinions.
3. **Formal proof in Lean 4 / Mathlib** ([`lean/ep488`](lean/ep488)): a
   machine-checked *deductive* proof settles **all** cases at once and is the only
   thing here that is verification in the strict sense. The `|primitive core| ≤ 4`
   case is now **fully** formalized and machine-verified `sorry`-free — both the
   arithmetic core and the classical counting half — and is `#print axioms`-clean
   (only `propext, Classical.choice, Quot.sound`; no `sorryAx`, no `native_decide`;
   CI re-checks this on every push). This does **not** certify the general problem:
   `|core| ≥ 5` is open and is not formalized.

## Why we think the process has some value: it caught its own mistakes

The honest case for adversarial collaboration is not that it is always right — it
is that it catches errors a single confident model would ship. Documented examples
from this very project (all in the honesty ledger of
[`adversary_collab_chat.md`](adversary_collab_chat.md), and in `PROVENANCE.md`):

- **A near-miss "finding" that was already public text.** One model produced an
  "audit" of a *different* Erdős problem (#728) as if it were a discovery; the
  adversarial pass found the identical construction was already printed on that
  problem's page. It was demoted to "not a finding."
- **A wrong attribution, caught by the human.** A summary credited a forum result
  ("the reduction fails for min A ≥ 3") to Terence Tao; when the human pasted the
  actual thread, it was MalekZ's. Corrected everywhere before anything was posted.
- **A false conjecture, drafted then broken.** A tempting generalization
  (`2B(n) > nS` for all primitive sets) was written down, then refuted by an
  explicit counterexample (`A = {2p : p ≤ 100}`) in the next pass.
- **Major novelty corrections.** Several results were initially framed as new,
  then found to be public (Chojecki, MalekZ, Blair) or classical
  (Heilbronn–Rohrbach, 1937). Novelty claims were withdrawn.

These are presented as the method *working*, and as a caution: AI reasoning is
confidently wrong often enough that the redundancy is not optional.

## Honest limitations

- **The math result is modest.** The `|primitive core| ≤ 3` case is a correct,
  elementary re-proof of a result already *claimed* by Chojecki (Corollary 4.7) —
  we cede priority. The `|primitive core| = 4` case is one Chojecki's paper leaves
  open (his route to it needs the still-open pair-vs-two-tail conjecture); it is
  closed here by a *different, classical* method (the two-term Bonferroni /
  Heilbronn–Rohrbach inequality, 1937), and its novelty is modest and **not yet
  human/literature-refereed**. **Nothing here solves #488, which remains open.**
  No new method is claimed.
- **The Lean certifies `|core| ≤ 4`, not the general problem.** The open frontier
  (`|core| ≥ 5`) is not proved here or, to our knowledge, anywhere.
- **AI can be wrong in ways the redundancy misses.** Five agreeing models is not a
  proof; the Lean is the backstop, and it is not finished.
- **The human referee is not a mathematician** and relied on the models and the
  formal check, not on personal verification of the mathematics.

## Bottom line

The interesting artifact is the *process* — an adversarial, redundantly-checked,
formal-verification-anchored pipeline run by a non-expert — and the honest record
of where it succeeded and where it slipped. The theorem is a small, correct,
already-known test case, presented at its true strength and nothing more.
