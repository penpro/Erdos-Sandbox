# Project Rules For Agents

This workspace is a shared Erdos-problem research sandbox for Codex, Claude Code,
and the human user.

## Required Checks

Before making or upgrading any mathematical claim, read:

1. `adversary_collab_chat.md`
2. `literature_notes.md`
3. `proof_attempt.md`
4. `final_report.md`

Before upgrading any size-5 claim, also read and attack
`REFEREE_SIZE5_CANDIDATE.md`.

Before selecting a new problem, switching the active target, or calling a result
"new", "solved", "publishable", or "worth publishing", add or review an entry in
`adversary_collab_chat.md`.

## Collaboration Style

- Be adversarial about proofs and generous about leads.
- Distinguish `PROVED`, `COMPUTED`, `PLAUSIBLE`, `BROKEN`, `PUBLIC`, and `NOVEL?`.
- Do not hide failed approaches. Put them in `adversary_collab_chat.md` or the
  relevant proof note.
- If another agent left a claim, try to break it before building on it.
- If a correction affects a file, update that file, not only the chat.
- Do not claim novelty from an elementary lemma until the problem thread,
  linked notes, and likely literature have been checked.

## Computation Tooling — which tool for which job (added 2026-07-10)

Lesson from the G3 overclaim: a "min ≤ 54, zero counterexamples in 12.5M sets"
claim came from *Python* enumeration capped at small entries — the counterexamples
lived at entries in the hundreds/thousands, out of Python's reach, so a small-range
search got reported as comprehensive. Rule:

- **Rust for iteration / exhaustive sweeps / negative-existence.** Any claim of the
  form "no counterexample exists in range X", "every set with property P satisfies
  Q", "the class is finite/bounded" — run it in Rust. It is ~50–200× faster than
  Python and reaches the ranges where surprises hide. Use hand-rolled exact `i128`
  common-denominator arithmetic (no external crates, matching `fastcheck`), or
  `i128`/`u128` integer counting; escalate to bignum only if `i128` can overflow
  (lcm of the set exceeds ~1.7e38). Parallelize with `std::thread` if needed.
  - Claude's census crate: `census/` (separate from Codex's `fastcheck/` — do not
    edit his). Build/run with the GNU toolchain: the machine default is MSVC, so
    always `cargo +stable-x86_64-pc-windows-gnu ...`. Keep build artifacts out of
    git (`CARGO_TARGET_DIR` under a temp/ignored path).
  - Codex owns `fastcheck/` (window/separator certificates). Prefer coordinating a
    query to him for those; do not modify his crate.
- **Python (exact `fractions.Fraction`) for**: exact arithmetic on *specific* sets,
  quick spot-checks, prototyping a formula before porting to Rust, and any one-off
  where the set count is small (< ~1e6). Never use it for a comprehensive/"searched
  everything" claim.
- **LLM agents for**: structural reasoning, deriving proofs, *constructing* witnesses
  / counterexamples, classification. NOT for "I searched N and found nothing" — that
  is a negative-existence claim and belongs in Rust. (The G3 counterexamples were
  found by an agent reasoning about the dual structure, not by brute force — that is
  the right use of an agent; the mistake was trusting an agent/Python *negative*.)

Bottom line: if the answer depends on how much you searched, use Rust. If it depends
on a construction or an argument, an agent/Python is fine — but then verify the
resulting claim's *range* in Rust before banking it.

## Active Target

The current publishable-track target is Erdos Problems #488, not #728.

The #728 work is archived as a non-novel formulation audit in
`problem_728_formulation_audit/`.

