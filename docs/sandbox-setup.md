---
title: "Set up your own adversarial-AI math sandbox"
description: "How to reproduce this repository's setup — two rival AI coding agents that check each other, a shared adversarial notebook, and formal verification as the backstop — so you can attack problems independently."
---

# Set up your own adversarial-AI math sandbox

*This repository is a working template for what it calls the "frenemy loop":
**two rival AI models take turns proposing arguments and attacking each other's,
with a human referee, and every claim is escalated toward a machine-checkable
proof.** This page shows how to stand up the same setup yourself. You do not need
to be a programmer, but you do need patience and a healthy distrust of confident
answers — including the AIs'.*

The idea in one paragraph is in [`METHODOLOGY.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/METHODOLOGY.md);
the ground rules the agents follow are in
[`AGENTS.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/AGENTS.md) and
[`CLAUDE.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/CLAUDE.md).

[← back to the main write-up](https://penpro.github.io/Erdos-Sandbox/)

---

## Why two *rival* models

A single model rubber-stamps its own reasoning. Two models from **different
vendors** are much more willing to tear each other's arguments apart — which is the
whole point. This project used **Anthropic's Claude** and **OpenAI's Codex/GPT**.
Any two capable, *different* coding agents work; the rivalry matters more than the
brand.

**Honest note:** both agents are commercial products and need paid accounts. This
is not a free setup. The *method* (adversarial checking + formal verification) is
what transfers; the specific tools are replaceable.

---

## What you will assemble

| Piece | Purpose | This repo uses |
|---|---|---|
| Two rival AI coding agents | propose & attack arguments | Claude Code + OpenAI Codex |
| A git repository (a shared folder) | the agents share files here | a normal GitHub repo |
| A shared adversarial notebook | agents leave tagged messages for each other | [`adversary_collab_chat.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/adversary_collab_chat.md) |
| Ground-rule files | tell each agent how to behave | `AGENTS.md`, `CLAUDE.md` |
| A proof assistant | the *backstop* — turns arguments into checked proofs | Lean 4 / Mathlib |
| A fast exact-arithmetic tool | cheap evidence / counterexample hunting | Rust (`fastcheck/`) + Python |
| **You** | the referee who forces the process | — |

---

## Step 1 — Install the two agents

Both are command-line tools that operate on a folder on your computer.

- **Claude Code** (Anthropic): install and sign in per
  [Anthropic's instructions](https://docs.anthropic.com/en/docs/claude-code). It
  runs in a terminal inside your project folder and automatically reads a
  `CLAUDE.md` file there for instructions.
- **OpenAI Codex** (the Codex CLI/agent): install and sign in per
  [OpenAI's instructions](https://developers.openai.com/codex/). It likewise runs
  in your project folder and reads an `AGENTS.md` file for instructions.

They "collaborate" because they operate on the **same folder** and read/write the
**same shared notebook file** — not because they talk to each other directly. You
run each one (in its own terminal), and they leave each other messages in the repo.

## Step 2 — Create the repository scaffold

Make a new git repository (a folder tracked by [git](https://git-scm.com/)) and add
these files. The simplest way to get correct, battle-tested versions is to copy
them from this repo:

1. **`AGENTS.md`** — the rules Codex reads. **`CLAUDE.md`** — the rules Claude
   reads. Keep them short and identical in spirit. The load-bearing rules here are:
   - *Be adversarial about proofs, generous about leads.* Try to **break** the
     other agent's claim before building on it.
   - *Tag every claim* with its strength: `PROVED`, `COMPUTED` (finite evidence),
     `PLAUSIBLE`, `BROKEN`, `PUBLIC` (already known), `NOVEL?` (needs a literature
     check).
   - *Never hide a failed idea* — record it.
   - *Do not claim novelty* until the problem thread, notes, and likely literature
     have been checked.
   - *Commit / post nothing without the human saying so.*

2. **`adversary_collab_chat.md`** — the shared notebook. Every entry is dated and
   tagged; **nothing is deleted**; you reply *underneath* a claim to dispute it.
   This file *is* the collaboration. (See this repo's copy for the format.)

3. **`METHODOLOGY.md`** and a `README.md` stating, up front and honestly, what the
   project is and is not — so neither the AIs nor a future reader drift into hype.

## Step 3 — Add the verification toolchains

Arguments are cheap; *checks* are the point. Two tiers:

- **Formal proof (the backstop): Lean 4 + Mathlib.** This is the only thing that
  *verifies* rather than *suggests*. Install `elan` (see the
  [check-it-yourself guide](https://penpro.github.io/Erdos-Sandbox/verify)); scaffold a project with `lake new`. The
  discipline: whenever an argument stabilizes, push the agents to formalize it in
  Lean until it compiles `sorry`-free. A machine-checked proof settles all cases at
  once and cannot be talked out of.
- **Cheap evidence: exact-integer computation.** Python is easiest to start
  (`Fraction` for exact rationals); a compiled language (this repo uses **Rust**,
  via [rustup.rs](https://rustup.rs)) lets you search far larger ranges. Evidence
  **rules out small counterexamples — it never proves anything.** Label it
  `COMPUTED`, never `PROVED`.

## Step 4 — Run the loop

A typical cycle:

1. **Pick a target** and have one agent write the precise statement + a first
   attack into the notebook, tagged.
2. **Hand it to the rival agent** to *break* — find a gap, a counterexample, a
   missing case, or prior art. Corrections go into the notebook and into the
   affected file, not just the chat.
3. **Escalate rigor.** Weak evidence → stronger evidence → independent
   re-derivation → **Lean proof**. Do not upgrade a claim's tag until it survives
   the next tier.
4. **You referee.** Even if you cannot check the mathematics yourself, you *can*
   force the process: demand independent re-derivation, demand the literature be
   checked, demand a machine-checkable reduction, and **stop anything that reads as
   hype**. That is the human's entire, essential job.

---

## The honest caveats (please internalize these)

- **AI is confidently wrong often enough that the redundancy is not optional.**
  This project's own notebook records a near-miss "discovery" that was already
  public text, a wrong attribution the human caught, and a tempting conjecture that
  was drafted then refuted. The method's value is that it *caught its own
  mistakes* — but only because the checks were actually run.
- **Agreeing models are not a proof.** Five AIs nodding is still opinion. The Lean
  proof is the backstop; until something compiles `sorry`-free, treat it as
  unproven.
- **A non-mathematician can referee the process but not the mathematics.** Be
  explicit about that limit in your write-ups, and lean on the formal check.
- **State results at exactly their true strength.** "Machine-verified a known
  sub-case" is a real, honest outcome. "Solved an Erdős problem" almost certainly
  is not.

---

## Use this repo as your template

Everything above is live in this repository — copy and adapt:
[`AGENTS.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/AGENTS.md),
[`CLAUDE.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/CLAUDE.md),
[`METHODOLOGY.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/METHODOLOGY.md),
[`adversary_collab_chat.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/adversary_collab_chat.md),
the Lean project in [`lean/ep488`](https://github.com/penpro/Erdos-Sandbox/tree/main/lean/ep488),
and the Rust workbench in [`fastcheck/`](https://github.com/penpro/Erdos-Sandbox/tree/main/fastcheck).

---

[← back to the main write-up](https://penpro.github.io/Erdos-Sandbox/) &nbsp;·&nbsp;
[check the proof yourself →](https://penpro.github.io/Erdos-Sandbox/verify)
