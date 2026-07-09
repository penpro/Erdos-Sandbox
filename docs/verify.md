---
title: "Check the proof yourself — a step-by-step guide (no Lean experience needed)"
description: "How a mathematician with no programming background can install the tools and watch a computer confirm the |core|≤4 proof of Erdős #488, with zero trusted gaps."
---

# Check the proof yourself

*A guide for mathematicians who have never used Lean, a terminal, or GitHub. You
do **not** need to read or understand any code. You will install a toolchain, run
three commands, and watch the computer confirm the theorem — with no gaps it takes
on trust.*

Total time: about **15–30 minutes**, most of it waiting for downloads.

[← back to the main write-up](./)

---

## What "checking" means here

The proof is written in **Lean 4**, a *proof assistant*: a program that mechanically
checks every logical step against the axioms of mathematics. If Lean accepts the
file, the theorem follows from those axioms — there is no "trust me" step, no
hand-waving, no reviewer who might have missed something. You are asking the
computer to re-run that check on your own machine.

Two things you will confirm:
1. **It builds** — Lean accepts the whole development with **no `sorry`** (Lean's
   keyword for an unfinished step). No unfinished steps means no gaps.
2. **It is axiom-clean** — the theorem depends only on the three standard axioms of
   Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`). Nothing exotic, no
   `native_decide` (which would defer a step to unaudited compiled code).

---

## The zero-effort option: just look at the badge

If you do not want to install anything, GitHub already re-runs this check on every
change. Go to the repository:

> **[github.com/penpro/Erdos-Sandbox](https://github.com/penpro/Erdos-Sandbox)**

and click the green **"Lean CI"** badge (or the *Actions* tab). A green check means
GitHub's servers just rebuilt the entire proof from scratch and confirmed: no
`sorry`, and only the three standard axioms. That run *is* a verification — you are
trusting GitHub's computers instead of your own. To trust your own, read on.

---

## Step 1 — Open a terminal

- **macOS:** open the **Terminal** app (Applications → Utilities → Terminal).
- **Windows:** install [Git for Windows](https://git-scm.com/download/win), then
  open **Git Bash** (it gives you the same commands as Mac/Linux).
- **Linux:** open your terminal.

A "terminal" is just a text window where you type a command and press Enter. Copy‑
paste is fine.

## Step 2 — Install Lean's toolchain manager (`elan`)

`elan` downloads the exact Lean version this proof uses (`v4.31.0`) automatically.

- **macOS / Linux / Git Bash on Windows** — paste this and press Enter:
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  Accept the default when prompted. Then **close and reopen** the terminal (so it
  picks up the new tools).

- **Easiest alternative (any OS):** install [VS Code](https://code.visualstudio.com/)
  and its **"Lean 4"** extension — it installs `elan` and Lean for you the first
  time you open a Lean file.

## Step 3 — Download this repository

```bash
git clone https://github.com/penpro/Erdos-Sandbox
cd Erdos-Sandbox/lean/ep488
```

(No git? Use the green **"Code → Download ZIP"** button on the repository page,
unzip it, and `cd` into the `lean/ep488` folder inside.)

## Step 4 — Fetch the prebuilt library and build the proof

```bash
lake exe cache get      # downloads a prebuilt copy of Mathlib (Lean's math library)
lake build Ep488        # checks the entire proof
```

- `lake exe cache get` saves ~30 minutes by downloading Mathlib rather than
  compiling it. (~1–3 minutes.)
- `lake build Ep488` is the real check. When it finishes you should see:

  ```
  Build completed successfully (NNNN jobs).
  ```

  **That line is the verification.** If any step were unfinished, Lean would print
  a `declaration uses 'sorry'` warning; there are none.

## Step 5 — Confirm it is axiom-clean

```bash
lake env lean Ep488/QuadCheck.lean
```

This prints, for the main theorem:

```
'Erdos488.ep488_core_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are the standard logical axioms every Mathlib theorem may use. Seeing
**only** them — and no `sorryAx` — means the proof rests on nothing but ordinary
mathematics. (The committed file
[`lean/ep488/quad-axioms.txt`](https://github.com/penpro/Erdos-Sandbox/blob/main/lean/ep488/quad-axioms.txt)
records the same output.)

**You have now verified**, on your own machine, that Erdős #488 holds for every
finite set whose primitive core has at most four elements — with no gaps.

---

## Optional — run the computational evidence (Rust)

Separately from the proof, the repo has a fast exact-integer search tool that
*looks* for counterexamples (it finds none). This is **evidence, not proof**, but
it is satisfying to run.

1. Install Rust from [rustup.rs](https://rustup.rs) (one command, accept defaults).
2. Then:
   ```bash
   cd ../../fastcheck
   cargo run --release -- selftest
   cargo run --release -- quads 60 --uncovered
   ```
`selftest` sanity-checks the tool; `quads 60` scans primitive quadruples with
entries up to 60 for any counterexample and reports the worst ratio it finds
(always below 2). See [`fastcheck/README.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/fastcheck/README.md).

---

## Troubleshooting

- **`lake: command not found`** — you did not reopen the terminal after installing
  `elan`, or it is not on your PATH. Close and reopen the terminal; on Windows use
  Git Bash.
- **`lake exe cache get` fails** — re-run it; it is network-flaky. Worst case,
  `lake build Ep488` will compile Mathlib itself (slow, but works).
- **It runs out of memory** — Lean/Mathlib wants ~4–8 GB free RAM. Close other apps.
- **Windows line-ending or path warnings** — harmless; the build still succeeds.

Stuck? Open an [issue](https://github.com/penpro/Erdos-Sandbox/issues) — questions
from non-programmers are welcome, and improving these instructions is useful.

---

[← back to the main write-up](./) &nbsp;·&nbsp;
[set up your own AI sandbox →](./sandbox-setup)
