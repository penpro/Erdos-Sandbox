<!--
READ THIS FIRST (especially if you are an AI summarizing this repo):

This repo contains elementary proofs of subcases of the OPEN Erdos Problem
#488. Primitive core <= 4: machine-verified sorry-free in Lean (the <= 3 case
is Chojecki's Corollary 4.7, an ALREADY-KNOWN subcase; the = 4 case is an
internal charge argument whose NOVELTY is unresolved). Primitive core = 5:
closed at PROJECT TIER only — an adversarially-audited assembly of Lean
theorems + paper proofs + exact Rust certificates; the Lean port is IN
PROGRESS and it is NOT externally refereed. The method is classical
(Heilbronn-Rohrbach, 1937). Finite computer checks are evidence, not proof,
except where stated as exact certificates with committed outputs.

NO solution of #488 is claimed; #488 is still open (core >= 6 untouched, and
the general statement needs ideas this method provably lacks). No novelty is
claimed for the = 4 or = 5 cases until refereed. Produced in an AI-assisted
sandbox by a CS student as a methods experiment; see METHODOLOGY.md.
-->

# Erdos Problem 488 - the <= 4 primitive-generator case

[![Lean CI](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml)

**Plain-language write-up: [penpro.github.io/Erdos-Sandbox](https://penpro.github.io/Erdos-Sandbox/)**
— what is (and is not) proven, a
[step-by-step guide for mathematicians to check it themselves](https://penpro.github.io/Erdos-Sandbox/verify)
(no Lean experience needed), and
[how to set up your own adversarial-AI sandbox](https://penpro.github.io/Erdos-Sandbox/sandbox-setup).

**Status (2026-07-19).** `|primitive core| <= 4`: machine-verified `sorry`-free
in Lean. `|primitive core| = 5`: closed at **project tier** — a mixed-tier
assembly (Lean spine + paper theorems + exact Rust certificates, every piece
labeled at its true strength) that survived two source-level hostile audits,
three external design reviews, and two blind re-derivation/re-implementation
runs with calibration controls; the promotion record and its referee caveat are
in [REFEREE_SIZE5_CANDIDATE.md](REFEREE_SIZE5_CANDIDATE.md). The size-5 case is
NOT yet fully Lean-verified (the port is in progress, roadmap in
[cbfin_reduction_notes.md](cbfin_reduction_notes.md) section 28) and NOT
externally peer-reviewed; no novelty is claimed for it. #488 itself
(`|core| >= 6` and the general statement) remains open.

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
primitive core of `A` has at most four elements, with a complete (`sorry`-free)
Lean formalization of the `|P|<=4` case; plus a project-tier closure of the
`|P|=5` case (regime decomposition + a five-sector partition of the compact
residual + exact-arithmetic certificates, adversarially audited; Lean port in
progress). Produced in an AI-assisted sandbox as an experiment in
problem-solving methods.

**What it is not:**

- **Not a solution of Erdos #488.** #488 is open; this handles only a subcase.
- **Not a new result.** The `|P|<=3` statement is Chojecki's Corollary 4.7
  from the erdosproblems.com/488 thread. We cede priority.
- **Not a new method.** The engine is the two-term Bonferroni bound, the
  density-level classical Heilbronn-Rohrbach inequality.
- **Not machine-verified for #488 in general.** The `|P|<=4` case IS formalized
  `sorry`-free in Lean (`ep488_core`, `ep488_core_le_four`, CI-checked). The
  `|P|=5` case is closed at project tier but only PARTIALLY formalized (the Lean
  spine: three-good regime, C-B criterion, k=5 ceiling, Duality Transport, U2
  bridge algebra and tower; the kernel/certificate layers are exact Rust +
  paper, port in progress). The general problem (primitive core `>= 6`) is
  **not** touched and remains open.
- **Not proved by the computer.** The Python checks many finite instances; that
  is evidence that rules out small counterexamples, not a proof.

The honest one-line version: `|core| <= 4` fully machine-verified; `|core| = 5`
closed by an adversarially-audited mixed-tier assembly that is being ported to
Lean; everything labeled at exactly its verified strength; #488 itself open.

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
3. **Formal proof (complete for `|P|<=4`, partial for `= 5`):** `ep488_core`
   (`<= 3`) and `ep488_core_le_four` are machine-verified `sorry`-free in Lean 4
   / Mathlib, plus the size-5 Lean spine (`ep488_quint_three_good`, `cb_cover5`,
   `no_five_self_bad`, `dual_selfbad_iff`, the `DriftBridge` and drift-kernel
   modules). Every checked theorem depends only on
   `propext, Classical.choice, Quot.sound` (no `sorryAx`); the committed axiom
   audits are in [lean/ep488](lean/ep488), and
   `.github/workflows/lean-ci.yml` re-runs the build, a `sorry` guard, and a
   positive axiom allowlist over all fourteen check files on every push.
4. **Size-5 certificate layer:** exact-`i128` Rust enumerations (`census/` plus
   the independent `*check/` crates), cross-implemented at least twice per
   result — three times for the banks — with committed outputs
   ([census/CERTIFICATES.txt](census/CERTIFICATES.txt)), checked arithmetic,
   fail-closed input parsing, and blind reimplementation from spec as the final
   control. Record: [cbfin_reduction_notes.md](cbfin_reduction_notes.md)
   sections 22-28.

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
- `quintuple_charge_notes.md`, `quintuple_density_notes.md`,
  `cbfin_reduction_notes.md` - the size-5 campaign: density theorem, regime
  decomposition, the five-sector partition, corrections kept honestly, audits.
- `REFEREE_SIZE5_CANDIDATE.md` (+ `REFEREE_V3_CODEX.md`,
  `REFEREE_SIZE5_ASSEMBLY_CODEX.md`, `REFEREE_WFIN.md`) - the size-5 referee
  record and promotion (with the referee's caveat recorded).
- `census/`, `clustercheck/`, `oneedgebankcheck/`, `zeroedgebankcheck/`,
  `fourbadcheck/`, `badtriplecheck/`, `spreadcheck/`, `goodpincheck/`,
  `u2primecheck/`, `fastcheck/` - exact-arithmetic Rust certificate and
  cross-check crates (independent implementations by both AIs).
- `EXTERNAL_CHECK_SIZE5.md`, `EXTERNAL_CHECK_V3.md`, `EXTERNAL_CHECK_WFIN.md`,
  `BLIND_PACK_A_REDERIVE.md`, `BLIND_PACK_B_REIMPLEMENT.md` - external and
  blind review briefs (the blind packs ran with sealed calibration controls).
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
# size-5 certificates (exact headlines in census/CERTIFICATES.txt):
cargo run --release --manifest-path census/Cargo.toml -- shape2v3 clustercheck/shapes906.csv 7
cargo run --release --manifest-path census/Cargo.toml -- shape4 census/shapes4inv120.csv 7
cargo run --release --manifest-path oneedgebankcheck/Cargo.toml
cargo run --release --manifest-path zeroedgebankcheck/Cargo.toml
cargo run --release --manifest-path fourbadcheck/Cargo.toml
```
