---
title: "Erdős #488 for primitive cores of size ≤ 4 — a machine-checked proof"
description: "A sorry-free Lean 4 / Mathlib proof that Erdős Problem 488 holds whenever the primitive core of A has at most four elements. Not a solution of #488; the method is classical; novelty is modest and unrefereed."
---

# Erdős Problem 488 for primitive cores of size ≤ 4

**A `sorry`-free, machine-checked proof (Lean 4 / Mathlib) that Erdős Problem 488
holds for every finite set whose primitive core has at most four elements.**

[![Lean CI](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/penpro/Erdos-Sandbox/actions/workflows/lean-ci.yml)
&nbsp;·&nbsp; Source & Lean: [github.com/penpro/Erdos-Sandbox](https://github.com/penpro/Erdos-Sandbox)
&nbsp;·&nbsp; Top theorem: [`Erdos488.ep488_core_le_four`](https://github.com/penpro/Erdos-Sandbox/blob/main/lean/ep488/Ep488/Quad.lean)

**New here?** → **[Check the proof yourself](https://penpro.github.io/Erdos-Sandbox/verify)**
(step-by-step, no Lean experience needed) &nbsp;·&nbsp;
**[Set up your own AI sandbox](https://penpro.github.io/Erdos-Sandbox/sandbox-setup)**
(reproduce the method)

---

## Read this first — what this is, and what it is not

This page documents a **modest, machine-verified sub-case** of an **open** Erdős
problem. It was produced in an AI-assisted sandbox (OpenAI Codex and Anthropic
Claude working adversarially, with a human referee) as a methods experiment.
Please quote it at exactly the strength stated here.

**What it is.**
- A complete, `sorry`-free Lean formalization that #488 holds whenever the
  primitive core of `A` has `≤ 4` elements. The Lean kernel checks the proof; the
  audit shows it depends only on the three standard Mathlib axioms
  (`propext, Classical.choice, Quot.sound`) — no `sorryAx`, no `native_decide`.
- The `≤ 3` half is an independent, `sorry`-free re-proof of Chojecki's claimed
  Corollary 4.7 (whose own Lean bundle gates it behind one `sorry`). The `= 4`
  half proves a case that, to our knowledge, is **not** established in the public
  record (see the novelty caveat below).

**What it is not.**
- **Not a solution of Erdős #488.** #488 is open; this handles only `|core| ≤ 4`.
  The general case (`|core| ≥ 5`) is open here and, to our knowledge, everywhere.
- **Not a new method.** The engine is the classical **Heilbronn–Rohrbach /
  two-term Bonferroni** density inequality (1937). The `= 4` argument is an
  elementary case analysis, not a new technique.
- **Not "Chojecki's Conjecture 4.8."** That conjecture is the *general
  pair-vs-tail split doubling*, a stronger statement that (via his Prop 4.9)
  implies **all** of #488. We prove the weaker, assembled `|core| ≤ 4` inequality
  directly — closing, by a different route, the `|core| = 4` case that his
  *pair-vs-two-tail* bottleneck (the §7 "first unresolved" problem) leaves open,
  **without** proving that transport inequality itself.
- **Not human/literature-refereed for novelty.** A live-web literature sweep found
  no prior proof of the `|core| = 4` case, but the priority claim still wants a
  human eyeball. Treat the novelty as *likely but unconfirmed*.

---

## The problem (Erdős #488)

Let `A` be a finite set of integers `≥ 2`, and let

```
B = { k ≥ 1 : a divides k for some a in A }        (the "set of multiples" of A)
B(x) = |B ∩ [1, x]|                                (its counting function)
```

**Erdős #488 asks:** is

```
B(m)/m < 2 · B(n)/n        for all m > n ≥ max(A) ?
```

i.e. the density of multiples cannot more than double as the range grows. This is
Problem 27 of Erdős, *Some unsolved problems* (1961); it is
[listed open](https://www.erdosproblems.com/488) and independently formalized as
open (with a `sorry`) in Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project with the same inequality.

The **primitive core** (or primitive reduction) `core A` of `A` is the set of its
divisibility-minimal elements — a `∣`-antichain — and `B_A = B_{core A}`. `|core A|`
is the size of that antichain. Small primitive core is exactly the regime the
charge method reaches.

---

## The result

The top theorem, machine-checked in
[`lean/ep488/Ep488/Quad.lean`](https://github.com/penpro/Erdos-Sandbox/blob/main/lean/ep488/Ep488/Quad.lean):

```lean
theorem ep488_core_le_four {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a)
    (hAne : A.Nonempty) (hcore : (core A).card ≤ 4)
    {n m : ℕ} (hn : ∀ a ∈ A, a ≤ n) (hm : n < m) :
    n * (Bgen A m).card < 2 * m * (Bgen A n).card
```

Here `Bgen A n` is `B_A(n)` and the conclusion `n · B_A(m) < 2 · m · B_A(n)` is the
cross-multiplied (division-free) form of `B_A(m)/m < 2 · B_A(n)/n`; `hn : ∀ a ∈ A,
a ≤ n` is exactly `n ≥ max(A)`. The statement is **character-for-character
identical** to our own `sorry`-free `≤ 3` theorem `ep488_core` — only the
core-size bound changes from `≤ 3` to `≤ 4` — and its conclusion is the same
doubling inequality DeepMind formalizes as the full open problem (they impose no
`|core|` bound, so ours is a restricted instance of their open target).

More strongly, for a primitive quadruple `P` with reciprocal sum `S = Σ 1/d`, the
development's pointwise inequalities yield the ordering-free sandwich

```
sup_m B(m)/m ≤ S < 2 · inf_{n ≥ max P} B(n)/n,
```

which yields #488 without the `m > n` hypothesis.

---

## The proof, in brief

The engine is the **charge method** (Heilbronn–Rohrbach at density level; a
finitary two-term Bonferroni bound with integrality). For an element `e` of the
core, define its **charge** `Σ_{f ≠ e} gcd(e,f)/f`; call `e` *good* if this is
`< 1`. Two facts:

1. **Good ⟹ contributes.** If `e` is good then `X_e(n) = ⌊n/e⌋ − Σ_f ⌊n/lcm(e,f)⌋ ≥ 1`
   for `n ≥ max`.
2. **Two good charges suffice (size 4).** Exact 4-set inclusion–exclusion plus a
   nonnegative pointwise weight table give `2·B(n) > n·S`, hence (with the union
   bound `B(m)/m ≤ S`) the #488 inequality — provided at least two of the four
   core elements are good.

The combinatorial heart is that **every primitive quadruple has at least two good
charges**:

- **The least element is always good** (`least_good`).
- **If the second element is bad, the third is good** (`c_good_of_b_bad`): a
  "bad" second element forces its `a`-cofactor to equal 2, after which the reduced
  ratios `c/b` and `d/b` fall into exactly **five shapes**
  (`3/2, 5/3`), (`3/2, 5/2`), (`4/3, 3/2`), (`5/4, 3/2`), (`6/5, 3/2`) — an
  `interval_cases` enumeration on the cofactors — and `c` is good in each.

The two good elements are then relabelled into the two-good-charge proposition,
and a `min'/max'` extraction reduces an arbitrary `≤ 4`-element antichain (and,
via `B_A = B_{core A}`, an arbitrary finite `A`) to the sorted quadruple. Sizes
`≤ 3` are handled by the antecedent development (Chojecki's Cor 4.7 route,
re-proved `sorry`-free). Full notes: [`quadruple_charge_notes.md`](https://github.com/penpro/Erdos-Sandbox/blob/main/quadruple_charge_notes.md).

---

## Why it stops at 4 (the honest frontier)

The method **provably** does not extend to size 5 by the same closing:

- The size-4 miracle "every quadruple has ≥ 2 good charges" fails at size 5:
  `{4, 6, 10, 14, 15}` has **one** good charge.
- The naive rescue (drop to 2 good, group the other 3) makes the pointwise weight
  **`−1`** at a point divisible by exactly the 3 grouped elements. There is no
  flat pointwise extension.
- The size-5 residual is **unbounded**: `{2, 3, 5, 7, p}` gives a distinct hard
  quintuple for every prime `p`, so "a certificate per residual" never closes.

Note the residual quintuples all *satisfy* `2·B(n) > n·S` in computation — this is
a **proof-method gap, not a failure of #488**. The sharp open question is whether
`2·B(n) > n·S` holds for *every* primitive quintuple; that is currently unknown.
A partial size-5 result — the *three-good-charge* proposition (a primitive
quintuple with ≥ 3 good charges satisfies #488), covering
`43,290,285 / 43,291,981 ≈ 99.996%` of primitive quintuples with entries ≤ 100 —
is now formalized `sorry`-free in
[`Ep488/Quint.lean`](https://github.com/penpro/Erdos-Sandbox/blob/main/lean/ep488/Ep488/Quint.lean)
(`Erdos488.ep488_quint_three_good`). It is **not** a closure: the `≤ 2`-good
residual, where the new idea is needed, is untouched.

---

## Check it yourself

Everything is re-verified by CI on every push (the badge above). To reproduce
locally (needs [`elan`](https://github.com/leanprover/elan); Mathlib `v4.31.0`):

```bash
git clone https://github.com/penpro/Erdos-Sandbox
cd Erdos-Sandbox/lean/ep488
lake exe cache get          # prebuilt Mathlib
lake build Ep488            # compiles the whole development, sorry-free
# axiom audit — prints the axiom dependencies of the size-4 chain:
lake env lean Ep488/QuadCheck.lean
```

The audit output (committed as
[`quad-axioms.txt`](https://github.com/penpro/Erdos-Sandbox/blob/main/lean/ep488/quad-axioms.txt))
shows the top theorem's dependencies:

```
'Erdos488.ep488_core_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and every other theorem in the chain depends on a subset of those three — no
`sorryAx`, no non-standard axiom. The CI additionally enforces a positive
allowlist, so it fails if *any* axiom outside those three ever appears.

---

## Use it

`ep488_core_le_four` is an ordinary Mathlib-level lemma. Import `Ep488.Quad`,
supply a finite `A` of positive integers with `(core A).card ≤ 4`, and it gives
`n · B_A(m) < 2 · m · B_A(n)` for all `m > n ≥ max A`. The intermediate results are
reusable too — notably `ep488_quad_two_good` (the analytic engine: two good
charges ⟹ #488 for a quadruple) and `card_ie4` (exact 4-set inclusion–exclusion
in ℤ).

---

## Provenance & credits

- **The problem** is Erdős's (1961). The **method** is the classical
  **Heilbronn–Rohrbach inequality (1937)**.
- The **`≤ 3` result** is **Przemysław Chojecki's** claimed Corollary 4.7 (his
  Lean bundle gates it behind one `sorry`); we cede priority and re-prove it
  independently, `sorry`-free.
- The **`= 4` charge argument** was authored by **OpenAI Codex** and audited by
  **Anthropic Claude**; **Claude** wrote the Lean formalization. The whole thing
  was produced in a public "adversarial collaboration" sandbox run by a computer
  science student (**Wes**) as the human referee — the process (rival LLMs
  checking each other) is offered as a methods experiment alongside the math.
- Related thread work is credited on the
  [erdosproblems.com #488 thread](https://www.erdosproblems.com/488) (MalekZ on
  the `2 ∈ A` case; Will Blair on `|A| = 2`; Boris Alexeev; Terence Tao; and
  others).

If you find prior art for the `|core| = 4` case, or an error, please open an issue
on the [repository](https://github.com/penpro/Erdos-Sandbox/issues) — that is
exactly the review this note still wants.

---

*Machine-verified, honestly scoped, and deliberately un-hyped. #488 remains open.*
