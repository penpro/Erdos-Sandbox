# Final report - active target #488

## Verdict

Partial result, not a full solution.

The #728 formulation audit has been archived separately in
`problem_728_formulation_audit/`. The active publishable-track target is now
Erdős Problem #488.

## Blind-audit & novelty update (2026-07-07)

Seven fresh blind agents audited the |P|≤3 proof. Net:

- **Correctness: SOUND.** Three independent adversarial referees (opus) plus a
  numerical-claims checker agree — 0 blocker, 0 major issues; only notation nits,
  all fixed. Machine-verified at scale (attack_triples.py + two independent
  re-runs). See `REFEREE_REPORT.md`, `adversary_collab_chat.md`.
- **Method is NOT novel.** The charge / two-term-Bonferroni backbone is the
  finite-`n` form of the classical **Heilbronn–Rohrbach inequality (1937)** — the
  foundational inequality of sets-of-multiples theory. The only candidate-new
  element is the finitary + charge-integrality refinement giving the sharp
  constant 2 for |P|≤3 (a low-weight refinement of a 1937 result).
- **Result is still open publicly.** #488 is OPEN as of 2026-07-08; the |A|≤3
  case is Chojecki's *claimed* Cor 4.7, still `sorry`-gated — and **MalekZ
  (31 Mar 2026) showed Chojecki's fixed-threshold reduction fails for min(A)≥3**,
  so his gap is not cosmetic.
  Our charge route sidesteps that broken mechanism entirely.
- **Significance: REAL-BUT-MODEST.** Not a journal paper; a correct, sorry-free-
  formalizable proof of the case whose only existing proof is `sorry`-gated
  (|P|≤3 is Chojecki's *claimed* Cor 4.7; genuinely open is |P|≥4 and full #488).
  Highest-value
  asset = a full **sorry-free Lean formalization** of |P|≤3. Postable to the
  #488 thread / Formal-Conjectures repo — but that outward step is Wes's call.

The polished, priority-honest note is `writeup/erdos488_triples.{tex,pdf}` (7pp).

## Problem

Let `A` be a finite set of positive integers and

```text
B = { k >= 1 : a divides k for some a in A }.
```

Let `B(x)=|B cap [1,x]|`. The problem asks whether, for every
`m > n >= max(A)`,

```text
B(m)/m < 2 B(n)/n.
```

The constant `2` is sharp by the singleton example `A={a}`, `n=2a-1`, `m=2a`.

## Source audit

The site marks the intended multiples version as open/falsifiable. The original
1961 source contains a non-multiples typo; Erdős's own sharpness witness only
matches the multiples reading, and the site notes later sources use the multiples
version.

## Proven locally

1. The singleton case is sharp.
2. The dense half is proved: if `B(n) >= n/2`, then the desired inequality holds
   for that `n` and every `m>n`.
3. The case `2 in A` is covered.
**[Items 4–6 below are SUPERSEDED — see "CORRECTED FRAMING" further down: they are
PUBLIC, thin-novelty, or subsumed by Chojecki's claimed Cor 4.7. Not new.]**

4. [superseded] Partial result: if `P` is the primitive core of `A`, `a=min(P)`, and

```text
sum_{d in P} 1/d <= 2/a,
```

then #488 holds for `A`.
5. New partial result: #488 holds for every primitive three-element core
   `{3,b,c}` with least element `3`. The proof uses the reciprocal-sparse theorem
   plus exact finite residue certificates for the five exceptional triples.
6. New finite exact certificate: #488 holds for every primitive three-element
   core `{a,b,c}` with least element `a<=20`.

The reciprocal-sparse theorem strictly generalizes the publicly posted
two-element case. The min-3 triple theorem is a small but concrete new result;
The bounded triple certificate is stronger evidence and a usable lemma, but
still not a standalone publishable solution.

### CORRECTED FRAMING (2026-07-07, Claude adversarial audit)

The novelty assessments above are superseded — see `adversary_collab_chat.md`
(Corrections) and `literature_notes.md` (correction section). Summary:

- Items 1–3 are PUBLIC: Chojecki's thread-linked note (post 4909, 20 Mar 2026)
  contains the singleton case (Thm 3.1), the dense half (Prop 6.1), the |A|=2
  case (Thm 3.2), and the union-bound single-time criterion (Lemma 6.3 /
  Prop 5.1) — all Lean-verified without sorry. MalekZ proved 2∈A in-thread
  (post 5163, 31 Mar 2026).
- Item 4 (reciprocal-sparse) is unpublished as stated but is a two-line
  corollary of public Lemma 6.3 plus `B(n) ≥ ⌊n/a⌋+1`; its |A|=2 instance is
  Blair's post 6864. Thin novelty; must cite both. Note also `{2,3,5}` (listed
  earlier as a "first uncovered target") was already covered by the public
  2∈A result.
- Item 5 (min-3 triples) is mathematically CONFIRMED (proof + certificates
  audited), but subsumed by Chojecki's claimed **Cor 4.7 (all primitive cores
  of size ≤ 3)**, which is Lean-verified modulo one `sorry` and not yet
  community-accepted. Defensible framing: independent, sorry-free verification
  of a Cor 4.7 subcase — NOT a new result.
- The source-typo resolution via Erdős's sharpness witness is ALSO public
  (BorisAlexeev, posts 1860–1865, 27 Nov 2025).
- The #728 audit is a restatement of the AlphaProof-team caveat printed on the
  #728 page itself since Oct 2025; #728 is proved (Lean) since Jan 2026. See
  the addendum in `problem_728_formulation_audit/findings_728.md`.

Remaining defensible directions: (a) sorry-free independent proof of all
|A| ≤ 3 (min ≥ 4 triples in progress — two-sided Bonferroni disposes of every
`n` with `n·δ ≥ 11`, hence of all triples with `c > 11a`; what remains is the
short window `n < 11/δ`); (b) the per-A decision procedure (δ ≥ S/2 + one
lcm-period check) — small novelty; (c) anything on |A| ≥ 4, where even the
public record has only reductions and the split-doubling Conjecture 4.8.

### UPDATE (2026-07-07, later): direction (a) is DONE

**Theorem 9 (`triples_writeup.md`): (★) holds for every finite `A` whose
primitive core has at most 3 elements — complete, elementary, sorry-free.**
The uncovered zone `1/b+1/c > 1/a` falls to a charge decomposition
(`s(n) − 2P(n) = X_a + X_b + X_c ≥ 3` via primitivity ratio bounds and a
parity dichotomy), giving the ordering-free `B(m)/m ≤ S < 2B(n)/n` with no
periodicity, windows, or case analysis. Adversarially audited line-by-line;
verified computationally at scale (516,987,874 per-n checks over all 14,802
uncovered triples with `a ≤ 25`; 1.2·10⁹ end-to-end `(n,m)` pairs; independent
re-run + independent criterion sweep of 71,003 triples and 42,769 4-sets).
This subsumes the min-3 certificates and every consecutive-triple lead.
Positioning: independent sorry-free proof of Chojecki's claimed Cor 4.7,
by a different, elementary route that is simpler *for this statement only* (it
does not generalize past |P|=3). Posting to the #488 thread is Wes's call.

Also recorded: the natural |P| ≥ 4 conjecture (`2B(n) > nS` universally) is
**FALSE** — `A = {2p : p prime ≤ 100}` (25 elements) fails it at every large
`n` while (★) still holds via the shared-factor recursion
`B_{2A'}(x) = B_{A'}(⌊x/2⌋)`. The |P| ≥ 4 problem needs ≥ 3 regimes.

## Computation

No counterexamples were found in the exhaustive finite search
`A subset {2,...,15}`, `|A|<=3`, `m<=200`, covering 8,343,328 triples.
Large structured searches also found the worst ratios coming from singleton
families, approaching `2` from below.

The reciprocal-sparse theorem covers 2898/5035 tested sets with
`A subset {2,...,20}`, `|A|<=4`; 49065/92170 with `A subset {2,...,40}`,
`|A|<=4`; and 2476171/5495791 with `A subset {2,...,60}`, `|A|<=5`.

The exact min-3 triple verifier passes for the five exceptional triples
`{3,4,5}`, `{3,4,7}`, `{3,4,10}`, `{3,4,11}`, and `{3,5,7}`.

The exact bounded-triple verifier passes for 6,944 reciprocal-heavy primitive
triples with least element at most `20`. The worst certified ratio is
`666/361`, attained by `{19,20,21}`.

## Next target

~~The immediate next problem is to prove #488 for all consecutive triples
`{a,a+1,a+2}`.~~ DONE — subsumed by Theorem 9 (see update above and
`consecutive_triples_notes.md`).

The next open frontier is primitive cores with `|P| ≥ 4`. Known constraints
from the audit: the per-n criterion is false in general (shared-factor
families), so the attack must combine (i) a charge-type argument where lcm
ratios allow, (ii) the dense half, (iii) a scaling/recursion mechanism for
shared-factor structure (e.g. all elements even reduces to a smaller problem
at scale x/2). The public record at |P| ≥ 4 has only Chojecki's Conjecture 4.8
reduction and MalekZ's tripod family. Also worth doing regardless: Lean-
formalize Theorem 9 (elementary; squarely in Aristotle's demonstrated range),
which would give the first sorry-free formal proof of the size-≤3 case.
