# Literature notes — Erdős #488

## Primary source (verified)

**[Er61]** P. Erdős, *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int.
Közl. **6** (1961) 221–254. Problem **27**, p. 236.
PDF: https://users.renyi.hu/~p_erdos/1961-22.pdf (saved: `scratch_erdos1961.pdf`).

Exact text (OCR, lightly cleaned):

> "Let `a₁ < a₂ < … ≤ n` be any sequence of integers, `b₁ < b₂ < …` the integers
> no one of which is a multiple of any `a`. `B(x) = Σ_{bᵢ≤x} 1`. Is it true that
> for every `m > n`,  `B(m)/m < 2·B(n)/n` ?  It is easy to see that in (1.27.1)
> 2 can not be replaced by any smaller constant; to see this let the `a`'s consist
> of `a₁`, `n = 2a₁ − 1`, `m = 2a₁`."

**Two facts extracted, both used in `selected_problem.md`:**
1. The bound `a₁<a₂<…≤n` is the constraint `max(A) ≤ n` (i.e. `n ≥ max A`).
2. The literal definition of `B` is the **non-multiples**. But Erdős's own
   tightness witness `A={a₁}, n=2a₁−1, m=2a₁` yields ratio `2−1/a₁ → 2` **only**
   for the *multiples* reading (for non-multiples that witness gives ratio
   `1−1/(2a₁) < 1`). The paragraph is thus internally inconsistent unless `B`
   means *multiples*. → The intended problem is the multiples version; "`a ∤ k`"
   in [Er61] is a typo for "`a | k`".

## Secondary sources

- **[Er66]** Erdős (1966) restates the problem with the **multiples** definition
  (per erdosproblems.com/488), corroborating the reading above.
- **R. Guy**, *Unsolved Problems in Number Theory* (3rd ed., 2004): the topic sits
  in the "sets of multiples / Besicovitch" circle (problem region E5); flagged
  there as unsolved. (Book not accessible offline; cited via erdosproblems.com.)
- **erdosproblems.com/488** (accessed 2026-07-07): status *open* (`falsifiable`).
  "No solutions, partial or complete, claimed." Notes the typo and that the
  *alternate* (non-multiples) version has counterexamples by **Cambie** (A = primes
  ≤ n, m = 2n), **Alexeev**, and **Aristotle**.

## Classical prior art for the METHOD (blind lit review, 2026-07-07) — the charge argument is NOT novel

A focused review of the classical sets-of-multiples circle (a blind opus agent +
web) found that the "charge / two-term Bonferroni" backbone of the |P|≤3 proof is
the finite-`n` form of a 1937 result:

- **Heilbronn (1937)**, *On an inequality in the elementary theory of numbers*,
  Proc. Camb. Phil. Soc. **33**, 207–209; and **Rohrbach (1937)**, *Beweis einer
  zahlentheoretischen Ungleichung*, J. Reine Angew. Math. **177**, 193–196:
  `δ(M(A)) ≥ Σ 1/aᵢ − Σ_{i<j} 1/[aᵢ,aⱼ]`. **This is exactly the density-level
  two-term Bonferroni bound = our Lemma 2.** The finite-`n` counting version is
  standard (the textbook opening move of the subject).
- **Behrend (1948)**, *Generalization of an inequality of Heilbronn and Rohrbach*,
  Bull. AMS **54**, 681–684 (+ the Behrend submultiplicativity inequality).
- **Ahlswede–Khachatrian (1995)**, *Density inequalities for sets of multiples*,
  J. Number Theory **55**, 170–180 ("sharper than Behrend… generalizes
  Rohrbach–Heilbronn").
- Standard references collecting all of the above: **Halberstam–Roth, *Sequences*
  (1966), Ch. V**; **R. R. Hall, *Sets of Multiples*, Cambridge Tract 118 (1996)**.

**Priority verdict (method):** the truncated-Bonferroni / charge mechanism is
**HIGH-risk = essentially classical (Heilbronn–Rohrbach)**; presenting it as a new
method would be embarrassing. The ONLY candidate-novel element: keeping it
finitary and using the **integrality of each per-generator charge** to extract the
*second* subtraction `s(n) − 2P₂(n) ≥ 3`, upgrading the density bound to the sharp
constant 2 for |P|≤3 — "a low-weight refinement of a 1937 result, not a new
method." The finitary two-point ratio statement (#488) itself is Erdős's and must
be attributed. The note (`writeup/erdos488_triples.tex`) now cites Heilbronn,
Rohrbach, Halberstam–Roth, Hall and frames the contribution accordingly.

Still to do before ANY refinement-novelty claim: check whether the finite-`n`
Heilbronn–Rohrbach form with the integrality sharpening appears as an exercise/
remark in Hall's tract or Halberstam–Roth Ch. V.

## Related theory (for the sparse case in §4 of `proof_attempt.md`)

- **Davenport–Erdős** (1936, 1951), "On sequences of positive integers": a set of
  multiples `B(A)` has a **natural density** `δ(B)` (= logarithmic density). This
  legitimizes `δ = lim B(x)/x` used in the necessary condition `inf g ≥ δ/2`.
- **Besicovitch** (1934): sets of multiples can have *no* natural density if `A`
  is infinite, and their finite counting functions oscillate substantially — this
  is the source of the irregularity (`sup g > δ` possible) that blocks a one-line
  proof. For *finite* `A` (our case) density exists and `B` is periodic mod
  `lcm(A)`, but the oscillation phenomenon still drives the sharpness.
- **H. Halberstam & K. F. Roth**, *Sequences* (Ch. V), and **R. R. Hall**, *Sets
  of Multiples* (1996): standard references; contain the density theory but, to my
  knowledge, **not** the finitary two-window inequality (★) itself.

## Current thread audit (2026-07-07)

The discussion thread at https://www.erdosproblems.com/forum/thread/488 contains
public partial progress that must not be claimed as new:

- Will Blair posted a proof of the two-element case on 2026-06-06, together with
  near-sharp examples `A={a,a+1}`.
- MalekZ posted a proof of a split-core tripod family
  `A={2u,3v,uv}` under coprimality/parity hypotheses on 2026-04-30.
- Earlier comments record work on the `2 in A` case and pair-tail split
  reductions, plus failed reductions and computational evidence.
- Tao noted that even asymptotic and prime-only variants remain nontrivial,
  and pointed toward alternating-sum / Granville-Soundararajan style estimates.

The reciprocal-sparse primitive-core theorem in `proof_attempt.md` Section 3A
appears not to be stated in the thread. It generalizes the posted two-element
case but remains elementary and should be treated as a partial result, not a
standalone publication claim.

### CORRECTION (2026-07-07, Claude): the thread audit above is materially incomplete

A full 30-post catalog of the thread plus its linked documents (fetched and
archived: `scratch_forum_488_parsed.txt`, `scratch_chojecki_488.txt`,
`scratch_malekz_note.txt`, `scratch_malekz_tripod.txt`,
`tmp/wf_result_a30cf8a95fd7761e0.md`) found the dominant prior-art document the
audit above missed:

**Przemek Chojecki, post 4909 (20 Mar 2026): 27-page note
"Signed Transport, Pair-Tail Reduction, and Low Layers in an Erdős
Density-Doubling Problem" (ulam.ai/research/erdos488.pdf, GPT-5.4-assisted),
with Aristotle Lean bundle (erdos488.tar.gz).** Contents relevant to us:

- Thm 3.1 (singleton), Thm 3.2 (|A|=2) — Lean-verified, no sorry.
- Prop 6.1 (dense case) = our Theorem 3 — Lean-verified.
- Lemma 6.3 + Prop 5.1 (single-time / union-bound criterion, exact-density and
  floor forms) — Lean-verified. Subsumes our union-bound criterion and §3A.
- **Cor 4.7: all primitive cores of size ≤ 3** — claimed unconditionally;
  Lean-verified **modulo one `sorry`** (`exact_one_count_ge_four`), which gates
  Thm 4.5, Cor 4.7, Cor 5.3. Not community-accepted (Blair still called |A|≥3
  "the first genuinely nontrivial case" on 06 Jun 2026; site header records no
  claimed partial solutions).
- Cor 2.5/2.6: near-extremizer finite-window reduction (n > (2W⁺+W⁻)/δ_A).
- Conjecture 4.8 (pair-vs-tail split doubling) + Prop 4.9: Conj 4.8 ⇒ full #488.

Other public items the audit above under-reported:
- MalekZ post 5163 (31 Mar 2026): complete proof of the **2∈A case** (so our
  Corollary 5 is PUBLIC, not just "worked on").
- MalekZ post 5089 + linked PDF (29–30 Mar 2026): exact periodicity
  `F(n) = δn + c_{n mod P}` and visible-slab finite-check reduction — the
  periodicity-certificate METHOD of `verify_min3_triples.py` is public in
  substance.
- Will Blair post 6864 (06 Jun 2026): |A|=2 proof — already in Chojecki's note
  (Thm 3.2, Lean); Blair's near-sharp family A={a,a+1}, n=2a−1, m=a².
- Tao post 5095 (30 Mar 2026): near-sharp example (primes in (n^{1/3},n^{1/2}),
  ratio 1.03114853…); post 5264 (06 Apr 2026): "four cheats" — resolves the
  prime-A, m→∞, unspecified-constant version via Bonferroni.
- BorisAlexeev posts 1860–1865 (27 Nov 2025): the typo counterexamples AND the
  witness-based argument that the multiples reading is the intended one — i.e.
  our "independent typo resolution from Erdős's sharpness witness" is ALSO
  public (Alexeev made the same argument first).

Novelty ledger after this correction (see adversary_collab_chat.md for the
full table): dense half, union-bound criterion, 2∈A, periodicity method,
witness-based typo resolution — all PUBLIC. Theorem 6 — unpublished as stated
but a 2-line remix of public results (cite Chojecki Lemma 6.3 + Blair 6864).
Min-3 triples — subsumed by sorry-gated Cor 4.7; defensible only as
independent sorry-free verification. δ ≥ S/2 finite-check phrasing and the
inf g ≥ δ/2 necessary condition — not explicitly public; small novelty at most.

## Cross-reference audit (does any source prove the full statement?)

- No source located proves the full finitary inequality (★) for the multiples version.
  The density references prove *asymptotic/limit* statements (existence of `δ`,
  logarithmic uniformity), which give only the necessary condition `inf g ≥ δ/2`,
  **not** the uniform `sup g < 2 inf g` over all `x ≥ max(A)`.
- Counterexamples attached to #488 for the **wrong** non-multiples version do not
  touch the intended problem.
- Some partial results are public in the thread, especially the two-element case.
- Conclusion: the intended (★) is genuinely open. Current local contributions
  include the reciprocal-sparse primitive-core theorem, the min-3 primitive
  triple theorem, and an exact finite certificate for all primitive triples with
  least element at most `20`. These still require outside novelty audit before
  any publication claim.
