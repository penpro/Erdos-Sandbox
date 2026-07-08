# Candidate scan

Goal: identify exactly one high-probability Erdős target for a rigorous proof,
counterexample, status invalidation, or defensible partial result.

## Method

- Source of truth: the machine-readable database `data/problems.yaml` in the
  community repo `teorth/erdosproblems` (1217 problems), plus the individual
  problem pages on erdosproblems.com (fetched with a browser UA — plain fetch is
  403'd), plus the "AI contributions" wiki, plus primary Erdős sources.
- Prioritized: (a) problems flagged `ambiguous statement`; (b) unusual logical
  statuses (`falsifiable`, `verifiable`, `decidable`); (c) AI-claimed solutions
  with reported gaps; (d) small/computationally-explorable statements.
- For each shortlisted candidate I fetched the exact statement and ran a fast
  reconnaissance search (`scratch_probe.py`, `scratch_probe488*.py`) — a small
  counterexample would be an immediate result.

## Status distribution (from problems.yaml)

open 616 · proved 210 · proved(Lean) 116 · disproved 71 · disproved(Lean) 61 ·
solved 67 · solved(Lean) 23 · falsifiable 27 · decidable 9 · verifiable 7 ·
independent 3 · not provable 3 · not disprovable 4.

## Candidates examined (exact statements verified on-site)

### "Ambiguous statement" cluster (explicitly flagged by the database owner)
| # | Topic | Status | Verdict |
|---|---|---|---|
| 129 | Ramsey R(n;3,r) < C^√n | open, ambiguous | **No-go.** Already disproved *as written* by A. Girao (r=2 gives ≥C^n). Ambiguity understood; nothing to add. |
| 460 | Eggleton–Erdős–Selfridge reciprocal sum | open, ambiguous | No-go. Intended problem genuinely unclear; source paper not locatable. |
| 467 | congruence-class covering, 2 primes | open, ambiguous | Maybe. Missing quantifiers; intended statement uncertain. |
| 655 | distinct distances, "no 3 on a circle" | open, ambiguous | No-go. Already disproved *as written* by Z. Hunter (regular n-gon). |
| 660 | convex polyhedron in R³, ≥(1−o(1))n/2 distances | open, ambiguous | No-go (hard). Clean statement but a genuinely hard distinct-distance problem. |
| 662 | triangular-lattice distance counting | open, ambiguous | No-go. Literally nonsense as written (typos); intent unrecoverable. |
| 1163 | "describe statistically" subgroup orders of Sₙ | open, ambiguous | No-go. Too vague to formalize. |

### "Falsifiable / open" cluster (∀-statements; a finite counterexample would settle)
| # | Statement (paraphrase) | Recon result | Verdict |
|---|---|---|---|
| 23 | triangle-free on 5n vtcs → bipartite by deleting ≤ n² edges | — | Known-hard conjecture. |
| 64 | min-degree ≥3 → cycle of length 2^k (Erdős–Gyárfás) | — | Famous, hard. |
| 97 | convex polygon: a vertex with no 4 others equidistant | — | Geometry, hard. |
| 128 | dense induced subgraphs → triangle | — | Extremal, hard. |
| 287 | distinct nᵢ, Σ1/nᵢ=1 → max gap ≥ 3 | no CE ≤ den 400 | Elegant but tied by owner to a hard prime-pair conjecture. |
| 375 | run of composites → SDR of prime divisors (**Grimm**) | no CE ≤ 2·10⁵ | No-go: implies Legendre's conjecture. |
| 458 | LCM inequality [1..p_{k+1}−1] < p_k[1..p_k] | no CE, k<60 | No-go: Erdős–Graham "beyond our ability", ↔ Legendre. |
| **488** | **set of multiples: B(m)/m < 2·B(n)/n for m>n≥max(A)** | **true & tight** | **GO — selected.** See below. |
| 548 | Erdős–Sós tree-packing threshold | — | Famous, hard. |
| 583 | connected graph → ⌈n/2⌉ edge-disjoint paths | — | Hard (Gallai). |
| 617 | Ramsey r-colouring of K_{r²+1} | — | Hard. |
| 699 | binomial-coefficient gcd support | no CE, n<120 | Interesting (task-priority area) but likely hard. |
| 723 | projective plane order → prime power | — | No-go: enormous open problem. |
| 779 | primorial + prime is prime | ∃-statement | No-go: counterexample effectively impossible. |
| 982 | convex polygon: a vertex with ≥⌊n/2⌋ distances | — | Hard (Altman-type). |
| 993 | independence sequence of trees unimodal | — | No-go: famous, checked to large sizes. |
| 1082 | n pts no-3-collinear → ≥⌊n/2⌋ distances + one apex | — | Hard. |

### AI-claimed / invalidation cluster
| # | Status | Note | Verdict |
|---|---|---|---|
| 75 | open | AI "solves a variant"; but the variant gap is *already documented* (Erdős's own oversight). | No-go (not novel). |
| 358 | proved | site says proved; AI wiki says "major gaps" — potential mismatch, but I lack the accepted proof to audit. | Backlog. |
| 963 | open | dissociated subsets, log₂n vs Erdős's log₃n | Clean but improving the log base is hard. |
| 1040/1041/1044 | mixed | Erdős–Herzog–Piranian lemniscate problems | Complex-analysis, hard to make rigorous. |
| 1044 | solved(Lean) | Tang's proof, Lean-verified | No-go (verified). |
| 36 | open | minimum-overlap constant, active numeric race | No-go (only ε-improvements available). |

## Selection

**#488** selected. It is the unique candidate that is simultaneously: (i) exactly
statable and elementary; (ii) genuinely open with no claimed solution; (iii)
computationally decisive — my searches show it is **true and tight** (max ratio
→2 but never reached, extremal config = single element), so the target is a
**proof**; (iv) fully checkable; and (v) it has a clean *primary source* whose
own tightness witness lets me independently resolve the database's flagged typo.
See `selected_problem.md`.

Backups if #488 proves intractable: #287 (Egyptian-fraction gaps) and the #358
proved-vs-"gaps" audit.
