# Selected problem — Erdős #488

## Statement (erdosproblems.com/488, the intended "multiples" version)

Let `A` be a finite set of positive integers and
```
B = { k ≥ 1 : a | k for some a ∈ A }      (the set of multiples of A)
```
Write `B(x) = |B ∩ [1,x]|`. Is it true that for every `m > n ≥ max(A)`,
```
        B(m)        B(n)
        ────  <  2 ·────   ?            (★)
          m           n
```
The constant `2` is best possible: for `A = {a}`, `n = 2a−1`, `m = 2a` the ratio
equals `2 − 1/a → 2`.

- **Status on erdosproblems.com:** open (logical tag `falsifiable`). No solution,
  partial or complete, is claimed on the page.
- **Sources:** P. Erdős, *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató
  Int. Közl. **6** (1961) 221–254 — Problem **27**, p. 236 `[Er61]`; restated in
  Erdős 1966 `[Er66]`; R. Guy, *Unsolved Problems in Number Theory*, problem E5.
- **Primary source PDF:** https://users.renyi.hu/~p_erdos/1961-22.pdf (saved
  locally as `scratch_erdos1961.pdf`; Problem 27 on p. 236).

## The typo, resolved independently from the primary source

The database owner notes that `[Er61]` literally writes the **complement**
version — "the integers *no one of which is a multiple* of any `a`" (i.e. `a ∤ k`)
— and conjectures this is a typo for the multiples version, citing `[Er66]`.

I verified this from the primary source and, crucially, from Erdős's **own
tightness witness**, which disambiguates the intent without needing `[Er66]`:

- Witness `A={a}`, `n=2a−1`, `m=2a`.
- **Multiples** reading: `B(n)=1`, `B(m)=2`, ratio `(2/2a)/(1/(2a−1)) = 2−1/a → 2`.
  ✔ matches Erdős's claim "2 cannot be replaced by any smaller constant".
- **Non-multiples** reading: `B(x)=x−⌊x/a⌋`, ratio `= 1 − 1/(2a) < 1`. ✘ does
  **not** approach 2 — so the literal text is internally inconsistent.

Therefore the *intended* problem is unambiguously the multiples version (★). This
is the version I attack. (The literal non-multiples version is separately **false**
— it fails with ratio → ∞; see `final_report.md` §Alternate version.)

The condition `m > n ≥ max(A)` is exactly Erdős's "`a₁<a₂<⋯≤n`".

## Why this problem was selected

1. **Exact & elementary.** No specialized prerequisites even to state; every
   quantity is a finite integer count.
2. **Genuinely open**, with a clean primary source and a known-sharp constant.
3. **Computationally decisive.** Extensive search (single-element, random,
   interval/Besicovitch, geometric, prime-shell sets; `n` up to ~30000) shows the
   ratio always stays `< 2` and the supremum is the trivial single-element family.
   This *tells me the direction*: (★) is true and tight, so the target is a proof
   (open → proved), not a counterexample.
4. **Checkable** either way by any mathematician.
5. **Attackable**, with a real foothold: the inequality is equivalent to a clean
   complement inequality that already yields a rigorous proof of half the cases.

## Attack plan

1. **Statement normalization** (`proof_attempt.md` §1): quantifiers, universe,
   degenerate cases (`1∈A`, `|A|=1`), the complement reformulation.
2. **Sharp single-element case** — complete elementary proof that the extremal
   ratio is exactly `2 − 1/a`. (Done, rigorous.)
3. **Complement reduction** — prove (★) ⇔ `2γ(n) − γ(m) < 1` where `γ = C(x)/x`,
   `C` = non-multiples; deduce (★) unconditionally whenever `B(n) ≥ n/2`. (Done.)
4. **Sparse case** `B(n) < n/2` — the remaining core. Attempt a full proof;
   otherwise record rigorous partial progress and the precise gap.
5. **Alternate (non-multiples) version** — give an explicit infinite family
   proving it false (generalizing Cambie's observation). (Done, rigorous.)
6. **Computation** — exhaustive small verification with a written-down search
   space, plus the large structured search. (`counterexample_search.py`,
   `computational_results.md`.)

## Do-not-switch note

Selection is final unless (★) turns out to be already fully resolved in the
literature or impossible to formalize — neither is the case. Backups (#287, #358)
are recorded in `candidate_scan.md` only as contingencies.
