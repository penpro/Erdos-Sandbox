# Erdos Problem #728: Formulation Audit

Status of this note: internal sandbox finding; not claimed as novel; not worth
publishing as a standalone mathematical result.

## ADDENDUM (2026-07-07, Claude adversarial re-verification)

The arithmetic below is correct (re-verified symbolically, by direct factorial
brute force, and by running the script). However, the construction is **not a
finding of this audit**: the identical construction, with the same variable
names (`a=n+w+1`, `b=(n+w+1)!/n!-1`, `w>=max(C log n, eps n)`), is printed on
the erdosproblems.com/728 page itself, attributed to the **AlphaProof team**,
and has been there since at least the 2025-10-20 revision — as are the
`a=b=n` remark and the `a,b<=(1-eps)n` fix suggested below. #728 has been
marked **proved (Lean)** since 2026-01-05: Barreto/GPT-5.2 + Aristotle proved
the intended two-sided version (`eps n <= a,b <= (1-eps)n`,
`C1 log n < a+b-n < C2 log n`); see arXiv 2601.07421. The forum thread reached
consensus that this resolves the problem as intended.

Disposition: this note confirms already-documented site content. Do not post
anything to the #728 thread. See `adversary_collab_chat.md` (Corrections).

## Summary

The literal written formulation of Erdos Problems #728 is true for a degenerate
reason. It does not upper-bound the variables \(a\) and \(b\), so one can take
\(a>n\) and make \(b\) very large in a way that forces the factorial divisibility.

This is not a solution of the intended nontrivial problem. It is only a check
that the written formulation needs extra hypotheses, such as
\(a,b\leq (1-\delta)n\), to capture the intended question.

Source page: https://www.erdosproblems.com/728

## Written Statement

For sufficiently small \(C>0\) and \(\epsilon>0\), are there infinitely many
integers \(a,b,n\) such that

\[
a\geq \epsilon n,\qquad b\geq \epsilon n,\qquad
a!b!\mid n!(a+b-n)!,
\]

and

\[
a+b>n+C\log n?
\]

## Result

For every fixed \(C>0\) and every fixed \(\epsilon>0\), the written statement has
infinitely many solutions.

## Proof

Fix \(C>0\) and \(\epsilon>0\). For any sufficiently large positive integer \(n\),
choose an integer

\[
w\geq \max(C\log n,\epsilon n).
\]

Define

\[
a=n+w+1,\qquad b=\frac{(n+w+1)!}{n!}-1.
\]

Then \(a\geq \epsilon n\), and \(b\geq \epsilon n\) for all sufficiently large
\(n\). Also

\[
a+b-n=b+w+1.
\]

Now compute

\[
\frac{n!(a+b-n)!}{a!b!}
=
\frac{n!(b+w+1)!}{(n+w+1)!b!}.
\]

Since

\[
\frac{(n+w+1)!}{n!}=b+1,
\]

we have

\[
\frac{n!(a+b-n)!}{a!b!}
=
\frac{(b+1)(b+2)\cdots(b+w+1)}{b+1}
=(b+2)(b+3)\cdots(b+w+1),
\]

which is an integer. Hence \(a!b!\mid n!(a+b-n)!\).

Finally,

\[
a+b-n=b+w+1>C\log n,
\]

so \(a+b>n+C\log n\). Since \(n\) can be chosen arbitrarily large, this gives
infinitely many triples.

## Interpretation

The construction uses \(a>n\) and huge \(b\). Therefore it does not touch the
intended logarithmic-barrier problem. It merely confirms that the written
statement is too weak unless additional upper bounds are included.

Even adding only \(a,b\leq n\) would not fully remove degeneracy, since
\(a=b=n\) gives \(n!n!\mid n!n!\) and \(2n>n+C\log n\) for all sufficiently
large \(n\).

## Verdict

This is a useful sanity check and formulation audit, but not a publishable new
finding. The active search for a publishable result should move to a different
target or to a strengthened version of #728 with the intended upper-bound
hypotheses.
