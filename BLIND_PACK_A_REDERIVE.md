# Blind re-derivation pack (Pack A)

You are a research mathematician. Prove or refute each claim below from
scratch. Do NOT search the web and do NOT browse any repository — work only
from this document. Where a claim is false, give an explicit counterexample;
where true, give a complete proof. Partial results ("true with constant C
replaced by C'") are valuable — state exactly what you can prove.

Throughout: all variables are positive integers. gcd/lcm are the usual ones.
A set is an ANTICHAIN if no element divides another. For an element e of a
5-element set P, its CHARGE is sum over the other four f of gcd(e,f)/f, and
e is BAD if its charge is >= 1, GOOD otherwise.

## Claim 1 (ceiling)

In any 5-element antichain of positive integers, the maximum element is never
bad relative to the other four IN THE DUAL SENSE: if e is the maximum and
x1..x4 the others, then gcd(e,x1) + gcd(e,x2) + gcd(e,x3) + gcd(e,x4) < e.
Determine the sharp constant: is the sum always <= (59/60)e, and which
configurations approach it?

## Claim 2 (divisor jump)

If x, y are distinct elements of an antichain and 4*gcd(x,y) < min(x,y),
then gcd(x,y) <= min(x,y)/5.

## Claim 3 (one-edge structure)

Let D = {b1, b2, b3, g1, g2} be a 5-element antichain with gcd(D) = 1 and
max(D)/min(D) < 7, in which exactly b1, b2, b3 are bad (dual sense: for each
bad b, the sum of its four gcds is >= b) and exactly one of the three pairs
{b1,b2}, {b1,b3}, {b2,b3} satisfies 4*gcd >= min (say {b1,b2}); the other two
bad pairs do not. Prove:
(a) both goods satisfy b3/gcd(b3, g_j) <= 10, and the smaller of the two
    values c_j = b3/gcd(b3, g_j) is 2 or 3, with 1/c1 + 1/c2 >= 3/5;
(b) writing u = gcd(b1,b2), b1 = u*alpha, b2 = u*alpha': the cofactors are
    coprime, min(alpha, alpha') <= 4, max(alpha, alpha') <= 27;
(c) writing L = lcm(c1,c2), v = b3/L (prove L | b3), and
    Sgam = L + L*k1/c1 + L*k2/c2 where g_j = b3*k_j/c_j: derive explicit
    upper bounds on u in terms of Sgam and the cofactors, and on v in terms
    of the cofactors and c1, c2 — in particular determine for exactly which
    (c1, c2) the bound on v fails and what bounds v in that case instead.
State your final bounds precisely. (This is the heart of the pack: derive
the bounds yourself; do not assume any given form is correct.)

## Claim 4 (zero-edge structure)

Same setting but NO bad pair satisfies 4*gcd >= min. Prove that for every
bad b and BOTH goods g, b/gcd(b,g) <= 10, and that consequently, anchoring
either good as a unit, every element of D is a rational multiple of it with
numerator and denominator bounded by explicit constants — so there are only
finitely many such D up to nothing at all (i.e., absolutely finitely many),
and describe how to enumerate them completely.

## Claim 5 (4-bad filter)

Now suppose FOUR elements b1..b4 of the 5-element antichain are bad and one
good g remains, with gcd(b1,..,b4) = s and w_i = b_i/s. Prove that for every
i: sum over j != i of gcd(w_i, w_j)/w_j >= 1/2, and that max(w)/min(w) < 7.
Then prove or refute: the set of quadruples (w1 < w2 < w3 < w4), gcd = 1,
antichain, satisfying these conditions, is finite — and if you can, bound
min(w) explicitly. (Hint-free; if you find an infinite family, exhibit it.)

## Deliverable

For each claim: PROVED (full proof) / REFUTED (counterexample) / PARTIAL
(exact statement proved). Then list any additional structural consequences
you noticed that the claims miss.
