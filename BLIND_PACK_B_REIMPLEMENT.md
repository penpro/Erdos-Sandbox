# Blind re-implementation pack (Pack B)

You are given precise specifications of three finite enumerations. Implement
them YOURSELF (Python is fine; use exact integer arithmetic only — fractions
via cross-multiplication, never floats), run them, and report your outputs.
Do not browse the web or any repository; work only from this document. Your
outputs will be compared against an existing implementation you have not
seen. Report exactly what your code produces.

Common definitions: gcd/lcm usual; a list of positive integers is an
ANTICHAIN if no element divides another. For a 5-element list D, vertex i is
SELF-BAD if sum over j != i of gcd(D[i], D[j]) >= D[i]. A pair (x,y) is a
STRONG EDGE if 4*gcd(x,y) >= min(x,y).

A 5-element sorted list D = [d0..d4] is a COMPACT RESIDUAL if:
  (R1) antichain, gcd of all five = 1;
  (R2) at most 2 vertices are NOT self-bad;
  (R3) window: 7*(d0+d1+d2+d3+d4) <= 1135*d0;
  (R4) CRIT: 2*(sum(D) - 2*sum over pairs of gcd) <= 7*d0;
  (R5) ratio: d4 < 7*d0.

## Task B1: the one-edge bank

Enumerate ALL compact residuals with exactly 3 self-bad vertices whose three
bad vertices induce exactly ONE strong edge. Search space: every tuple of the
form (sorted) {u*a, u*a', v*L, v*(L*k1 div c1), v*(L*k2 div c2)} where:
  a, a' in [2, 27], coprime, min(a,a') <= 4, max < 7*min;
  c1 in {2, 3}; c2 in [c1, 10]; 5*(c1 + c2) >= 3*c1*c2;
  k1 in [2, 7*c1); k2 in [2, 7*c2); gcd(k1,c1) = gcd(k2,c2) = 1;
  k1*c2 != k2*c1;
  L = lcm(c1, c2); the two division terms must be exact integers by
  construction (verify);
  u in [1, Sgam * amax div (amax - 1)] where Sgam = L + L*k1 div c1
    + L*k2 div c2 and amax = max(a, a');
  v in [1, Vmax] where Vmax = min(7*u*amin div L, (a + a')*c1*c2 div
    (c1*c2 - c1 - c2)) if c1*c2 - c1 - c2 > 0, else 7*u*amin div L,
    with amin = min(a, a').
Deduplicate the resulting 5-element sets; keep those passing the compact-
residual test AND the exactly-3-bad AND exactly-one-strong-edge tests.
For each member, also run this TOWER CHECK: let l = lcm of the five, P =
sorted [l div d for d in D], prod = product(P), nsum = sum(prod div p),
cap = (1135*prod) div (7*nsum) - 1; incrementally count B(m) = #{k <= m :
some p in P divides k} for m = 1..cap; for every m in [max(P), cap] require
2*B(m)*prod - (m+1)*nsum > 0. Report: the full member list (sorted lists),
the count, and any tower failures.

## Task B2: the zero-edge bank

Enumerate ALL compact residuals with exactly 3 self-bad vertices and ZERO
strong edges among the bads. Method: for c1, c2 in [2,10] with
5*(c1+c2) >= 3*c1*c2, k1 in [2, 7*c1) coprime to c1 with c1 < 7*k1, k2 in
[2, 7*c2) coprime to c2 with c2 < 7*k2: record the "bad ratio" r = c1/k1
(reduced) and the "second-good ratio" t = (c1*k2)/(k1*c2) (reduced),
skipping t = 1. Group all r values by t. For each t and each choice of THREE
DISTINCT r values from its group, form the five rationals
{1, t, r_a, r_b, r_c}, clear denominators by their lcm, divide by the
overall gcd, sort — a candidate integer 5-list. Keep candidates passing the
compact-residual + exactly-3-bad + zero-strong-edge tests; deduplicate; run
the same tower check. Report the member list, count, tower failures.

## Task B3: the 4-bad shape inventory

Enumerate ALL quadruples w1 < w2 < w3 < w4 with w1 <= 300 satisfying:
  gcd(all four) = 1; antichain; w4 < 7*w1;
  for EVERY i: sum over j != i of gcd(w_i, w_j) * (prod over l != i,
    l != j of w_l) * 2 >= product over j != i of w_j
  (i.e. sum_j gcd(w_i,w_j)/w_j >= 1/2, cross-multiplied).
Report: the count, the largest w1 appearing, and the full sorted list.

## Deliverable

Your code (complete), and for each task the exact outputs. If any spec point
is ambiguous, state the ambiguity, choose a reading, and flag it. Do not
attempt to guess what the "expected" answers are.
