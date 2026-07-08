# Erdős #488 for all primitive triples — complete proof

**Status: PROVED — an elementary proof of an ALREADY-CLAIMED case (Chojecki's
Cor 4.7); not a new result or method. See the priority note below.** Covers all
three-element primitive cores, any least element ≥ 2.
Computational checks: `attack_triples.py` (exact integer arithmetic, finite
instance checks — not a substitute for the proof; scope in §8).

> **Priority & novelty (read first).** The *result* is Chojecki's Corollary 4.7
> (erdosproblems.com/488 thread, 20 Mar 2026), proved there by other means but
> Lean-verified only modulo one `sorry`; the *method's backbone* (the two-term
> Bonferroni bound of Lemma 2) is, at the density level, the classical
> **Heilbronn–Rohrbach inequality (1937)**. The only candidate-new element is the
> finitary + charge-integrality refinement giving the sharp constant 2 for
> |P|≤3. "Everything below is new" means **new relative to our earlier files**,
> not world-first. The polished, priority-honest writeup is
> `writeup/erdos488_triples.{tex,pdf}`; see also `final_report.md`,
> `literature_notes.md`. Confirmed SOUND by three independent adversarial referees
> (see `adversary_collab_chat.md`, `REFEREE_REPORT.md`).

## 0. Setting and statement

Let `A` be a finite set of integers `≥ 2`, `B = {k ≥ 1 : a | k for some a ∈ A}`,
`B(x) = |B ∩ [1,x]|`. Erdős #488 asks:

> **(★)** For all integers `m > n ≥ max(A)`: `B(m)/m < 2·B(n)/n`.

A set `{a,b,c}` with `a < b < c` is *primitive* if no element divides another
(`a ∤ b`, `a ∤ c`, `b ∤ c`). Replacing `A` by its primitive core `P` leaves `B`
unchanged and has `max(P) ≤ max(A)`, so it suffices to prove (★) for primitive
`A` on the (wider) range `n ≥ max(P)`.

**Main Theorem (Theorem 9 below).** (★) holds for every finite set `A` whose
primitive core has at most three elements. In particular it holds for every
`A` with `|A| ≤ 3`.

Throughout, for a primitive triple `{a,b,c}` write

```text
S    = 1/a + 1/b + 1/c
s(n) = ⌊n/a⌋ + ⌊n/b⌋ + ⌊n/c⌋
P(n) = ⌊n/L_ab⌋ + ⌊n/L_ac⌋ + ⌊n/L_bc⌋,   L_xy = lcm(x,y).
```

Previously proved and used here:

* **Theorem 6 (reciprocal-sparse, proved earlier in `proof_attempt.md`).**
  If `P` is primitive with least element `a` and `Σ_{d∈P} 1/d ≤ 2/a`, then (★)
  holds for `P`. For a triple this hypothesis reads `1/b + 1/c ≤ 1/a`
  (the **covered zone**). Its proof is three lines: for `n ≥ max(P)`,
  `B(n) ≥ ⌊n/a⌋ + 1 > n/a` (primitivity supplies one counted integer that is
  not a multiple of `a`), while `B(m) ≤ m·Σ1/d ≤ 2m/a` for every `m`, so
  `B(m)/m ≤ 2/a < 2·B(n)/n`.

So only the **uncovered zone** `1/b + 1/c > 1/a` is at issue. (This forces
`b < 2a` and `c < ab/(b−a)`, but the proof below does not need those
consequences.) Everything below is new.

## 1. Elementary floor facts

**Lemma 1.**
Let `n ≥ 0`, `d, q, q' ≥ 1` be integers.

**(i)** `⌊n/(qd)⌋ = ⌊⌊n/d⌋ / q⌋`.

**(ii)** If `t ≥ 1` is an integer and `q ≥ 2`, `q' ≥ 3` (in either order), then
`t − ⌊t/q⌋ − ⌊t/q'⌋ ≥ 1`. The same holds a fortiori when `q, q' ≥ 3`.

*Proof.* (i) is the standard nested-floor identity `⌊⌊x⌋/q⌋ = ⌊x/q⌋`
(valid for real `x ≥ 0` and integer `q ≥ 1`) applied to `x = n/d`:
both sides count the multiples of `qd` in `[1,n]`.
Directly: writing `⌊n/d⌋ = qu + v`, `0 ≤ v < q`, one has
`n/(qd) ≥ (qu)/q = u` and `n/(qd) < (qu + v + 1)/q ≤ u + 1`.

(ii) `t − ⌊t/q⌋ − ⌊t/q'⌋ ≥ t(1 − 1/q − 1/q') ≥ t(1 − 1/2 − 1/3) = t/6 > 0`.
The left-hand side is an integer, hence `≥ 1`. ∎

**Lemma 2 (Bonferroni, three sets).** For any `n ≥ 0`,
`B(n) ≥ s(n) − P(n)`.

*Proof.* Count each `k ∈ [1,n]` on both sides. If `k` is divisible by exactly
`j ∈ {0,1,2,3}` of `a, b, c`, it contributes `1` (if `j ≥ 1`) or `0` to `B(n)`,
and exactly `j − C(j,2)` to `s(n) − P(n)` (a `k` divisible by exactly two of
them is divisible by exactly one pairwise lcm; a `k` divisible by all three is
divisible by all three pairwise lcms). Since `j − C(j,2) = 0, 1, 1, 0` for
`j = 0, 1, 2, 3`, every summand on the right is at most the one on the left. ∎

(At the density level, dividing by `n` and taking `n → ∞` gives the classical
**Heilbronn–Rohrbach inequality** `δ(B) ≥ Σ 1/d − Σ 1/lcm`. This lemma is its
finite-`n` form; the new step below is the *second* subtraction `s − 2P₂ ≥ 3`
extracted by charge integrality.)

## 2. Ratio bounds from primitivity

**Lemma 3.** Let `x < y` with `x ∤ y` and `y ∤ x` (automatic as `x < y`), and
`g = gcd(x,y)`. Then

```text
L_xy / x = y/g ≥ 3      and      L_xy / y = x/g ≥ 2.
```

*Proof.* `g` is a divisor of `y`, and `g ≤ x < y`, so `g ≠ y`. If `g = y/2`,
then `y/2 = g` divides `x` and `y/2 ≤ x < y`, forcing `x = y/2`, i.e. `x | y` —
contradiction. As `g` is a divisor of `y` different from `y` and `y/2`,
`g ≤ y/3`, so `y/g ≥ 3`. For the second bound, `g = x` would mean `x | y`;
hence `g ≤ x/2` and `x/g ≥ 2`. ∎

Applied to the three pairs of a primitive triple `a < b < c`:

```text
(R1) L_ab/a = b/gcd(a,b) ≥ 3        (R4) L_ab/b = a/gcd(a,b) ≥ 2
(R2) L_ac/a = c/gcd(a,c) ≥ 3        (R5) L_ac/c = a/gcd(a,c) ≥ 2
(R3) L_bc/b = c/gcd(b,c) ≥ 3        (R6) L_bc/c = b/gcd(b,c) ≥ 2
```

**Lemma 4 (the uncovered-zone dichotomy).** Let `{a,b,c}` be a primitive
triple with `1/b + 1/c > 1/a`. Then **not both** `L_ac/c = 2` and
`L_bc/c = 2`; i.e. at least one of the two ratios in (R5), (R6) is `≥ 3`.

*Proof.* Suppose `L_ac/c = a/gcd(a,c) = 2` and `L_bc/c = b/gcd(b,c) = 2`.
Then `gcd(a,c) = a/2` (so `a` is even and `a/2` divides `c`); write
`c = k·(a/2)`. Since `a ∤ c`, `k` is odd, and `c > a` gives `k ≥ 3`.
Likewise `c = l·(b/2)` with `l` odd, `l ≥ 3`. From `a < b`:
`k = 2c/a > 2c/b = l`, and both are odd, so `k ≥ l + 2`. Hence

```text
1/a = k/(2c) ≥ (l+2)/(2c) = l/(2c) + 2/(2c) = 1/b + 1/c,
```

contradicting `1/b + 1/c > 1/a`. ∎

*Remark.* Lemma 4 is where the covered/uncovered split earns its keep: the
boundary configurations (e.g. `{6,10,15}`, where `1/10 + 1/15 = 1/6` exactly)
have `L_ac/c = L_bc/c = 2` and satisfy `1/b + 1/c = 1/a`; they belong to the
covered zone and are handled by Theorem 6.

## 3. The charge decomposition

**Lemma 5.** Let `{a,b,c}` be a primitive triple with `1/b + 1/c > 1/a`.
Then for every integer `n ≥ c`,

```text
s(n) − 2·P(n) ≥ 3.
```

*Proof.* Put `t_a = ⌊n/a⌋`, `t_b = ⌊n/b⌋`, `t_c = ⌊n/c⌋`; all are `≥ 1`
because `n ≥ c > b > a`. Define

```text
X_a = t_a − ⌊n/L_ab⌋ − ⌊n/L_ac⌋
X_b = t_b − ⌊n/L_ab⌋ − ⌊n/L_bc⌋
X_c = t_c − ⌊n/L_ac⌋ − ⌊n/L_bc⌋.
```

Each pairwise lcm term appears in exactly the two `X`'s of its elements, so

```text
X_a + X_b + X_c = s(n) − 2·P(n).
```

By Lemma 1(i), `⌊n/L_ab⌋ = ⌊t_a/(L_ab/a)⌋ = ⌊t_b/(L_ab/b)⌋`, and similarly
for the other lcms. Hence:

* `X_a = t_a − ⌊t_a/(L_ab/a)⌋ − ⌊t_a/(L_ac/a)⌋` with both ratios `≥ 3`
  by (R1), (R2); so `X_a ≥ 1` by Lemma 1(ii).
* `X_b = t_b − ⌊t_b/(L_ab/b)⌋ − ⌊t_b/(L_bc/b)⌋` with ratios `≥ 2` (R4) and
  `≥ 3` (R3); so `X_b ≥ 1` by Lemma 1(ii).
* `X_c = t_c − ⌊t_c/(L_ac/c)⌋ − ⌊t_c/(L_bc/c)⌋` with ratios `≥ 2`, `≥ 2` by
  (R5), (R6), **and at least one `≥ 3` by Lemma 4** (this is the only use of
  the uncovered-zone hypothesis); so `X_c ≥ 1` by Lemma 1(ii).

Summing, `s(n) − 2P(n) = X_a + X_b + X_c ≥ 3`. ∎

## 4. The per-n criterion

**Theorem 8.** Let `{a,b,c}` be a primitive triple with `1/b + 1/c > 1/a`.
Then for every integer `n ≥ c`,

```text
2·B(n) > n·S.
```

*Proof.* Using `2⌊x⌋ = x + ⌊x⌋ − {x}` for each of the three floor terms,

```text
2·s(n) = n·S + s(n) − ({n/a} + {n/b} + {n/c}) > n·S + s(n) − 3,
```

since each fractional part is `< 1`. Combining with Lemma 2 and Lemma 5:

```text
2·B(n) ≥ 2·s(n) − 2·P(n) > n·S + (s(n) − 2·P(n)) − 3 ≥ n·S.       ∎
```

(All inequalities are exact rational statements; the middle one is strict.)

## 5. (★) for uncovered triples

**Corollary 8'.** Let `{a,b,c}` be a primitive triple with `1/b + 1/c > 1/a`.
Then for **all** integers `m ≥ 1` and `n ≥ c`,

```text
B(m)/m ≤ S < 2·B(n)/n.
```

In particular (★) holds for `{a,b,c}`, in the strong ordering-free form
`sup_{m≥1} B(m)/m < 2·inf_{n≥c} B(n)/n`.

*Proof.* `B(m) ≤ s(m) ≤ m·S` (union bound, `⌊x⌋ ≤ x`), and `S < 2·B(n)/n` is
Theorem 8. ∎

### 5A. The general charge-positivity criterion (any size)

The argument is not special to triples. For a finite primitive `P` and `e ∈ P`
define the **charge** `X_e(n) = ⌊n/e⌋ − Σ_{f∈P∖{e}} ⌊n/L_{ef}⌋`.

**Proposition 8''.** Let `P ⊂ {2,3,…}` be finite and primitive, `S = Σ_{d∈P}1/d`,
and suppose for every `e ∈ P`
```text
Σ_{f∈P∖{e}} gcd(e,f)/f < 1.        (charge-positivity)
```
Then `2B(n) > nS` for all `n ≥ max P`, hence `B(m)/m ≤ S < 2B(n)/n` for all
`m ≥ 1`, `n ≥ max P`.

*Proof.* `X_e(n) = t_e − Σ_{f≠e} ⌊t_e/(L_{ef}/e)⌋` (Lemma 1(i), `t_e=⌊n/e⌋≥1`),
and `L_{ef}/e = f/gcd(e,f)`, so `X_e(n) ≥ t_e(1 − Σ_{f≠e} gcd(e,f)/f) > 0`,
hence `≥ 1`. Each pairwise-lcm floor lies in exactly two charges, so
`Σ_e X_e = s(n) − 2P₂(n) ≥ |P|` (`P₂` = sum over all pairs). Bonferroni gives
`B(n) ≥ s(n) − P₂(n)`, and `2⌊x⌋ = x + ⌊x⌋ − {x}` (each `{n/d}<1`) gives
`2s(n) > nS + s(n) − |P|`; combine: `2B(n) ≥ 2s − 2P₂ > nS + (s−2P₂) − |P| ≥ nS`. ∎

For an uncovered triple, Lemma 4 is exactly what forces charge-positivity: the
three charge sums are `≤ 1/3+1/3`, `1/2+1/3`, and (by Lemma 4) `1/2+1/3`, all
`< 1`. So **Theorem 8 is the triple case of Proposition 8''**, and Corollary 8'
follows from it.

Proposition 8'' also proves (★) for many larger primitive sets — e.g. every
pairwise-coprime set the reciprocals of whose **three smallest elements** sum to
`< 1` (the binding case of the hypothesis is `e = max P`), such as `{2,5,7,9}` or
`{3,4,5,7}` (verified: all four charges `≥ 1` over a full period). NB the phrasing
"three smallest reciprocals" would be wrong — `{2,3,5,7}` has `1/3+1/5+1/7 < 1`
yet fails the hypothesis at `e=7` (`1/2+1/3+1/5 > 1`).
It does **not** close `|P|=4`: for a clustered set the largest element collects
weak-side ratios summing to `≥ 1/2+1/2 = 1` (e.g. `{2,3,5,7}`: charge sum for `7`
is `1/2+1/3+1/5 > 1`), and no size-4 analogue of Lemma 4 rescues the boundary —
the natural conjecture "charge-sum `= 1` ⇒ covered zone" is **false**
(`{6,10,15,25}`: charge sum for `25` is `1`, yet `1/10+1/15+1/25 = 0.207 > 1/6`;
37 of 49 boundary quadruples with `a ≤ 25` violate it). See §7.

## 6. All triples; all `A` with a small core

**Theorem 9.** (★) holds for every finite set `A` of integers `≥ 2` whose
primitive core `P` has `|P| ≤ 3`. In particular (★) holds whenever `|A| ≤ 3`.

*Proof.* `B_A = B_P` and `max(P) ≤ max(A)`, so it suffices to prove the
inequality for `P` for all `m > n ≥ max(P)`.

* `|P| = 1`: Proposition 1 (proved earlier; sharp constant `2 − 1/a`).
* `|P| = 2`, `P = {a,b}`: `1/a + 1/b < 2/a`, so Theorem 6 applies.
* `|P| = 3`, `P = {a,b,c}`: if `1/b + 1/c ≤ 1/a`, Theorem 6 applies;
  otherwise Corollary 8' applies. ∎

This subsumes all earlier partial triple results: the case `2 ∈ A`, the
`min = 3` triples (Theorem 7's five exceptional certificates `{3,4,5}`,
`{3,4,7}`, `{3,4,10}`, `{3,4,11}`, `{3,5,7}` are no longer needed — they all
satisfy `1/b + 1/c > 1/a` and fall to Corollary 8'), and the originally
targeted range `4 ≤ a < b < c`.

## 7. Sharpness and what remains open

* The constant `2` is sharp already for singleton cores (`A = {a}`,
  `n = 2a−1`, `m = 2a`, ratio `2 − 1/a`). It is **not** unique to singletons as
  an asymptotic direction: fixed-length consecutive primitive runs such as
  `{a,a+1,a+2}` also have beta/alpha ratios tending to `2` (for example
  `{101,102,103}` has `beta/alpha = 20100/10201 ≈ 1.9704`). For triples the
  proof above gives a quantitative gap for each fixed set: in the uncovered zone
  the proof of Theorem 8 yields
  `2·B(n)/n − S ≥ [(s(n) − 2P(n) − 3) + (3 − {n/a} − {n/b} − {n/c})]/n > 0`
  (first bracket `≥ 0` by Lemma 5, second `> 0`); in the covered zone
  Theorem 6 gives `2·B(n)/n > 2/a ≥ S ≥ B(m)/m`.
* **Open:** primitive cores with `|P| ≥ 4`. The natural extension of Lemma 5
  breaks: with four elements each `X_x` carries **three** lcm charges, and
  `t − ⌊t/q₁⌋ − ⌊t/q₂⌋ − ⌊t/q₃⌋` need not be positive when the guaranteed
  ratios are only `(2,3,3)` (`1/2 + 1/3 + 1/3 > 1`); moreover Bonferroni
  truncated at pairs discards the positive triple terms, and the required
  slack grows to `s(n) − 2P(n) ≥ 4` against a fractional loss of `4`. A
  four-element analogue would need either triple-term bookkeeping or a
  different charging scheme.
* Empirically the per-`n` criterion persists for **quadruples**: a probe over
  all 8 836 uncovered (`Σ1/d > 2/min`) primitive quadruples with elements
  `≤ 30` and `lcm ≤ 3·10⁶`, over a full period each, found **no** failure of
  `2B(n) > nS` for `n ≥ max(P)`; an independent sweep (`sweep_criterion.py`)
  confirms this for all 42 769 primitive 4-sets with elements in `{3..40}`.
* **CORRECTION (2026-07-07 adversarial audit): the general conjecture
  "`2B(n) > nS` for all `n ≥ max(P)`, every primitive `P`" is FALSE.**
  Explicit counterexample family: `A = {2p : p prime ≤ P₀}` (primitive, since
  `2p | 2q ⇔ p | q`). Here `S = ½·Σ_{p≤P₀} 1/p → ∞` while
  `δ = ½·(1 − ∏_{p≤P₀}(1−1/p)) < ½`, so `S > 2δ` once `P₀ ≥ 100`
  (at `P₀ = 100`: `|A| = 25`, `S = 0.9014 > 2δ = 0.8797`). Verified
  computationally for `P₀ = 300` (`|A| = 62`, `max A = 586`): `2B(n) ≤ nS`
  fails at **every** `n ∈ [586, 2·10⁶]`. Note (★) itself still holds for
  these `A` — all multiples are even, so `sup_x B(x)/x ≤ 1/2 < 2δ ≈ 0.90` —
  via a *third* mechanism (a shared-factor bound: `B_{2A'}(x) = B_{A'}(⌊x/2⌋)`,
  a scaling recursion). Moral for `|P| ≥ 4`: a full proof will need at least
  three regimes (union-bound criterion, dense half, shared-factor/recursive
  structure), not a single per-`n` criterion. Only small `|P|` can hope for
  the criterion to be universal; it IS universal for `|P| ≤ 3` (Theorem 8 +
  the covered zone, where Theorem 6's proof in fact also gives
  `2B(n) > 2n/a ≥ nS`).

## 8. Computational verification (`attack_triples.py`)

All checks use exact integer/rational arithmetic (no floating point in any
assertion). All pass:

* **Part A (main).** For **every** primitive triple with `2 ≤ a ≤ 25` in the
  uncovered zone `1/b + 1/c > 1/a` (14 802 triples: 14 796 with `a ≥ 4`, five
  with `a = 3`, one with `a = 2`), and **every** `n` in the full period
  `c ≤ n < c + lcm(a,b,c)`: Lemmas R1–R7, the nested-floor identities, `X_a,
  X_b, X_c ≥ 1`, `s(n) − 2P(n) ≥ 3`, Bonferroni, and the strict per-`n`
  criterion `2B(n) > nS`; plus the union bound `B(m) ≤ mS` over a full period.
  The one-period check covers all `n ≥ c`: writing `n = n₀ + kL` with
  `n₀ ∈ [c, c+L)`, `k ≥ 0`, periodicity gives `B(n) = B(n₀) + k·B(L)`, and
  `2B(L) > LS` is itself among the verified checks (since `L ≥ 2c > c`, the
  point `n = L` lies in the verified range), so
  `2B(n) = 2B(n₀) + 2k·B(L) > n₀·S + kL·S = n·S`.
* **Part B.** Ratio Lemma 3 (R1–R6) on all 37 253 817 primitive triples with
  `a ≤ 25`, `c ≤ 2000` (both zones), and R7 on the uncovered ones.
* **Part C.** End-to-end (★): `B(m)·n < 2·B(n)·m` directly for all uncovered
  primitive triples with `a ≤ 8`, all `n ∈ [c, c+L)`, all `m ∈ (n, c+3L]`
  (1 209 671 136 pairs `(n,m)`).
* **Part D.** Discovery sweep (historical): the per-`n` criterion on the
  finite window `[c, 6ac/(c−a))` for all 156 263 uncovered triples with
  `4 ≤ a ≤ 60` and `c < 7a`: no failures. (The window form was the original
  attack plan; the final proof does not need the window at all.)
* **Part E.** Brute-force unit tests of the abstract lemmas, independent of
  the triple enumeration: Lemma 1(i) (`n ≤ 3000`, `d,q < 25`), Lemma 1(ii)
  (`t ≤ 1000`, `q < 40`, `q' < 40`), and the abstract form of Lemma 4
  (all `a < b < c ≤ 2000` with `a/gcd(a,c) = b/gcd(b,c) = 2`: 13 336
  configurations, every one satisfies `1/b + 1/c ≤ 1/a`).

### Proof-status ledger

| Claim | Status |
|---|---|
| Lemmas 1–5, Theorem 8, Corollary 8', Theorem 9 | **Proved** (full proofs above) |
| Theorem 6, Proposition 1 (cited) | Proved earlier (`proof_attempt.md`) |
| `|P| ≥ 4` | **Open** |

Nothing in this note is conjectural. (The result equals Chojecki's claimed
Cor 4.7 and the method's backbone is the classical Heilbronn–Rohrbach inequality —
see the priority note at the top; the contribution is a correct, elementary,
sorry-free-formalizable proof, not a new theorem or a new method.)
