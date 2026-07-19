# External hostile-review package: the shape2v3 / shape4 certificates (referee attack 3)

Self-contained brief for an INDEPENDENT reviewer (human or AI) with no access
to this project's history. Your job is to BREAK the certificate design below,
or fail to. You are not asked to trust anything; every claim has a
reproduction command. The authors want refutations, not endorsements.

Context guard: this is one component of a larger campaign on Erdős problem
#488 (size-5 case). Nothing here claims #488 or its size-5 case is solved.
The specific question is whether two exact-arithmetic certificate programs are
SOUND — i.e., whether "PASS/VACUOUS" outputs really imply the mathematical
statements claimed.

## 1. The mathematical setting (all you need)

Fix a quintuple of distinct positive integers P = {p1..p5} forming an
antichain under divisibility. For an element e, define its charge

```text
charge(e) = sum over f != e of gcd(e,f)/f.
```

Call e BAD if charge(e) >= 1, GOOD otherwise. Facts you may assume (proved
elsewhere in the project, not under review here):

- F1. In the configurations under review there are EXACTLY 3 bads and 2 goods
  (the "3-bad sector"; a separate run covers 4 bads + 1 good with the same
  machinery, `shape4`).
- F2. All five elements satisfy max(P)/min(P) < 7.
- F3. The 3 bads have the form w1*s, w2*s, w3*s for a COMMON positive integer
  scale s, where (w1,w2,w3) is one of finitely many known "shapes" (a CSV
  input; its derivation is not under review). The 2 goods are arbitrary
  positive integers subject only to antichain + goodness + F2.
- F4 (drift machinery, certified elsewhere): for a "row" with moduli multiset
  M = {m1..m4} (integers >= 2), the exact function f_M(J) (implemented as
  `f_exact`, returning 60*f) measures a certified drift; the target inequality
  for a configuration at scale position tau is

      2*sum over the 5 rows of f(J_row) - 5 + S >= 0,   S > 0,

  where J_row = floor(tau / coefficient). The certificate must show the
  margin m60 = sum 2*f*60 - 300 is > 0 (or >= 0, since +S > 0) for all tau in
  [2*wmax, 33*7*wmax]. Rows of BAD elements must have moduli consistent with
  badness (sum of reciprocals of the 4 moduli >= 1); rows of GOOD elements
  the reverse (< 1). A good row's drift is also floored by the certified
  staircase stair60: 30/50/70/90 at J >= 2/6/12/15.
- F5 (tail): for J > 40, a bad row's drift is >= (7/300)J - 7/30 and a good
  row's is >= 3/2 (so 90 in x60 units).

The MODULUS an element f presents in e's row is f/gcd(e,f); e's charge is the
sum of reciprocals of the four moduli it receives. For the bads, the moduli
from the other two bads are fixed by the shape ("pins": w_j/gcd(w_i,w_j));
the moduli from the two goods are unknown integers >= 2.

## 2. The certificate design under review

`census/src/main.rs`, functions `shape2v3` (3-bad) and `shape4` (4-bad), plus
the shared helper `f_exact` and `stair60`. Roughly 200 lines each, pure
integer arithmetic, no dependencies.

Core design (shape2v3): partition ALL configurations by the CLASS MATRIX —
for each (bad row i, good g), the slot value (the modulus good g presents in
row i) is declared either an exact value v in {2,3,4,5,6} or BIG (>= 7).

Key mechanism (the part most worth attacking): if a good y presents modulus
v in row i, then with q := p_i/gcd(y, p_i),

```text
y = v * p_i / q,   gcd(v, q) = 1,   q >= 2,
q*wmax < v*7*w_i   and   q*7*wmin > v*w_i      (from F2, strict),
```

and ALL of y's gcds against the other bads are s-free template constants:
with g_j = gcd(v*w_i, q*w_j),

```text
y's modulus in bad row j     = v*w_i/g_j,
row-y's modulus from bad p_j = q*w_j/g_j,
```

via the identity gcd(A/q, B) = gcd(A, qB)/q for q | A. If both goods carry
exact slots, their mutual moduli are exact too (identity
gcd(A/q, B/r) = gcd(Ar, Bq)/(qr)). The certificate enumerates all class
matrices, all q values in range, forces all implied moduli, and kills branches
whose forced values contradict (a) the declared classes, (b) the antichain
(modulus 1), (c) the pinned good's own goodness (exact reciprocal sum >= 1),
or (d) some bad row's badness. Surviving branches get exact margin scans over
tau. "VACUOUS" for a shape means every branch died: the claim is that NO
3-bad configuration with that shape exists (within F1-F3's model).

## 3. What to attack (the authors' own list, plus anything else)

1. Partition completeness: does every true configuration land in exactly one
   (class matrix, q assignment) branch, with all exclusion tests implied by
   true-configuration axioms? Check especially: the q-range derivations; the
   consistency requirement "forced slot == declared class"; the treatment of
   the pinned recipient's own row.
2. BIG-class row-table representatives: for the row minimum at entry J = j,
   the representatives are m in [7, j+1], PLUS m = j+1 when j < 6, on the
   argument that any modulus > j has no divisibility events on [1, j] and so
   has identical f-prefix. Is the badness test at the representative
   (conservative inclusion) handled soundly in BOTH directions?
3. Forced-slot clamping at 41 = JT+1: exactness of the tail representative
   for J <= 40; the badness test at the clamped value.
4. The pinned good's own drift row: 4 known moduli (or 3 + a minimized free
   slot with an exact goodness feasibility test, where the free slot's value
   41 stands for the infinite tail and its goodness term is dropped — is that
   sound?), evaluated at J in [q*tau/(v*w_i), q*(tau+1)/(v*w_i)] and MINIMIZED
   over that interval on the stated ground that f is not monotone in J. Is
   the interval right? Is min the right operation? Is the stair60 max sound?
   IMPORTANT evaluation split (spelled out after an earlier reviewer read the
   brief as evaluating the exact row at all J): the exact row f-array is
   computed only for J <= 40 and is consulted ONLY when the evaluated index
   jy <= 40 (`if jy <= jt { max(exact, stair60) } else { 90 }` at all three
   sites); for jy >= 41 the code uses the flat certified good-row floor 90
   (F5) and never the 41-clamped exact prefix. The 41-representative is
   therefore only ever used where it is exact (J <= 40, no multiple of 41 in
   range). Attack the split itself if you can.
5. The tau loop: integer tau with J = floor(tau/w) — check the floor-identity
   argument (floor(floor(x)/n) = floor(x/n)) wherever exact J's are needed,
   and inequality direction wherever floored J's are used with monotone floors.
6. The assembly: margin m60 = 2*(goods) + 2*(bads) - 300, PASS iff > 0 for
   all tau in [2*wmax, 231*wmax]; ZERO (== 0) passes via the retained +S > 0.
7. shape4 (4 bads, ONE good): same machinery with a 4x1 class matrix; the
   pinned good's row has NO free slot. Check the analogous surfaces, and the
   all-BIG column's coverage of arbitrarily large goods.
8. Arithmetic: i128 overflow anywhere? (Moduli clamped at 41; pins bounded by
   the shapes; check the products.)

## 4. Reproduction

Rust (any recent toolchain; the project uses GNU on Windows):

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-census-target'
cargo run --release --manifest-path census\Cargo.toml -- shape2v3 clustercheck\shapes906.csv 7
cargo run --release --manifest-path census\Cargo.toml -- shape2v3 zeroedgebankcheck\shapes0edge.csv 7
cargo run --release --manifest-path census\Cargo.toml -- shape4 census\shapes4inv120.csv 7
```

Expected: `PASS 906 (incl. 869 VACUOUS) / ZERO 0 / SHORT 0`;
`PASS 4 / ZERO 0 / SHORT 0`; `PASS 174 (incl. 164 VACUOUS) / ZERO 0 / SHORT 0`.

## 5. Verdict format

For each numbered attack surface: BREAK (with a concrete counterexample
configuration or a specific unsound step) or HOLDS (with the one-sentence
reason). Then an overall verdict: SOUND / UNSOUND / SOUND-WITH-REPAIRS.
Partial credit for narrowing: "surface 4's interval is right but the min
should also include jhi+1 when ..." is exactly the kind of finding wanted.
