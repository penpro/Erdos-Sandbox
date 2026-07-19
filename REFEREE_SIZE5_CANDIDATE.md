# Referee checklist: size-5 candidate closure for Erdos #488

Date: 2026-07-18

Status: `PLAUSIBLE` end-to-end assembly, with `PROVED` paper/Lean components and
`COMPUTED` exact certificates. This document does **not** claim that size 5 or
Erdos #488 is solved. Promote only after the proof and code attacks below pass.

Internal audit state: Claude independently marked attacks 1, 2, 4, and 5 PASS.
Codex's primary code knife marks attack 3 SOUND under the stated drift
dependencies (`REFEREE_V3_CODEX.md`) and the joint seam pass marks attack 6
HOLDS (`REFEREE_SIZE5_ASSEMBLY_CODEX.md`). Independent external review remains
required before promotion.

## 1. Target and reductions

For a primitive antichain quintuple `P`, put

```text
B_P(n) = #{k<=n : some p in P divides k},
S_P = sum_{p in P} 1/p.
```

The size-5 separator needed by #488 is

```text
2 B_P(n) > n S_P  for every n >= max(P).
```

The current regime assembly is:

1. At least three good charges: sorry-free Lean theorem.
2. First doubling `max(P)<=n<2max(P)`: size-4 separator plus the new maximum.
3. Bridge `7nS>1135-157S`: U2 drift theorem.
4. Nonprimitive scaling: tower form for the primitive base.
5. At most two good charges and `CRIT>7/2`: C-B covering theorem.
6. `max(P)/min(P)>=7`: SPREAD certificate.
7. What remains is the compact primitive C-B residual.

W-FIN and its residual refinement prove this residual finite at paper tier; the
edge-count reductions below are intended to replace its impractical numerical
cutoff by complete finite structural banks.

## 2. Compact residual partition

Dualize with `D={lcm(P)/p : p in P}`. A dual vertex `d_i` is self-bad when

```text
sum_{j!=i} gcd(d_i,d_j) >= d_i.
```

A strong edge satisfies

```text
4*gcd(d_i,d_j) >= min(d_i,d_j).
```

The minimum-good lemma excludes five self-bad vertices. The proposed complete
partition is:

| Sector | Structural inventory | Exact certificate | Current tier |
|---|---|---|---|
| 3 bad, at least 2 internal strong edges | 906 normalized triples | `shape2v3`: 906/906, 869 vacuous | `COMPUTED`, v3 knife needed |
| 3 bad, exactly 1 internal strong edge | corrected finite two-block box, 19 residuals | direct tower bank: 19/19 | `COMPUTED`, parametrization audit needed |
| 3 bad, 0 internal strong edges | finite anchored rational templates, 4 residuals | direct tower bank: 4/4; v3: 4/4 | `COMPUTED`, surjectivity audit needed |
| 4 bad | 174 necessary-filter shapes | `shape4`: 174/174, 164 vacuous | `COMPUTED`, inventory/shape4 knife needed |
| 5 bad | impossible by minimum-good lemma | paper proof | `PROVED` at paper tier |

## 3. Repaired overclaims

Do not restore any of these claims:

- The old G3/min-54 bound is false.
- The 69 all-internal-owner triples do not cover the three-bad sector.
- The 906 triples cover only bad triples with at least two internal strong edges.
- The initial shared `census bank1edge` scale proof is false: it used `1/k`
  where the self-charge is `1/c`, included three noncompact tuples, and omitted
  the compact residual `D=[30,52,78,130,195]`.
- The zero-edge class is not empty. It has four survivors in the corrected
  rational-template bank; the first is dual to primal `{2,3,5,7,11}`.

## 4. Proof attacks required

1. Prove the one-edge parametrization is surjective. In particular, prove the
   normalized isolated block has gcd one, hence primitive `D` gives `gcd(u,v)=1`,
   and rederive both corrected CROSS scale bounds without swapping `u` and `v`.
2. Prove the zero-edge anchored-rational parametrization is surjective for any
   choice of the first good. Check the divisor jump, `c_i<=10`, ratio bounds,
   rational normalization, and the selection of three distinct bad ratios.
3. Audit `shape2v3`: class partition, BIG representatives, forced-slot clamp,
   q ranges, nonmonotone `J` interval, tau range, and every vacuity exclusion.
4. Audit the four-bad cutoff-free inventory (`fourbadcheck` and Section 23.7)
   and the analogous `shape4` surfaces.
5. Audit the final bad-count exhaustiveness and verify every compact residual
   enters exactly one row of the table.
6. Recheck the regime seams: FD below, U2 above, C0 scaling, C-B and SPREAD.

## 5. Tower handoff

The direct banks check `2B(m)>(m+1)S` while `7(m+1)S<1135`. On the complement,
U2 gives

```text
2B(m)-mS >= (7mS-1135+157S)/150 >= S.
```

The code cap `floor(1135/(7S))-1` is exact for a nonintegral quotient and checks
one extra endpoint for an integral quotient. Tower form then handles every gcd
scaling because `n/t<floor(n/t)+1`.

## 6. Exact commands

```powershell
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path clustercheck\Cargo.toml --target-dir C:\tmp\ep488-clustercheck-target
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape2v3 clustercheck\shapes906.csv 7
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path oneedgebankcheck\Cargo.toml --target-dir C:\tmp\ep488-oneedgebankcheck-target
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path zeroedgebankcheck\Cargo.toml --target-dir C:\tmp\ep488-zeroedgebankcheck-target
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape2v3 zeroedgebankcheck\shapes0edge.csv 7
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path fourbadcheck\Cargo.toml --target-dir C:\tmp\ep488-fourbadcheck-target
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape4 census\shapes4inv120.csv 7
```

## 7. Promotion gate

Only after two independent hostile proof/code passes should the project consider
upgrading the size-5 statement from `PLAUSIBLE` to `PROVED`. Novelty and
publishability are separate questions and still require a literature check.
