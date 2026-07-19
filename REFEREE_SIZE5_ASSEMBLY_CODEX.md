# Codex joint seam audit: size-5 candidate assembly

Date: 2026-07-18

Verdict: **NO UNCOVERED REGIME SEAM FOUND.** This upgrades referee attack 6 to
`HOLDS` at paper-audit tier, conditional on the stated component theorems and
certificate verdicts. It is not by itself a novelty or publication verdict.

## 1. From the separator to Erdos #488

The union bound gives `B_P(m)<=mS_P`. Therefore

```text
2B_P(n)>nS_P  =>  nB_P(m)<2mB_P(n)
```

for every `m>n>=max(P)`. Divisibility-redundant elements are removed first.

## 2. n-range tiling

For a primitive quintuple base:

- `max(P)<=n<2max(P)`: FD, using the size-4 separator.
- `n>=2max(P)` and `7nS>1135-157S`: U2 bridge.
- `n>=2max(P)` below the bridge: the C window handled below.

The v3/shape4 tau scans begin exactly at the FD endpoint. Their inclusive upper
bound `33*7*wmax` is conservative because every nonbridge configuration has
`n<33max(P)` and compact spread gives `max(P)<7s*wmax`.

## 3. Structural tiling in the C window

After the at-least-three-good Lean branch, the remaining core has at most two
good charges, hence at least three self-bad dual vertices.

- `CRIT>7/2`: C-B covering theorem.
- `CRIT<=7/2` and `max/min>=7`: SPREAD.
- `CRIT<=7/2` and `max/min<7`: compact residual.

The inequalities use complementary strict/nonstrict boundaries, so no equality
case is lost.

The minimum-good lemma gives at most four self-bad vertices. Thus the compact
bad-count partition is exactly 3 or 4:

- 3 bad, induced edge count 2 or 3: complete 906 inventory and v3.
- 3 bad, induced edge count 1: exact compact 19-bank.
- 3 bad, induced edge count 0: exact rational-template 4-bank.
- 4 bad: complete 174-shape inventory and shape4.
- 5 bad: impossible.

The induced bad-triple graph has exactly 0, 1, 2, or 3 edges, so the three-bad
rows are mutually exhaustive and disjoint.

## 4. Scaling and tower endpoint

For `P=tP0`,

```text
B_(tP0)(n)=B_P0(floor(n/t)).
```

The direct banks check tower form while `7(m+1)S0<1135`. On the complement,
U2 gives

```text
2B(m)-mS >= (7mS-1135+157S)/150 >= S,
```

hence the same tower form. The integer cap checks one harmless extra endpoint
when `1135/(7S)` is integral. Finally,
`n/t<floor(n/t)+1` turns nonstrict tower form into the strict scaled separator.

## 5. Dependency ledger

The assembly is valid if all of the following hold at their stated tiers:

1. Size-4 separator and three-good size-5 theorem.
2. U2 bridge and tower interpretation.
3. C-B covering theorem, SPREAD, and minimum-good lemma.
4. 906, 19, 4, and 174 inventory surjectivity results.
5. v3/shape4 and direct-bank certificate soundness.

Codex's audits currently mark the 19/4 reductions, tower seam, v3/shape4 code,
and regime tiling as holding; Claude independently reproduced attacks 1/2/4/5.
W-FIN is no longer needed to enumerate the compact bank once the structural
partition is accepted, but remains an independent finiteness cross-check.

## 6. Promotion status

The remaining promotion gate is independent confirmation of the v3/shape4
audit (the package `EXTERNAL_CHECK_V3.md`) and the user's external W-FIN review,
followed by one final proof-text consolidation. Do not call the size-5 case
solved or novel before those reviews are recorded.
