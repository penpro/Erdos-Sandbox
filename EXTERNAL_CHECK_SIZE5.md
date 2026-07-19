# External cross-confirmation brief: the full size-5 assembly (Erdős #488, |core| ≤ 5)

You are an INDEPENDENT hostile reviewer. Your job is to BREAK this proof
assembly or fail to. Do not trust the authors; every claim below carries a
file pointer or a reproduction command. Refutations with concrete line
references are worth far more than endorsements.

Repository (public): https://github.com/penpro/Erdos-Sandbox — branch `main`.
All paths below are repo-relative. If you can browse but not execute, work in
READING MODE (section 6); if you can execute Rust/Lean, also run EXECUTION
MODE (section 5).

## 0. Scope guard — what is and is not claimed

- CLAIMED (status `PLAUSIBLE`, promotion gated on reviews like yours): for
  every finite set of integers ≥ 2 whose primitive core has size ≤ 5, the
  separator `2·B_P(n) > n·S_P` holds for all n ≥ max(P), which implies
  Erdős #488's inequality for those sets.
- NOT claimed: that #488 is solved (it is open; larger cores remain), that
  anything here is novel (no literature check has been done), or that the
  certificate programs are formally verified (they are exact-arithmetic Rust,
  cross-implemented twice and audited, but not machine-checked).
- Two prior cold reviews (no source attached) confirmed the certificate
  DESIGN 7/8 and ~6/8 surfaces; each claimed break was refuted by source
  inspection (e.g. an alleged 41-clamp misuse that the guard
  `if jy <= jt {..} else { 90 }` at `census/src/main.rs` prevents). Lesson:
  READ THE SOURCE before claiming an evaluation-semantics break.

## 1. Definitions

For a finite set P of integers ≥ 2: `B_P(n) = #{k ≤ n : some p ∈ P divides k}`,
`S_P = Σ_{p∈P} 1/p`. The primitive core is the set of divisibility-minimal
elements (an antichain); #488 for A reduces to its core (Lean:
`lean/ep488/Ep488/Reduction.lean`). The separator `2B(n) > nS` for all
n ≥ max(P) implies `n·B(m) < 2·m·B(n)` for m > n ≥ max(P) via the union bound
`B(m) ≤ mS` (Lean: same file; also `REFEREE_SIZE5_ASSEMBLY_CODEX.md` §1).

For an element e ∈ P: `charge(e) = Σ_{f≠e} gcd(e,f)/f`; e is BAD if
charge ≥ 1. Dual: `D = {lcm(P)/p}`; dual self-bad (Σ gcd(d_i,d_j) ≥ d_i)
equals primal bad — machine-checked (`lean/ep488/Ep488/Transport.lean`,
`dual_selfbad_iff`).

## 2. The master documents

1. `REFEREE_SIZE5_CANDIDATE.md` — the assembly checklist (regimes, partition
   table, proof attacks, promotion gate).
2. `REFEREE_SIZE5_ASSEMBLY_CODEX.md` — seam audit (verdict: no uncovered seam).
3. `REFEREE_V3_CODEX.md` — source-level audit of the certificate programs
   (verdict: sound; one cleanup, since applied).
4. `EXTERNAL_CHECK_V3.md` — the certificate-design attack surfaces (amended
   after the cold rounds; includes the canonical pin rule, the goodness
   direction policy, the all-BIG branch, the evaluation split).
5. `cbfin_reduction_notes.md` §22–§27 — derivations, corrections (kept
   honestly: §22.4, §25.1), audits (§26–26.3), seams (§27).
6. `census/CERTIFICATES.txt` — the committed certificate outputs.

## 3. The n-axis regime tree (per quintuple)

For a primitive antichain quintuple P and n ≥ max(P), FIRST MATCHING regime:

| Regime | Statement | Tier | Where |
|---|---|---|---|
| A | ≥3 good charges ⟹ separator, all n | LEAN | `Ep488/Quint.lean` (`ep488_quint_three_good`) |
| FD | max ≤ n < 2max, unconditional | LEAN+paper | `Ep488/Quad.lean` (size-4 separator) + notes |
| Bridge | 7nS > 1135 − 157S (incl. n ≥ 33max) | LEAN algebra + Rust kernel | `Ep488/DriftBridge.lean` (conditional algebra) + `census` `drift` certificate (U2 kernel) |
| C0 | gcd(P) > 1: scaling recursion + tower form | paper + Lean seam | `DriftBridge.lean` (`drift_bridge_tower`), notes |
| C-B | ≤2 good and CRIT > 7/2 | LEAN | `Ep488/CB.lean` (`cb_cover5`) |
| SPREAD | max/min ≥ 7 | paper + certificates | notes §14, `spreadcheck/`, `census/CERTIFICATES.txt` |
| box | the compact residual | certificates (below) | — |

Seam statements: `REFEREE_SIZE5_ASSEMBLY_CODEX.md` §2/§5 and notes §27
(overlaps at both ends; the tower cap ↔ bridge handoff; strict/nonstrict
boundary complementarity).

## 4. The compact-box partition (the former open region)

Box: ≤2 good, CRIT ≤ 7/2, ratio < 7, window-relevant. Bad count is 3 or 4
(5 is impossible — LEAN: `Ep488/Ceiling.lean`, `no_five_self_bad`). Partition
by the bad-triple's internal strong edges (4·gcd ≥ min):

| Sector | Inventory (complete by) | Certificate | Expected result |
|---|---|---|---|
| 3-bad, ≥2 edges | 906 min-strong triples (`clustercheck/`, proved cap a < 112) | `census shape2v3` | PASS 906 (869 VACUOUS) / 0 / 0 |
| 3-bad, 1 edge | two-block box, corrected caps (notes §25.1, `oneedgebankcheck/README.md`) | direct tower bank ×2 implementations | 19 members, 0 tower failures |
| 3-bad, 0 edges | anchored rational templates (`zeroedgebankcheck/README.md`) | direct bank + `shape2v3` | 4 members (first = dual of {2,3,5,7,11}), 0 failures |
| 4-bad | 174 necessary-filter shapes, THREE independent completeness routes (`census shapes4inv`/`shapes4inv2`, `fourbadcheck/`) | `census shape4` | PASS 174 (164 VACUOUS) / 0 / 0 |
| 5-bad | impossible | Lean | — |

## 5. EXECUTION MODE (if you can run code)

Rust (any recent toolchain; repo uses GNU on Windows):

```
cargo run --release --manifest-path census/Cargo.toml -- shape2v3 clustercheck/shapes906.csv 7
cargo run --release --manifest-path census/Cargo.toml -- shape2v3 zeroedgebankcheck/shapes0edge.csv 7
cargo run --release --manifest-path census/Cargo.toml -- shape4 census/shapes4inv120.csv 7
cargo run --release --manifest-path census/Cargo.toml -- bank1edge 7
cargo run --release --manifest-path oneedgebankcheck/Cargo.toml
cargo run --release --manifest-path zeroedgebankcheck/Cargo.toml
cargo run --release --manifest-path fourbadcheck/Cargo.toml
cargo run --release --manifest-path badtriplecheck/Cargo.toml -- 120 clustercheck/shapes906.csv
cargo run --release --manifest-path clustercheck/Cargo.toml
```

Expected headlines: 906/906 (869 vacuous); 4/4; 174/174 (164 vacuous);
19 members 0 failures (both one-edge banks, identical sets); 4 members
0 failures; fourbadcheck ALL PASS (connected 172 + two-pair 2, both boxes
exact vs canonical); badtriplecheck ALL PASS ([0,13,57,118] histogram at
M=120, ≥2-edge coverage 175/175); clustercheck asserts its CSVs.

Lean (elan + Lake; Mathlib cache recommended):

```
cd lean/ep488 && lake build
lake env lean Ep488/CeilingCheck.lean
lake env lean Ep488/TransportCheck.lean
lake env lean Ep488/DriftBridgeCheck.lean
lake env lean Ep488/QuadCheck.lean Ep488/QuintCheck.lean Ep488/CBCheck.lean
```

Every `#print axioms` line must list only
`[propext, Classical.choice, Quot.sound]` (some fewer). Any `sorryAx` = BREAK.

## 6. READING MODE (if you can only browse)

Verify, with line references:
1. Partition totality: every compact residual has bad count 3 or 4 and falls
   in exactly one sector row (Ceiling.lean + the edge-count trichotomy).
2. Seams: the four handoffs in notes §27 / assembly referee §2,§5 — check the
   inequalities mesh with no gap at boundaries (strict vs nonstrict).
3. Inventory completeness arguments: (a) 906 = all min-strong triples under
   the proved cap (`clustercheck/README.md`); (b) one-edge: the §25.1
   corrected caps and that `oneedgebankcheck` implements exactly them;
   (c) zero-edge surjectivity (`zeroedgebankcheck/README.md`: both pins have
   c ≤ 10; anchoring argument); (d) 4-bad: the ½-filter necessity and the two
   independent completeness proofs (heavy-graph cases; spanning-tree ratio
   box in `fourbadcheck/README.md`).
4. Certificate soundness: the surfaces in `EXTERNAL_CHECK_V3.md` §3 items
   1–9, against `census/src/main.rs` (`shape2v3`, `shape4`, `f_exact`,
   `stair60`, `cprod`). Specifically re-derive: the q-range bounds; the
   forced-slot identities; the goodness tests using EXACT (unclamped) values;
   the `jy ≤ jt` evaluation split; checked arithmetic + input bound asserts.
5. The committed outputs in `census/CERTIFICATES.txt` match the code's
   claimed semantics (spot-check several).

## 7. Honest dependency ledger (do NOT report these as hidden gaps)

- E4 kernel (157/300) enters the density theorem as an explicit HYPOTHESIS in
  Lean (`Density.lean`) — by design decision; its proof is paper + exhaustive
  computation outside Lean.
- The U2 finite drift kernel and staircase are Rust exact certificates
  (`census drift`, `spreadcheck/`, `goodpincheck/`) + paper; `DriftBridge.lean`
  machine-checks only the algebra above them.
- W-FIN (residual finiteness) is paper-tier, jointly hostile-reviewed
  (`REFEREE_WFIN.md`); it motivates the box but the sector certificates do
  not depend on its numeric cutoff.
- SPREAD is paper + certificates, not Lean.
- Novelty/publishability: explicitly unassessed.

## 8. Verdict format

For each: (1) regime tree & seams; (2) partition totality; (3) each of the
five sector rows (inventory completeness AND certificate soundness
separately); (4) Lean claims (axioms clean, statements match prose);
(5) arithmetic safety — give BREAK (concrete counterexample, config, or line)
or HOLDS (one-sentence reason). Then an overall verdict:
SOUND / SOUND-WITH-REPAIRS (list them) / UNSOUND (the break). Note anything
you could not check and why.
