# Codex hostile audit: shape2v3 and shape4

Date: 2026-07-18

Verdict: **SOUND under F1-F5 in `EXTERNAL_CHECK_V3.md`**. No false-PASS path
was found. This verdict concerns certificate soundness, not the derivation of
the input shape inventories or the rest of the size-5 assembly.

## Surface verdicts

1. **Partition completeness: HOLDS.** Every bad-row/good slot is an integer
   modulus at least 2 and enters exactly one class in `{2,3,4,5,6,BIG>=7}`.
   The first exact slot pins a good; subsequent forced slots must equal their
   declared exact class or remain at least 7. Unmodeled common-scale and
   divisibility compatibility is relaxed, which enlarges the searched class.

2. **BIG representatives: HOLDS.** For row entry `J=j<=40`, a modulus above
   `j` has no events in the prefix and is exactly represented by `j+1`.
   For `j>=6`, enumerating `7..j+1` covers every BIG prefix; for `j<6`, the
   explicit `j+1` representative covers the entire BIG class. Testing badness
   after replacing a larger modulus by the representative only enlarges
   feasibility.

3. **Forced-slot clamp: HOLDS.** A forced modulus above 41 is prefix-identical
   to 41 for every `J<=40`. Replacing it by 41 increases its reciprocal, so a
   true bad row remains included. For `J>40`, the code uses the independent U2
   tail and no clamped prefix value.

4. **Pinned-good row and J interval: HOLDS.** The identities for forced bad-row
   slots, reciprocal good-row slots, and mutual-good slots follow by clearing
   the reduced ratio `y/p_i=v/q`. Exact goodness kills only impossible pinned
   goods. With one free mutual slot, values 2..40 are checked exactly and 41 is
   a conservative representative for the infinite tail; dropping the goodness
   test at 41 enlarges the class. If `tau=floor(n/s)`, the true
   `J_y=floor(qn/(v w_i s))` lies in the enumerated integer interval from
   `floor(q*tau/(v w_i))` through `floor(q*(tau+1)/(v w_i))`; the upper endpoint
   can be one too large, which is conservative. Taking the minimum is necessary
   because `f(J)` is not monotone. Taking `max(exact, staircase)` combines two
   valid lower bounds.

5. **Tau loop and floors: HOLDS.** The identity
   `floor(n/(s w))=floor(floor(n/s)/w)` makes integer `tau=floor(n/s)` exact for
   every bad row. `n>=2max(P)` gives `tau>=2wmax`; nonbridge plus ratio `<7`
   gives a strict upper bound below `33*7*wmax`, while the inclusive code endpoint
   checks one extra value.

6. **Margin assembly: HOLDS.** `m60=2*sum(f*60)-300` is exactly the F4 margin
   with the positive `+S` omitted. Positive margins prove the target; a zero
   margin is rescued by retained `S>0`. Main runs have no zero cases. Bad-row
   tails use `floor(7J/5)-14`, a conservative integer lower bound for U2.

7. **shape4 analogue: HOLDS.** The 4x1 class partition and q pinning are the
   same argument. A pinned good has four exact reciprocal moduli and is checked
   for exact goodness; an all-BIG good uses the universal good staircase at
   `J>=2`. There is no missing free mutual slot in the one-good model.

8. **Arithmetic: HOLDS for the certified fixtures.** All row-table arithmetic
   is exact `i128`. For the 906 triples, the source bounds imply primal-dual
   coefficients below roughly `3.4e7`; q is below 42, keeping the largest
   four-modulus goodness products well below `i128::MAX`. The 174 four-bad
   shapes and four zero-edge shapes are much smaller.

## Nonfatal cleanup

If a pinned-good free-slot table is infeasible for every representative at a
particular `J`, its entry remains `i128::MAX`. Doubling that sentinel in release
mode can wrap. The resulting value is negative and can only create a false
`SHORT`, not a false `PASS`; the current all-PASS outputs therefore remain
sound. Replacing the sentinel with an explicit vacuity branch would make this
cleaner and should be done before publication-grade code freeze.

## Reproduction

```powershell
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape2v3 clustercheck\shapes906.csv 7
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape2v3 zeroedgebankcheck\shapes0edge.csv 7
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml --target-dir C:\tmp\ep488-census-target -- shape4 census\shapes4inv120.csv 7
```

Expected results: `906/906`, `4/4`, and `174/174`, with no ZERO or SHORT.

## Residual dependency

The verdict assumes the F4 drift interpretation, staircase, and tail theorem as
stated in the external brief. Those kernels have separate certificates and were
not reproved in this code pass. A second independent reviewer should still run
the external package before promotion.
