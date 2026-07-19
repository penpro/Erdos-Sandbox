# oneedgebankcheck

Independent exact Rust bank for the exactly-three-bad compact C-B residuals
whose bad triple induces exactly one strong edge. This corrects the scale
inequalities in the initial `census bank1edge` draft.

Write the strong pair as `u*{alpha,alpha'}` and the isolated bad plus its two
goods as

```text
v*{L, L*k1/c1, L*k2/c2},  L=lcm(c1,c2).
```

The isolated badness gives `1/c1+1/c2 >= 3/5`, so after ordering,
`c1 in {2,3}` and `c2<=10`. CROSS applied to either bad pair row gives

```text
u <= (L + L*k1/c1 + L*k2/c2) * alpha/(alpha-1).
```

For the isolated bad row, CROSS uses the internal charges `1/c1+1/c2`
(not `1/k1+1/k2`). If their sum is below one it bounds `v`; in the equality
case `c1=c2=2`, compact spread `vL < 7*u*min(alpha,alpha')` bounds `v`.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-oneedgebankcheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path oneedgebankcheck\Cargo.toml
```

The tool filters every generated tuple by primitive antichain, compact spread,
exactly three bad vertices, exactly one induced bad-bad strong edge, window, and
`CRIT<=7/2`, then checks the exact tower inequality for every bank member.

Expected headline output:

```text
raw parameter tuples: 161310876
one-edge exactly-3-bad compact C-B residuals: 19
tower failures: 0
worst margin = 151632000/52488000 ~ 2.888889
RESULT: ALL PASS
```

The tower check covers the range `7(m+1)S<1135`. On its complement, U2 gives

```text
2B(m)-mS >= (7mS-1135+157S)/150 >= S,
```

so the same tower inequality holds there analytically. This also covers every
gcd scaling through `B_(tP)(n)=B_P(floor(n/t))`.
