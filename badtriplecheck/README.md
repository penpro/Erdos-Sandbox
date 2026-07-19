# badtriplecheck

Independent exact Rust audit of the claim that every exactly-three-self-bad
C-B residual has at least two strong edges inside its three bad dual vertices.
It does not modify Claude's `census/` or Codex's `fastcheck/`.

The enumerated dual cores `D=[a,b,c,d,e]` are strictly increasing, primitive,
antichain, window-relevant, have at most two co-good vertices, and satisfy
`CRIT(D) <= 7/2`. A strong edge is

```text
4*gcd(d_i,d_j) >= min(d_i,d_j).
```

Run the exact audit through dual-entry bound 120 with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-badtriplecheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path badtriplecheck\Cargo.toml -- 120 clustercheck\shapes906.csv
```

Expected headline output:

```text
<=2-good window class: 3244
C-B residual: 195
self-bad histogram [0..5]: [0, 0, 0, 188, 7, 0]
exactly-3-bad induced strong edges [0,1,2,3]: [0, 13, 57, 118]
>=2-edge residual coverage by clustercheck\shapes906.csv: 175/175
1-edge normalized shapes (5): {[5,6,9], [5,14,21], [9,10,12], [10,15,18], [10,15,21]}
RESULT: ALL PASS
```

Thus the `clustercheck/shapes906.csv` inventory, which assumes at least two
internal strong edges, is not complete for the full three-bad residual sector.
The first one-edge witness is `D=[9,10,12,15,42]`, whose bad indices are
`[0,1,2]`; its primal set is `P=[30,84,105,126,140]`. This refutes only the
inventory-completeness lemma, not Erdos Problem #488.

The five one-edge shapes seen through `M=120` are stored, with the range in the
filename, at `shapes1edge_m120.csv`. This is a bounded fixture, not a global
inventory claim. The existing shared v3 engine certifies all five:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-census-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path census\Cargo.toml -- shape2v3 badtriplecheck\shapes1edge_m120.csv 7
```

Expected result:

```text
PASS 5 (incl. 0 VACUOUS) / ZERO 0 (pass via +S) / SHORT 0
```
