# zeroedgebankcheck

Independent exact rational-template census for compact C-B residuals with
exactly three bad dual vertices and no strong edge inside the bad triple.

For each bad `b`, its two bad-bad gcds are at most `b/5`, so its two goods must
supply at least `3b/5`. Writing

```text
b/g1 = c1/k1,  g2/b = k2/c2
```

in lowest terms gives `1/c1+1/c2>=3/5`, hence `2<=c1,c2<=10`.
Antichain and compact spread give `2<=k_j<7c_j` (with the reciprocal spread
inequality checked as well). Anchor `g1=1`; then

```text
b/g1 = c1/k1,
g2/g1 = c1*k2/(k1*c2).
```

For a fixed second-good ratio, all compatible bad ratios therefore come from a
finite exact rational list. The tool chooses three distinct bad ratios,
normalizes the five rationals to a primitive integer core, and filters exact
antichain, spread, bad-count, zero-edge, window, and `CRIT<=7/2` conditions.
Any surviving bank member is checked by the exact tower inequality.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-zeroedgebankcheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path zeroedgebankcheck\Cargo.toml
```

Expected output:

```text
pin descriptors: 2610
distinct good ratios: 1830
rational bad triples tested: 2722
normalized five-cores: 1323
zero-edge exactly-3-bad compact C-B residuals: 4
D=[210,330,462,770,1155]
D=[210,390,546,910,1365]
D=[330,390,858,1430,2145]
D=[462,546,858,2002,3003]
tower failures: 0
RESULT: ALL PASS
```

The four normalized bad triples are stored in `shapes0edge.csv`; shared v3 also
passes all four. The direct tower check covers `7(m+1)S<1135`, while U2 proves
the same tower inequality on the complementary range. Thus the bank is uniform
under gcd scaling, subject to audit of the rational-template surjectivity proof.
