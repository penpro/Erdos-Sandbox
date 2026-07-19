# Min-strong cluster census

This isolated Rust tool enumerates the corrected normalized triple inventory
for the EP488 compact box. It intentionally does not modify Claude's `census/`.

It checks sorted triples `a<b<c` satisfying:

```text
gcd(a,b,c)=1,
no divisibility,
c<7a,
at least two edges with 4*gcd(x,y)>=min(x,y).
```

The proved cap `a<112` makes the sweep exhaustive. It separately counts the
old max-strong subset and records whether the largest coefficient can own an
internal strong edge.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-clustercheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path clustercheck\Cargo.toml
```

Current exact ratio-7 output:

```text
min-strong triples: 906
old max-strong subset: 4
all three can own internal edges: 69
all 906 by vertices forced outside: [0, 20, 258, 628]
69 internal-owner shapes by deficit-forced vertices: [0, 6, 17, 46]
sealed internal-owner shapes: 0
```

The tool prints the 69 all-internal-owner shapes and a deterministic digest
of the full 906-shape sequence. It asserts that the generated lists exactly
match both canonical files: `shapes69.csv` for the internal-owner subset and
`shapes906.csv` for the complete min-strong inventory. Passing an output path
rewrites a full CSV from the exhaustive generator; for example:

```powershell
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path clustercheck\Cargo.toml -- C:\tmp\shapes906.csv
```

The deficit test uses the exact divisor jump:
if an edge from source `x` is not strong, then `x/gcd` is an integer greater
than `4`, so that gcd is at most `x/5`. Two non-strong outside edges therefore
supply at most `2x/5`.

Consequently, in a ratio-`<7` quintuple with exactly three bad dual vertices,
at least one bad vertex has a strong edge to a good vertex. If no such edge
existed, all three bads would own internal edges in a connected triple; the
69-shape scan proves that one of them would still need a strong outside edge.

Together with the elementary two-pair argument documented in
`cbfin_reduction_notes.md`, this rules out every three-component strong graph
in the compact residual.
