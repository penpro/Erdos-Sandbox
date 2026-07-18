# Compulsory bad-good edge pair probe

This isolated exact Rust tool probes the paired partial-sum floor forced by a
dual strong edge from a bad vertex to a good vertex in the ratio-`<7`
residual. It is a relaxed-row certificate: pairwise consistency with the other
three vertices is intentionally omitted, so its minimum is a valid lower bound
for every realizable pair.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-paircheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path paircheck\Cargo.toml
```

The exact global minima, in units of `1/60`, are:

```text
bad receives m=2:  f_bad+f_good >= 40/60
bad receives m=3:  f_bad+f_good >= 25/60
bad receives m=4:  f_bad+f_good >= 35/60
```

The `m=3` minimum occurs at reverse cofactor `q=2` and equals the independent
baseline `-5/60+30/60`. Thus a compulsory strong edge alone is not a closing
estimate; the hard orientation `(m,q)=(3,2)` must retain more of the joint
cluster structure. The other two source types provide bonuses of `15/60` and
`10/60` over that baseline.
