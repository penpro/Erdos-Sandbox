# U2 prime-period checker

This dependency-free Rust checker matches `Ep488.U2PrimePeriodKernel` in
`lean/ep488/Ep488/DriftKernelReduction.lean`.

It checks all 256 ordered 4-tuples over `{2,3,5,7}`. For each tuple it scans
every prefix `0 <= J <= L`, where `L` is the tuple LCM, and verifies exactly

```text
7J - 70 <= 300 f(J),
7L      <= 300 f(L).
```

The arithmetic is integral: `60 f(J)` is an integer, so the right side is
`5 * (60 f(J))`. Release overflow checks are enabled; all values here are tiny.
The checker separately counts the 35 nondecreasing tuples, i.e. permutation
classes.

Run from the repository root:

```powershell
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path u2primecheck/Cargo.toml --target-dir C:/tmp/ep488-u2prime-target
```
