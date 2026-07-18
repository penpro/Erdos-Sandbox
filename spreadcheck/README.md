# Spread partial-sum certificate

This isolated Rust tool certifies the exact small-argument floors and
largest-element correlation used in the EP488 size-5 SPREAD theorem. It does
not edit or depend on Claude's `census/` crate.

For a four-modulus multiset `m` and

```text
f(J) = sum_{j=1}^J (1/(1+#{i:m_i|j}) - 1/2),
```

it checks exactly:

```text
free class:        f(J) >= -1/12 for every J>=2,
at-most-one-2:     f(J) >=  1/12 for every J>=2,
no-2 class:        f(J) >=  8/3  for every J>=22,
free max row:      f(J) >=  1/6  for J=2,3.
```

The certified drift bounds take over at `J=7`, `J=13`, and `J=25`; Rust
exhausts the remaining finite kernels. For fixed `J`, every modulus greater
than `J` has the same empty event pattern on `[1,J]`, so `J+1` exactly
represents the unbounded tail. Arithmetic uses denominator `60`; there are no
floating-point decisions or external crates.

The checker then uses the compulsory modulus contributed by the largest
element. It certifies:

```text
8<rho<11, J_min<=21: f_min >= 8/3,
7<=rho<8, J_min<=21: f_min >= 31/12,
7<=rho<8:             f_max >= 1/6 because J_max is 2 or 3.
```

The second line is an exact coprime ratio-band scan. If the largest/minimum
pair has reduced cofactors `(m,k)`, it enforces `gcd(m,k)=1`, `k>=2`,
`7<=m/k<8`, and `floor(2m/k)<=J`. The final assembly has margin
`1/3+S`; the `J_min>=22` assembly has margin `S`.

Thus the certificate proves SPREAD for every primitive quintuple with
`rho=max/min>=7`. Equality `rho=8` is impossible in an antichain because it
would make the minimum divide the maximum.

Run on this Windows workspace with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-spreadcheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path spreadcheck\Cargo.toml
```

## Charge-good row floors

A row with `sum 1/m_i < 1` (equivalently, a dual-good vertex) has the
additional exact certificates

```text
J>=2:   f(J) >= 1/2,
J>=6:   f(J) >= 5/6,
J>=12:  f(J) >= 7/6,
J>=15:  f(J) >= 3/2.
```

Each claim uses an exact finite prefix with tail representative `J+1`; the
certified at-most-one-2 drift line supplies the infinite tail. These floors
support the stage-2 donation argument: a donated modulus 2 forces the good
donor's argument upward by DRIFT-1.
