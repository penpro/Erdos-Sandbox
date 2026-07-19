# Four-bad shape completeness checker

This isolated exact Rust tool independently closes the normalized shape
inventory for the four-bad compact sector. It does not modify or depend on
Claude's `census` implementation, apart from reading the canonical 174-shape
CSV as an expected-output fixture.

For every necessary-filter shape, each row has internal reciprocal sum at
least `1/2`; hence every vertex has an incident **heavy** edge. If
`x=g*a`, `y=g*b` in lowest terms, heavy means `a<=6` or `b<=6`. The ratio-7
condition then bounds both edge cofactors by `41`.

A four-vertex graph of minimum degree one is either connected or has two
two-vertex components:

- **Connected:** choose a labeled heavy spanning tree. Its three edge ratios
  come from a finite cofactor list, and determine the normalized quadruple
  uniquely. The checker enumerates all 16 labeled trees and every ratio choice.
- **Two-pair:** each component has coprime cofactors at most 42. A needy row
  forces a cross reduced denominator at most 12 and numerator at most 83;
  coprime component scales are then determined exactly. The checker enumerates
  this finite box independently of any bound on the smallest element.

Every generated quadruple is checked exactly for distinctness, antichainness,
gcd one, ratio below 7, and all four reciprocal-row inequalities. The resulting
sets are compared with `census/shapes4inv120.csv`.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-fourbadcheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path fourbadcheck\Cargo.toml
```

A passing result proves that the 174-shape list is globally complete; no
`w1<=1512` raw sweep is needed. Combined with the shared `shape4` certificate
on those 174 shapes, this closes the four-bad compact sector at certificate
tier, subject to independent review of both finite reductions.
