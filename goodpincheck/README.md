# Pinned charge-good row checker

This isolated Rust tool computes exact lower floors for a charge-good
four-modulus row after retaining compulsory return moduli donated by bad rows.
The currently relevant pin multisets are the unpinned baseline, each odd return
`q in {3,5,7,9,11,13}`, and the forced shared-donor pairs `[3,5]` and `[3,7]`.

For each `J=2..80`, every free modulus at most `J` is enumerated and `J+1`
exactly represents the unbounded class of moduli greater than `J`. A free tail
has no divisibility events through `J` and can have arbitrarily small positive
reciprocal. Thus the strict charge-good test retains the reciprocals of all
fixed pins and free moduli at most `J`, and requires their sum to be `<1`.
All decisions use `i128` common-denominator arithmetic.

The previously certified at-most-one-2 drift line applies to every charge-good
row and gives `f60 >= 204` from `J=81` onward. The finite scan therefore proves
the reported suffix floors after taking the minimum of each finite suffix and
the certified infinite-tail floor.

Run with:

```powershell
$env:CARGO_TARGET_DIR='C:\tmp\ep488-goodpincheck-target'
cargo +stable-x86_64-pc-windows-gnu run --release --manifest-path goodpincheck\Cargo.toml
```
