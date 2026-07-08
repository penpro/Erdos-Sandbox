# fastcheck

Fast exact-integer scratch tools for Erdős #488.

This is a research workbench, not a substitute for written proof. It has two
complementary modes:

- bounded-window hunting, useful for large counterexample searches;
- exact periodic certificates, useful when the lcm is small enough to scan.

## Commands

```text
cargo run --release -- selftest
cargo run --release -- triples 30 40
cargo run --release -- quads 35 50 --uncovered
cargo run --release -- set 2,3,5,7 80
```

The commands above are Claude's bounded-window checker. They search
`max(A) <= n < m <= window_factor * max(A)` and keep the best suffix value of
`B(m)/m` in one backwards pass.

```text
cargo run --release -- classify 2,3,5,7
cargo run --release -- cert 2,3,5,7 50000000
cargo run --release -- sweep-quad-cert 30 3000000
```

The commands above are Codex's exact periodic-certificate layer.

- `classify` reports the reciprocal-sparse and charge-positive regimes.
- `cert` computes exact global candidates for `alpha = inf B(x)/x` and
  `beta = sup B(x)/x` over `x >= max(A)`. If `beta < 2*alpha`, this proves the
  ordering-free strengthening for that finite set.
- `sweep-quad-cert` enumerates primitive quadruples up to `N`, skips those
  already handled by reciprocal-sparse or the two-good-charge rescue lemma in
  `../quadruple_charge_notes.md`, and tries exact certificates on any remaining
  residual sets whose lcm is below the chosen cap.

All proof-relevant comparisons are integer/rational comparisons. Decimal output
is diagnostic only.

## Speed

Toolchain: pinned to the GNU Rust toolchain (`rustup override`), release build.
On the identical scan of all primitive triples with elements in `[2,60]`
(windowed worst-ratio + counterexample check), Rust finishes in **~0.3 s**; the
same loop in CPython did **not** finish in 120 s — a **>400×** speedup (the true
factor is larger). This is the entire point of the workbench: it lets the OPEN
`|P| >= 4` frontier be searched at a scale Python cannot reach.

### Multi-core

The enumeration modes (`triples`/`quads`/`quints`) and the exact
`sweep-quad-cert` sweep are parallelised across all cores with `std::thread`
(no external crate — the offline-by-default rule holds). The smallest element is
split round-robin across threads and the per-thread partial results are merged
**exactly**, so the output (counts, worst ratio + witness, certificate tallies)
is bit-identical to the serial run. On the 32-thread 14900K:

```text
quads 90 (1,735,597 primitive quadruples, windowed):
  FASTCHECK_THREADS=1   31.91 s
  all cores (32)         2.06 s        -> 15.5x, identical worst ratio 1.9409...
```

Set `FASTCHECK_THREADS=N` to pin the worker count (e.g. `=1` to force the serial
path for benchmarking or on a loaded machine); the default is all logical cores.

## Findings so far (all consistent with EP488 being true)

- **No counterexample found** to EP488 in any search: primitive triples to
  `max <= 100+`, primitive quadruples to `max = 120` (windowed), quintuples to
  `max = 30`. The site lists #488 as open; this is evidence, not a proof.
- **Extremal family:** the worst ratio is always a *consecutive run*
  `{a, a+1, ..., a+k-1}`, whose ratio tends to `2` from below (e.g. triples
  `{98,99,100} ~ 1.9566`, quads `{117,118,119,120} ~ 1.9417`). (This corrected an
  earlier over-strong "singletons only" claim.)
- **Size-4 symbolic check:** every primitive quadruple with entries up to
  `N = 150` satisfies the two-good-charge rescue condition from
  `../quadruple_charge_notes.md`; there is no residual after that symbolic
  regime. The `cert` command remains available for proof-strength certificates
  of individual finite sets when the lcm is small enough.

## Honest scope (please read)

- `triples`/`quads`/`quints`/`set` give **bounded-window evidence**, not proof.
- `cert` gives a **proof-strength certificate for that specific finite set**
  (exact, full-period).
- `sweep-quad-cert` is now mostly a symbolic-regime audit for the local size-4
  addendum. Treat `|P|<=4` as internal until human/literature review; the open
  frontier is `|P|>=5`.

Division of labor: the windowed searcher is Claude's; the exact certificate layer
is Codex's (the two cross-validate — e.g. both give `{19,20,21} -> 666/361`).
