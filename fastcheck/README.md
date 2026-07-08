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
  already handled by reciprocal-sparse or charge-positivity, and tries exact
  certificates on the residual sets whose lcm is below the chosen cap.

All proof-relevant comparisons are integer/rational comparisons. Decimal output
is diagnostic only.

## Speed

Toolchain: pinned to the GNU Rust toolchain (`rustup override`), release build.
On the identical scan of all primitive triples with elements in `[2,60]`
(windowed worst-ratio + counterexample check), Rust finishes in **~0.3 s**; the
same loop in CPython did **not** finish in 120 s — a **>400×** speedup (the true
factor is larger). This is the entire point of the workbench: it lets the OPEN
`|P| >= 4` frontier be searched at a scale Python cannot reach.

## Findings so far (all consistent with EP488 being true)

- **No counterexample found** to EP488 in any search: primitive triples to
  `max <= 100+`, primitive quadruples to `max = 120` (windowed), quintuples to
  `max = 30`. The site lists #488 as open; this is evidence, not a proof.
- **Extremal family:** the worst ratio is always a *consecutive run*
  `{a, a+1, ..., a+k-1}`, whose ratio tends to `2` from below (e.g. triples
  `{98,99,100} ~ 1.9566`, quads `{117,118,119,120} ~ 1.9417`). (This corrected an
  earlier over-strong "singletons only" claim.)
- **Exact certification:** every primitive quadruple with small enough `lcm` up to
  `N = 150` is *proof-strength* certified (`beta < 2*alpha` over a full period),
  after the charge-positivity / covered-zone theorems dispose of the rest.

## Honest scope (please read)

- `triples`/`quads`/`quints`/`set` give **bounded-window evidence**, not proof.
- `cert`/`sweep-quad-cert` give a **proof-strength certificate for that specific
  finite set** (exact, full-period) — this is NOT a general theorem for
  `|P| >= 4`, which remains **open**. The proved result is `|P| <= 3` (see
  `../writeup`, `../lean/ep488`).

Division of labor: the windowed searcher is Claude's; the exact certificate layer
is Codex's (the two cross-validate — e.g. both give `{19,20,21} -> 666/361`).
