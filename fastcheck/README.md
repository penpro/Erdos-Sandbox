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
cargo run --release -- quint-separator 50 120
cargo run --release -- density 60,80,90,99,100
```

The commands above are Claude's bounded-window checker. They search
`max(A) <= n < m <= window_factor * max(A)` and keep the best suffix value of
`B(m)/m` in one backwards pass. `quint-separator` instead searches the raw
size-5 union-bound separator `2B(n) > n*sum(1/a)` over the same bounded window;
add `--middle` to skip the proved first window `n < 2*min(A)`, and `--cover`
to restrict to the current size-5 cover class: gcd 1, at most two good charges,
and `max(A)*sum(1/a) <= 1135/7`. Add `--top K` to print the largest separator
witness ratios.

```text
cargo run --release -- classify 2,3,5,7
cargo run --release -- tower 76,114,153,171,285
cargo run --release -- cert 2,3,5,7 50000000
cargo run --release -- sweep-quad-cert 30 3000000
cargo run --release -- sweep-quint-cert 35 3000000 25
cargo run --release -- quint-density 100 --gcd1 --top 10
```

The commands above are Codex's exact periodic-certificate layer.

- `classify` reports the reciprocal-sparse and charge-positive regimes.
- `density` reports the exact asymptotic density `delta` and the gap
  `2*delta - sum(1/a)` for one finite set.
- `tower` checks the size-5 tower inequality
  `2B(m) >= (m+1)*sum(1/a)` on the drift-bridge window for one set.
- `cert` computes exact global candidates for `alpha = inf B(x)/x` and
  `beta = sup B(x)/x` over `x >= max(A)`. If `beta < 2*alpha`, this proves the
  ordering-free strengthening for that finite set.
- `sweep-quad-cert` enumerates primitive quadruples up to `N`, skips those
  already handled by reciprocal-sparse or the two-good-charge rescue lemma in
  `../quadruple_charge_notes.md`, and tries exact certificates on any remaining
  residual sets whose lcm is below the chosen cap.
- `sweep-quint-cert` does the analogous first-pass size-5 sweep: it skips
  `2 in A`, reciprocal-sparse, and three-good-charge quintuples,
  exact-certifies residuals with small lcm, reports whether the stronger
  union-bound separator still holds, and optionally prints more residual
  classes up to common scaling.
- `quint-density` exactly checks the asymptotic density gap `2*delta > sum(1/a)`
  for primitive quintuples by inclusion-exclusion over the 31 nonempty subsets.
  Add `--top K` to print the `K` smallest positive gaps, which is useful for
  spotting near-extremal families. Add `--hard` to restrict to the current
  post-Lean size-5 frontier: no `2`, not reciprocal-sparse, and fewer than
  three good charges. Add `--residual` to also remove the currently audited
  scaled-family templates Q through AX.

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
- **Size-5 first pass:** `sweep-quint-cert 100 3000000` enumerates 43,291,981
  primitive quintuples; after `2 in A`, reciprocal-sparse, and
  three-good-charge symbolic regimes, plus thirty-three scaled-family audits, only
  950 residuals remain, all exact-certified and all satisfying the stronger
  union-bound separator. The helper `../audit_scaled_quint_families.py`
  exact-audits those scaled families.
- **Raw size-5 separator hunt:** `quint-separator 80 120 --uncovered` checked
  9,799,967 reciprocal-heavy primitive quintuples in the bounded window and found
  no failure of `2B(n) > n*sum(1/a)`. The closest case was the consecutive run
  `{76,77,78,79,80}` at `n=151`, with `nS/(2B(n)) = 3491573453/3606002400`.
- **Size-5 density gap:** `quint-density 120 --gcd1 --top 15` checked
  114,647,427 gcd-1 primitive quintuple base shapes and found no failure of
  `2*delta > sum(1/a)`. The smallest positive gap was `2509/99360`, at
  `{72,96,108,115,120}`. The all-quintuple near-misses follow the easy
  good-charge skeleton `{6q,8q,9q,10q-h,10q}` and have gap
  `37/(120q)+O(1/q^2)`, so they stress a universal density proof but not the
  current <=2-good residual.
- **Size-5 residual density gap:** `quint-density 150 --gcd1 --residual --top 20`
  checked 1,185 post-audit residual base shapes through `amax=150` and found no
  density failure. The smallest positive gap was `7/240`, at
  `{54,80,90,120,135}`; `cert 54,80,90,120,135 3000000` gives
  `beta/alpha = 319/240` and the union-bound separator still passes.
- **Size-5 cover-class separator:** `quint-separator 200 33 --cover` checked
  4,347 gcd-1 quintuples in the current cover class (at most two good charges
  and `max(A)*sum(1/a) <= 1135/7`) and found no failure of
  `2B(n) > n*sum(1/a)`. The closest case was `{4,6,9,10,14}` at `n=39`, with
  `nS/(2B(n)) = 34359/40320`. The `--top 20` list through `amax=150` is still
  led by small scaled-family base shapes, with the 20th witness below `0.812`.
  The same cover scan now reports G3-oriented stats: through `amax=200`, broad
  cover candidates have `max min(A)=56`; the two `min(A)>54` candidates are
  `{56,72,84,126,189}` and `{56,84,108,126,189}`, both C3-style continuations
  with positive `tower` margins.
  This is evidence for the cover lemma, not proof.

## Honest scope (please read)

- `triples`/`quads`/`quints`/`set` give **bounded-window evidence**, not proof.
- `cert` gives a **proof-strength certificate for that specific finite set**
  (exact, full-period).
- `sweep-quad-cert` is now mostly a symbolic-regime audit for the local size-4
  addendum. Treat `|P|<=4` as internal until human/literature review.
- `sweep-quint-cert` is exploratory: size 5 already has counterexamples to the
  naive "three good charges always" closing condition, so residuals matter.
- `quint-separator` is bounded-window evidence only; use `cert` for a
  proof-strength full-period separator check on one finite set when the lcm is
  small enough.
- `quint-density` is exact for the asymptotic density inequality, but it does not
  by itself prove the finite-`n` separator or EP488.

Division of labor: the windowed searcher is Claude's; the exact certificate layer
is Codex's (the two cross-validate — e.g. both give `{19,20,21} -> 666/361`).
