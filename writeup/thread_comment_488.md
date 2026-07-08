# DRAFT comment for erdosproblems.com/488  (for Wes to review & post)

<!-- Honest framing per our audits. Do NOT claim: a new method, a new result,
     or a completed Lean proof. DO cite Chojecki + Heilbronn-Rohrbach. Swap the
     LINK placeholders for the actual repo/PDF URLs before posting. -->

An elementary, self-contained proof of the primitive-core-≤3 case.

The result here is the same as Chojecki's Corollary 4.7 (that (★) holds whenever
the primitive core of $A$ has at most three elements), so I claim no priority for
the statement. I'm posting because the proof is short, uses nothing beyond the
counting function $B$ itself, and — unlike the transport route — has no step of
the "≥4 exact-one points" type. Given that the reduction underlying that step was
shown (Tao, above) to fail for $\min A\ge 3$, an independent elementary route to
the same case may be worth recording.

Reduce to the primitive core $P$ (this only widens the range to $n\ge\max P$).
Write $S=\sum_{d\in P}1/d$. For a primitive triple $a<b<c$, if
$1/b+1/c\le 1/a$ then $B(n)\ge\lfloor n/a\rfloor+1>n/a$ while $B(m)\le mS\le 2m/a$,
so $B(m)/m<2B(n)/n$ (the "sparse" case; this also handles $|P|\le 2$). Otherwise
$1/b+1/c>1/a$, and the two-term Bonferroni bound
$B(n)\ge s(n)-\sum_{\text{pairs}}\lfloor n/\mathrm{lcm}\rfloor$ — the finite-$n$
form of the Heilbronn–Rohrbach inequality — gives, after grouping the pairwise
terms into per-generator "charges"
$X_e=\lfloor n/e\rfloor-\sum_{f\ne e}\lfloor n/\mathrm{lcm}(e,f)\rfloor$,
that each $X_e$ is a positive integer, hence $s(n)-2\sum_{\text{pairs}}\lfloor
n/\mathrm{lcm}\rfloor=X_a+X_b+X_c\ge 3$. The one substantive input is that in this
zone not both $\mathrm{lcm}(a,c)/c=2$ and $\mathrm{lcm}(b,c)/c=2$ (a two-line
parity argument), which is exactly what forces each charge positive. Feeding
$s(n)-2(\cdots)\ge 3$ back through $2\lfloor x\rfloor=x+\lfloor x\rfloor-\{x\}$
yields $2B(n)>nS$ for all $n\ge c$, and then $B(m)/m\le S<2B(n)/n$ for all
$m\ge 1$ — the order-free form. The same charge computation gives (★) for any
primitive set with $\sum_{f\ne e}\gcd(e,f)/f<1$ for every $e$ (e.g. spread
pairwise-coprime sets), but this fails at $|P|=4$ (already for $\{2,3,5,7\}$;
and $A=\{2p:p\le100\}$ shows the criterion $2B(n)>nS$ itself is false for large
sets), so the argument is genuinely special to three generators.

Writeup with full proofs, the sharp/extremal remarks, and the exact obstruction
to four generators:
https://github.com/penpro/Erdos-Sandbox/blob/main/writeup/erdos488_triples.pdf .
Exact-arithmetic verification (all uncovered primitive triples $a\le25$ over full
periods; ~$1.2\times10^9$ direct $(n,m)$ pairs; PASS):
https://github.com/penpro/Erdos-Sandbox/blob/main/attack_triples.py .

Lean status: the self-contained arithmetic core is already formalized sorry-free
in Lean 4 / Mathlib — including the parity dichotomy above (the single
substantive step), verified `#print axioms`-clean:
https://github.com/penpro/Erdos-Sandbox/tree/main/lean/ep488 . The remaining
piece is the counting half (the finite-$n$ Heilbronn–Rohrbach / two-term
Bonferroni bound) and the mechanical assembly; I'll follow up when that compiles.

—[your name/handle]

---

## Pre-post checklist
- [ ] Replace `[LINK to PDF]` and `[LINK to code]` with real URLs (push the repo first).
- [ ] Confirm the account/handle you want to post under.
- [ ] Decide attribution wording (e.g. acknowledge the AI-assisted sandbox if you wish).
- [ ] Optional: mention it also settles the order-free bound with explicit separator S.
- [ ] Do NOT state the Lean is done until it compiles.
