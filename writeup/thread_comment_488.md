# DRAFT comment for erdosproblems.com/488  (for Wes to post)

> **Recommended: post [`thread_comment_488_cautious.md`](thread_comment_488_cautious.md)
> instead of this one.** That version (written by Codex, math-checked) spells out
> the full short proof inline so a reviewer can verify it on the spot, and it is
> more heavily hedged — better for surviving scrutiny. This shorter, links-only
> version is kept as an alternative.


Copy everything between the two `=====` lines into the comment box, replace
`—[your name]`, and post. The box supports LaTeX (`$...$`) and `<a>` HTML links;
`\lt \gt \le \ge` are used instead of `< > <= >=` so nothing is mistaken for HTML.

=====================================================================
An elementary, self-contained proof of the primitive-core-$\le 3$ case.

The result here is the same as Chojecki's Corollary 4.7 (that the inequality holds whenever the primitive core of $A$ has at most three elements), so I claim no priority for the statement. I'm posting because the proof is short, uses nothing beyond the counting function $B$ itself, and — unlike the transport route — has no step of the "$\ge 4$ exact-one points" type. Given MalekZ's observation (31 Mar) that the fixed-threshold reduction fails for $\min A \ge 3$, an independent elementary route to the same case may be worth recording.

Reduce to the primitive core $P$ (this only widens the range to $n \ge \max P$). Write $S = \sum_{d \in P} 1/d$. For a primitive triple $a \lt b \lt c$: if $1/b + 1/c \le 1/a$ then $B(n) \ge \lfloor n/a \rfloor + 1 \gt n/a$ while $B(m) \le mS \le 2m/a$, so $B(m)/m \lt 2B(n)/n$ (the "sparse" case; this also handles $|P| \le 2$). Otherwise $1/b + 1/c \gt 1/a$, and the two-term Bonferroni bound $B(n) \ge s(n) - \sum_{\text{pairs}} \lfloor n/\mathrm{lcm} \rfloor$ — the finite-$n$ form of the Heilbronn–Rohrbach inequality — gives, after grouping the pairwise terms into per-generator "charges" $X_e = \lfloor n/e \rfloor - \sum_{f \ne e} \lfloor n/\mathrm{lcm}(e,f) \rfloor$, that each $X_e$ is a positive integer, hence $s(n) - 2\sum_{\text{pairs}} \lfloor n/\mathrm{lcm} \rfloor = X_a + X_b + X_c \ge 3$. The one substantive input is that in this zone not both $\mathrm{lcm}(a,c)/c = 2$ and $\mathrm{lcm}(b,c)/c = 2$ (a two-line parity argument), which forces each charge positive. Feeding $s(n) - 2(\cdots) \ge 3$ through $2\lfloor x \rfloor = x + \lfloor x \rfloor - \{x\}$ yields $2B(n) \gt nS$ for all $n \ge c$, hence $B(m)/m \le S \lt 2B(n)/n$ for all $m \ge 1$ — the order-free form. The same computation gives the inequality for any primitive set with $\sum_{f \ne e} \gcd(e,f)/f \lt 1$ for every $e$, but this fails at $|P| = 4$ (already $\{2,3,5,7\}$; and $A = \{2p : p \le 100\}$ shows $2B(n) \gt nS$ itself is false for large sets), so it is genuinely special to three generators.

Writeup with full proofs and the obstruction to four generators: <a href="https://github.com/penpro/Erdos-Sandbox/blob/main/writeup/erdos488_triples.pdf">erdos488_triples.pdf</a>. Exact-arithmetic verification (all uncovered primitive triples $a \le 25$ over full periods; $\sim 1.2 \times 10^9$ direct $(n,m)$ pairs; PASS): <a href="https://github.com/penpro/Erdos-Sandbox/blob/main/attack_triples.py">attack_triples.py</a>. The self-contained arithmetic core — including the parity dichotomy above, the single substantive step — is formalized sorry-free in Lean 4 / Mathlib (verified <code>#print axioms</code>-clean): <a href="https://github.com/penpro/Erdos-Sandbox/tree/main/lean/ep488">lean/ep488</a>. The remaining piece is the counting half (the finite-$n$ Heilbronn–Rohrbach bound) and the mechanical assembly; help finishing it is welcome.

Full disclosure: this was produced in an AI-assisted sandbox (Claude + Codex) and independently cross-checked, but a second human eye on the note and the Lean would be welcome.

—[your name]
=====================================================================

## Notes
- Sign-in: you are already signed in as `wesleyaweaverjr`.
- Comments go into a moderation queue and appear after approval.
- If the `$...$` doesn't render on preview, tell me and I'll adjust delimiters.
