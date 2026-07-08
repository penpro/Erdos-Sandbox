# Cautious draft comment for erdosproblems.com/488

Copy everything between the two `=====` lines into the comment box, replacing
`-- [your name]`. This version intentionally avoids novelty overclaiming and
does not call the partial Lean formalization a full verification.

=====================================================================
An elementary, self-contained proof of the primitive-core-$\le 3$ case.

This is the same statement as Chojecki's Corollary 4.7, so I am not claiming priority for the result. I am posting because the proof below is quite short, uses only the original counting function $B$, and gives an independent route to the case where the primitive core has at most three elements.

Let $P$ be the primitive core of $A$; replacing $A$ by $P$ leaves $B$ unchanged and only widens the range to $n \ge \max P$. Write $S=\sum_{d\in P}1/d$.

The singleton case is the usual sharp example: if $P=\{a\}$ then $B(x)=\lfloor x/a\rfloor$, and $B(m)/m<2B(n)/n$ for all $m>n\ge a$. If $P=\{a,b\}$, the same comparison as below works: $B(n)\ge \lfloor n/a\rfloor+1\gt n/a$ and $B(m)\le m(1/a+1/b)<2m/a$.

For a primitive triple $a\lt b\lt c$, first suppose $1/b+1/c\le 1/a$. Then $B(n)\ge \lfloor n/a\rfloor+1\gt n/a$ for $n\ge c$, while $B(m)\le mS\le 2m/a$, so the desired inequality follows.

It remains to consider $1/b+1/c\gt1/a$. Put

$$
s(n)=\lfloor n/a\rfloor+\lfloor n/b\rfloor+\lfloor n/c\rfloor,\qquad
P_2(n)=\sum_{\{x,y\}\subset\{a,b,c\}}\lfloor n/\operatorname{lcm}(x,y)\rfloor.
$$

The finite two-term Bonferroni bound gives $B(n)\ge s(n)-P_2(n)$. Group the pairwise-lcm terms into charges

$$
X_e=\lfloor n/e\rfloor-\sum_{f\ne e}\lfloor n/\operatorname{lcm}(e,f)\rfloor
\qquad(e\in\{a,b,c\}).
$$

Then $X_a+X_b+X_c=s(n)-2P_2(n)$. Primitivity gives the lcm-ratio bounds needed to show $X_a,X_b\ge1$. For $X_c$ one needs one extra observation: in the zone $1/b+1/c\gt1/a$, not both $\operatorname{lcm}(a,c)/c=2$ and $\operatorname{lcm}(b,c)/c=2$ can hold. Indeed, if both held, writing $c=k(a/2)=\ell(b/2)$ with odd $k>\ell$ gives $k\ge \ell+2$, hence $1/a=k/(2c)\ge \ell/(2c)+1/c=1/b+1/c$, a contradiction. Thus also $X_c\ge1$, and so

$$
s(n)-2P_2(n)\ge3.
$$

Combining this with $2\lfloor x\rfloor=x+\lfloor x\rfloor-\{x\}$ and the fact that three fractional parts have sum $<3$, one gets

$$
2B(n)\ge 2s(n)-2P_2(n)>nS+(s(n)-2P_2(n))-3\ge nS.
$$

Therefore $B(m)/m\le S\lt 2B(n)/n$ for all $m\ge1$, $n\ge c$. This proves the order-free form for primitive triples, and hence EP488 whenever the primitive core has at most three elements.

Full writeup: <a href="https://github.com/penpro/Erdos-Sandbox/blob/main/writeup/erdos488_triples.pdf">erdos488_triples.pdf</a>. Exact-arithmetic checks: <a href="https://github.com/penpro/Erdos-Sandbox/blob/main/attack_triples.py">attack_triples.py</a>. A partial Lean 4 / Mathlib formalization of the arithmetic core, including the parity dichotomy above, is here: <a href="https://github.com/penpro/Erdos-Sandbox/tree/main/lean/ep488">lean/ep488</a>. The counting half is not yet formalized, so this is not a complete Lean proof.

Full disclosure: this was produced in an AI-assisted sandbox (Claude + Codex) and cross-checked adversarially. I would very much welcome human review, especially of the short charge argument above and the Lean formalization.

-- [your name]
=====================================================================
