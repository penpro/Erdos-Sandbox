"""Extract normalized primal 4-bad shapes from cb 240 witness lines.

Input: lines '  4-BAD residual: D=[...]  P=[...]  comps=...'
For each dual core D: bad dual indices i with sum_j gcd(d_i,d_j) >= d_i (DT);
primal bads = lcm(D)/d_i for those i, normalized by their gcd. Emit unique
shapes as CSV (4 primal coefficients, ascending) + a report.
"""
import re, sys
from math import gcd
from functools import reduce

def lcm(a, b): return a // gcd(a, b) * b

shapes = {}
for line in open(sys.argv[1], encoding="utf-8", errors="replace"):
    m = re.match(r"\s*4-BAD residual: D=\[([0-9, ]+)\]", line)
    if not m:
        continue
    D = [int(t) for t in m.group(1).split(",")]
    L = reduce(lcm, D)
    bads = []
    good = []
    for i, d in enumerate(D):
        s = sum(gcd(d, D[j]) for j in range(5) if j != i)
        (bads if s >= d else good).append(L // d)
    assert len(bads) == 4 and len(good) == 1, (D, bads, good)
    g = reduce(gcd, bads)
    shape = tuple(sorted(b // g for b in bads))
    shapes.setdefault(shape, []).append((D, sorted(bads), good[0], g))

for shape, wits in sorted(shapes.items()):
    print("shape", ",".join(map(str, shape)), " witnesses:", len(wits))
    for D, bads, good, g in wits:
        print("   D=", D, " bads=", bads, "(scale", str(g) + ")", " good=", good)
with open(sys.argv[2], "w") as f:
    for shape in sorted(shapes):
        f.write(",".join(map(str, shape)) + "\n")
print("wrote", sys.argv[2], "with", len(shapes), "unique shapes")
