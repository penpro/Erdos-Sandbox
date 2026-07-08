#!/usr/bin/env python3
# Adversarial referee brute-force check of triples_writeup.md (Erdos #488, |A_min|<=3).
# Exact integer arithmetic in all hot loops (Fraction only for reporting). Streams progress.
import sys, time
from math import gcd
from fractions import Fraction

def pr(*a): print(*a); sys.stdout.flush()
def lcm(x, y): return x // gcd(x, y) * y
T0 = time.time()
def el(): return f"[{time.time()-T0:6.1f}s]"

def iter_uncovered(amax):
    """All primitive triples a<b<c with 1/b+1/c>1/a. Uncovered => b<2a, c<ab/(b-a)."""
    for a in range(2, amax+1):
        for b in range(a+1, 2*a):
            if b % a == 0: continue
            # 1/c > (b-a)/(ab)  <=>  c*(b-a) < ab
            for c in range(b+1, (a*b)//(b-a) + 1):
                if c % a == 0 or c % b == 0: continue
                # exact: 1/b+1/c > 1/a  <=>  a*c + a*b > b*c  (multiply by a*b*c>0)
                if a*c + a*b > b*c:
                    yield a, b, c

fails = []
def check(name, ok, detail=""):
    if not ok: fails.append(name)
    pr(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))

# =====================================================================
pr("="*72); pr("CHECK 1  Lemma 1(ii): t-floor(t/q)-floor(t/q')>=1,")
pr("  t>=1, {q,q'} min>=2 & max>=3; also >= t/6."); pr("="*72)
TMAX, QMAX = 3000, 120
min_val=None; min_at=None; t6_bad=0
for q in range(2, QMAX+1):
    for qp in range(2, QMAX+1):
        if not (min(q,qp)>=2 and max(q,qp)>=3): continue
        for t in range(1, TMAX+1):
            v = t - t//q - t//qp
            if 6*v < t: t6_bad += 1
            if min_val is None or v < min_val: min_val=v; min_at=(t,q,qp)
check(f"Lemma1ii >=1 (t<={TMAX}, q,q'<={QMAX})", min_val>=1, f"min={min_val} at (t,q,q')={min_at}")
check("Lemma1ii >= t/6 bound", t6_bad==0, "never violated")
check("Lemma1ii control (2,2),t=2 -> 0 (max>=3 required)", 2-2//2-2//2==0, "correctly excluded")
pr(el(),"check1 done")

# =====================================================================
pr("="*72); pr("CHECK 2  Lemma 3: primitive pair x<y => L/x=y/g>=3, L/y=x/g>=2.")
pr("  All primitive pairs x<y<=3000."); pr("="*72)
N3=3000; viol=0; wLx=None; wLy=None
for x in range(2, N3+1):
    for y in range(x+1, N3+1):
        if y % x == 0: continue
        g = gcd(x,y); r1=y//g; r2=x//g
        if r1<3 or r2<2:
            viol+=1
            if viol<=5: pr(f"   VIOLATION x={x} y={y} L/x={r1} L/y={r2}")
        if wLx is None or r1<wLx[0]: wLx=(r1,x,y)
        if wLy is None or r2<wLy[0]: wLy=(r2,x,y)
check(f"Lemma3 primitive pairs<= {N3}", viol==0,
      f"min(L/x)={wLx[0]} at {wLx[1:]}, min(L/y)={wLy[0]} at {wLy[1:]}")
pr(el(),"check2 done")

# =====================================================================
pr("="*72); pr("CHECK 3  Lemma 4 (crux), two independent sweeps:")
pr("  (A) ALL primitive triples with BOTH L_ac/c=2 & L_bc/c=2 (c<=3000) COVERED?")
pr("  (B) ALL uncovered primitive triples a<=300: any with both ratios=2?"); pr("="*72)
N4=3000; abstract=0; abstract_viol=0; on_boundary=0
for c in range(3, N4+1):
    two = c & (-c); codd = c // two
    elts=[]; d=1
    while d*d <= codd:
        if codd % d == 0:
            for e0 in {d, codd//d}:
                x = 2*e0*two
                if x < c: elts.append(x)
        d += 1
    elts=sorted(set(elts))
    for i in range(len(elts)):
        a=elts[i]
        for j in range(i+1, len(elts)):
            b=elts[j]
            if b % a == 0: continue
            abstract += 1
            # 1/b+1/c vs 1/a  <=>  a*c+a*b vs b*c
            lhs=a*c+a*b; rhs=b*c
            if lhs > rhs:
                abstract_viol+=1
                if abstract_viol<=5: pr(f"   LEMMA4 COUNTEREX a={a} b={b} c={c}")
            elif lhs==rhs: on_boundary+=1
check(f"Lemma4 (A) {abstract} both-ratio-2 primitive triples (c<={N4}) all covered",
      abstract_viol==0, f"{on_boundary} exactly on 1/b+1/c=1/a boundary")
unc=0; unc_both2=0
for a,b,c in iter_uncovered(300):
    unc+=1
    if (a//gcd(a,c))==2 and (b//gcd(b,c))==2:
        unc_both2+=1
        if unc_both2<=5: pr(f"   UNCOVERED both=2 a={a} b={b} c={c}")
check(f"Lemma4 (B) {unc} uncovered triples (a<=300): none has both ratios=2", unc_both2==0)
pr(el(),"check3 done")

# =====================================================================
pr("="*72); pr("CHECK 4  Lemma 5: s-2P=Xa+Xb+Xc identity; each X>=1, s-2P>=3 for n>=c;")
pr("  full period; n=c boundary. (integer-only, incremental)"); pr("="*72)
identity_bad=0; X_min=None; sm2P_min=None; nc_bad=0; tc=0
for a,b,c in iter_uncovered(12):
    Lab,Lac,Lbc = lcm(a,b),lcm(a,c),lcm(b,c); L=lcm(Lab,c); tc+=1
    for n in range(c, c+L):
        ta,tb,tcc=n//a,n//b,n//c
        pab,pac,pbc=n//Lab,n//Lac,n//Lbc
        s=ta+tb+tcc; P=pab+pac+pbc
        Xa=ta-pab-pac; Xb=tb-pab-pbc; Xc=tcc-pac-pbc
        if Xa+Xb+Xc != s-2*P: identity_bad+=1
        mn=min(Xa,Xb,Xc)
        if X_min is None or mn<X_min: X_min=mn
        if sm2P_min is None or (s-2*P)<sm2P_min: sm2P_min=s-2*P
        if n==c and (Xa<1 or Xb<1 or Xc<1 or (s-2*P)<3): nc_bad+=1
check("Lemma5 identity s-2P=Xa+Xb+Xc", identity_bad==0, f"exact over {tc} triples, full period")
check("Lemma5 each X>=1 (n>=c)", X_min>=1, f"min X={X_min}")
check("Lemma5 s-2P>=3 (n>=c)", sm2P_min>=3, f"min s-2P={sm2P_min}")
check("Lemma5 valid at n=c", nc_bad==0)
pr(el(),"check4 done")

# =====================================================================
pr("="*72); pr("CHECK 5  Theorem 8: 2B(n)>nS strict, uncovered a<=20, full period.")
pr("  integer-only: test 2*B(n)*Sden - n*Snum > 0. Tightest margin."); pr("="*72)
thm8_fail=0; best=None; best_at=None; tct=0; nchk=0
for a,b,c in iter_uncovered(20):
    Lab,Lac,Lbc=lcm(a,b),lcm(a,c),lcm(b,c); L=lcm(Lab,c); tct+=1
    Sden=lcm(lcm(a,b),c); Snum=Sden//a+Sden//b+Sden//c   # S=Snum/Sden
    # incremental B over the period
    B = (c//a+c//b+c//c) - (c//Lab+c//Lac+c//Lbc) + c//Sden  # B(c)
    tmin=None; tmin_n=None
    for n in range(c, c+L):
        if n>c:
            if n%a==0 or n%b==0 or n%c==0: B+=1
        g = 2*B*Sden - n*Snum        # >0 iff 2B(n)>nS
        nchk+=1
        if g<=0:
            thm8_fail+=1
            if thm8_fail<=5: pr(f"   THM8 FAIL {a,b,c} n={n} g={g}")
        if tmin is None or g<tmin: tmin=g; tmin_n=n
    # per-triple tightest margin = tmin/Sden ; compare globally as Fraction
    cand=Fraction(tmin, Sden)
    if best is None or cand<best: best=cand; best_at=(a,b,c,tmin_n)
check(f"Theorem 8 strict 2B(n)>nS ({tct} triples a<=20, {nchk} (triple,n) points)",
      thm8_fail==0, f"tightest 2B-nS={best} (~{float(best):.6f}) at (a,b,c,n)={best_at}")
pr(el(),"check5 done")

# =====================================================================
pr("="*72); pr("CHECK 6  Cor8'/Thm9: B(m)/m<=S for all m>=1 (incl m<c); (star) direct;")
pr("  small-core reduction."); pr("="*72)
# (a) union bound including m<c : B(m)*Sden <= m*Snum
ub_fail=0
for a,b,c in iter_uncovered(15):
    Lab,Lac,Lbc=lcm(a,b),lcm(a,c),lcm(b,c); Sden=lcm(Lab,c); Snum=Sden//a+Sden//b+Sden//c
    B=0
    for m in range(1, 3*c+1):
        if m%a==0 or m%b==0 or m%c==0: B+=1
        if B*Sden > m*Snum:
            ub_fail+=1
            if ub_fail<=5: pr(f"   UB FAIL {a,b,c} m={m}")
check("Cor8' B(m)/m<=S for m in [1,3c] (incl m<c)", ub_fail==0, "a<=15 uncovered")
# (b) direct (star): B(m)*n < 2*B(n)*m for m in (n, n+L], n in period; a<=6, L<=2000
star_fail=0; sct=0
for a,b,c in iter_uncovered(6):
    Lab,Lac,Lbc=lcm(a,b),lcm(a,c),lcm(b,c); L=lcm(Lab,c)
    if L>2000: continue
    sct+=1
    def Bf(x): return x//a+x//b+x//c-(x//Lab+x//Lac+x//Lbc)+x//L
    for n in range(c, c+L):
        Bn=Bf(n)
        for m in range(n+1, n+L+1):
            if Bf(m)*n >= 2*Bn*m:
                star_fail+=1
                if star_fail<=5: pr(f"   STAR FAIL {a,b,c} n={n} m={m}")
check(f"(star) B(m)n<2B(n)m direct ({sct} triples a<=6, n in period, m in (n,n+L])",
      star_fail==0)
# (c) small-core reduction: |A|>=3, primitive core size<=3
def B_of_set(A,x):
    A=sorted(set(A)); return sum(1 for k in range(1,x+1) if any(k%a==0 for a in A))
def core(A):
    A=sorted(set(A)); return [a for a in A if not any(a%d==0 and d<a for d in A)]
sc_fail=0
test_sets=[[3,4,6],[2,3,4,6],[6,10,15,30],[3,5,10,15],[4,6,8,9,12]]
for A in test_sets:
    mx=max(A)
    for n in range(mx, mx+50):
        Bn=B_of_set(A,n)
        for m in range(n+1, n+100):
            if B_of_set(A,m)*n >= 2*Bn*m:
                sc_fail+=1
                if sc_fail<=5: pr(f"   SMALLCORE FAIL A={A} core={core(A)} n={n} m={m}")
check("Small-core: |A|>=3, core<=3, (star) on n>=max(A)", sc_fail==0,
      "; ".join(f"{A}->{core(A)}" for A in test_sets))
pr(el(),"check6 done")

# =====================================================================
pr("="*72); pr("CHECK 7  Covered-zone: 2B(n)>nS there too? (Thm6 route claims yes)"); pr("="*72)
cov_fail=0; cov_cnt=0; cov_best=None
for a in range(2,16):
    for b in range(a+1,60):
        if b%a==0: continue
        for c in range(b+1,120):
            if c%a==0 or c%b==0: continue
            if a*c+a*b > b*c: continue        # skip uncovered -> want covered
            Lab,Lac,Lbc=lcm(a,b),lcm(a,c),lcm(b,c); L=lcm(Lab,c); cov_cnt+=1
            Sden=L; Snum=Sden//a+Sden//b+Sden//c
            step=max(1,L//300)
            for n in range(c,c+L,step):
                B=n//a+n//b+n//c-(n//Lab+n//Lac+n//Lbc)+n//L
                g=2*B*Sden-n*Snum
                cand=Fraction(g,Sden)
                if cov_best is None or cand<cov_best: cov_best=cand
                if g<=0: cov_fail+=1
check(f"Covered-zone 2B(n)>nS spot-check ({cov_cnt} covered triples)",
      cov_fail==0, f"min 2B-nS sampled={cov_best} (~{float(cov_best):.4f})")
pr(el(),"check7 done")

pr("="*72)
pr("OVERALL:", "ALL CHECKS PASS" if not fails else f"FAILURES -> {fails}")
pr("="*72)
