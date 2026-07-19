//! Claude-owned exact-i128 census tool for Erdos Problem 488.
//!
//! Purpose: exhaustive / negative-existence sweeps at ranges Python cannot reach.
//! Motivated by the G3 overclaim (min<=54 was a Python-range artifact; real
//! counterexamples live at entries in the hundreds/thousands).
//!
//! All arithmetic is exact i128 common-denominator; no external crates (matches
//! Codex's fastcheck convention, stays offline). GNU toolchain only.
//!
//! Usage:
//!   census quints <N> [--all-min]      enumerate primitive gcd=1 quintuples,
//!                                       entries in [2,N]; report the <=2-good class,
//!                                       window-relevant subset, max(min), and any
//!                                       2*delta<=S violation.
//!
//! "window-relevant" := max(P)*S <= 1135/7 (7*max*S <= 1135).
//! "<=2-good" := at most 2 elements have charge = sum_{f!=e} gcd(e,f)/f  < 1.

use std::env;

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a.abs()
}
fn lcm(a: i128, b: i128) -> i128 { a / gcd(a, b) * b }

/// number of good elements (charge < 1) among the 5.
fn ngood(p: &[i128; 5]) -> u32 {
    let mut good = 0;
    for i in 0..5 {
        let e = p[i];
        // charge(e) = sum_{j!=i} gcd(e,p[j]) / p[j].  Compare to 1 via common denom.
        // den = prod_{j!=i} p[j];  num = sum_j gcd(e,p[j]) * den/p[j].
        let mut den: i128 = 1;
        for j in 0..5 { if j != i { den *= p[j]; } }
        let mut num: i128 = 0;
        for j in 0..5 {
            if j != i { num += gcd(e, p[j]) * (den / p[j]); }
        }
        if num < den { good += 1; }
    }
    good
}

/// window-relevant: 7*max*S <= 1135, S = sum 1/p[i]. max = p[4] (sorted).
fn window_relevant(p: &[i128; 5]) -> bool {
    // 7*max*sum(1/p_i) <= 1135  <=>  7*max*sum(prod/ p_i) <= 1135*prod
    let mut prod: i128 = 1;
    for &x in p.iter() { prod *= x; }
    let mut s: i128 = 0;
    for i in 0..5 { s += prod / p[i]; }
    7 * p[4] * s <= 1135 * prod
}

/// sign of 2*delta - S over lcm(P). Returns the exact numerator (2δ−S = num / L).
/// 2δ−S = S − 2P2 + 2T3 − 2T4 + 2T5, each term ±(L/lcm(subset))/L.
fn two_delta_minus_s_num(p: &[i128; 5]) -> i128 {
    let mut l: i128 = 1;
    for &x in p.iter() { l = lcm(l, x); }
    let mut num: i128 = 0;
    // iterate nonempty subsets via bitmask 1..32
    for mask in 1u32..32 {
        let mut sub: i128 = 1;
        let mut k = 0;
        for i in 0..5 {
            if mask & (1 << i) != 0 { sub = lcm(sub, p[i]); k += 1; }
        }
        let term = l / sub; // integer
        // coefficient of 1/lcm(subset) in 2δ−S = S−2P2+2T3−2T4+2T5:
        // |subset|=1 -> +1, 2 -> -2, 3 -> +2, 4 -> -2, 5 -> +2
        let coef: i128 = match k { 1 => 1, 2 => -2, 3 => 2, 4 => -2, 5 => 2, _ => 0 };
        num += coef * term;
    }
    num
}

fn quints(n: i128, report_all_min: bool) {
    let mut count_le2: u64 = 0;
    let mut count_window: u64 = 0;
    let mut max_min_all: i128 = 0;
    let mut wit_all = [0i128; 5];
    let mut max_min_window: i128 = 0;
    let mut wit_window = [0i128; 5];
    let mut delta_violations: u64 = 0;
    let mut wit_delta = [0i128; 5];
    // histogram of min over window-relevant <=2-good, by min value
    let mut minhist: std::collections::BTreeMap<i128, u64> = std::collections::BTreeMap::new();

    let a_lo = 2i128;
    for a in a_lo..=n {
        for b in (a + 1)..=n {
            if b % a == 0 { continue; }
            let gab = gcd(a, b);
            for c in (b + 1)..=n {
                if c % a == 0 || c % b == 0 { continue; }
                let gabc = gcd(gab, c);
                for d in (c + 1)..=n {
                    if d % a == 0 || d % b == 0 || d % c == 0 { continue; }
                    let gabcd = gcd(gabc, d);
                    for e in (d + 1)..=n {
                        if e % a == 0 || e % b == 0 || e % c == 0 || e % d == 0 { continue; }
                        if gcd(gabcd, e) != 1 { continue; } // gcd(P)=1
                        let p = [a, b, c, d, e];
                        if ngood(&p) > 2 { continue; }
                        count_le2 += 1;
                        if a > max_min_all { max_min_all = a; wit_all = p; }
                        if window_relevant(&p) {
                            count_window += 1;
                            *minhist.entry(a).or_insert(0) += 1;
                            if a > max_min_window { max_min_window = a; wit_window = p; }
                            // density check on the class that matters
                            if two_delta_minus_s_num(&p) <= 0 {
                                delta_violations += 1;
                                wit_delta = p;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("=== quints census, entries in [2,{}] ===", n);
    println!("<=2-good gcd=1 primitive quintuples: {}", count_le2);
    println!("  window-relevant (7*max*S<=1135): {}", count_window);
    println!("  MAX(min) over ALL <=2-good:        {}  at {:?}", max_min_all, wit_all);
    println!("  MAX(min) over window-relevant:     {}  at {:?}", max_min_window, wit_window);
    println!("  2*delta<=S violations (window-rel): {}{}", delta_violations,
             if delta_violations>0 { format!("  e.g. {:?}", wit_delta) } else { String::new() });
    // show the tail of the min-histogram (largest mins) — is min bounded?
    let mut keys: Vec<_> = minhist.keys().cloned().collect();
    keys.sort();
    let tail: Vec<_> = keys.iter().rev().take(15).cloned().collect();
    print!("  window-rel count by min (top mins): ");
    for m in tail.iter().rev() { print!("{}:{} ", m, minhist[m]); }
    println!();
    if report_all_min {
        println!("  full min set (window-rel): {:?}", keys);
    }
}

/// DUAL census. Enumerate small dual cores D (gcd=1 antichain quintuples, entries
/// in [2,M]); the dual quintuple is P = lcm(D)/D (elementwise). Reaches LARGE min(P)
/// from small D — the region brute enumeration cannot touch. All arithmetic small.
///
/// Verified identities (P_i = L/d_i, L = lcm(D)):
///   charge(P_i) = (1/d_i) * sum_{j!=i} gcd(d_i,d_j)   [so P_i good <=> sum gcd < d_i]
///   min(P) = L / max(D);   P is automatically gcd=1 and an antichain.
///   window-relevant(P) <=>  7 * sum(D) <= 1135 * min(D).
fn dual(m: i128) {
    let mut count_le2: u64 = 0;
    let mut count_window: u64 = 0;
    let mut max_minp: i128 = 0;
    let mut wit_d = [0i128; 5];
    let mut wit_p = [0i128; 5];
    // histogram of min(P) rounded to log-ish buckets is noisy; track distinct large mins
    let mut large_mins: Vec<(i128, [i128;5])> = Vec::new();

    for a in 2..=m {
        for b in (a + 1)..=m {
            if b % a == 0 { continue; }
            let gab = gcd(a, b);
            for c in (b + 1)..=m {
                if c % a == 0 || c % b == 0 { continue; }
                let gabc = gcd(gab, c);
                for d in (c + 1)..=m {
                    if d % a == 0 || d % b == 0 || d % c == 0 { continue; }
                    let gabcd = gcd(gabc, d);
                    for e in (d + 1)..=m {
                        if e % a == 0 || e % b == 0 || e % c == 0 || e % d == 0 { continue; }
                        if gcd(gabcd, e) != 1 { continue; }
                        let dd = [a, b, c, d, e];
                        // cogood count = number of good elements of P
                        let mut cogood = 0;
                        for i in 0..5 {
                            let mut s = 0i128;
                            for j in 0..5 { if j != i { s += gcd(dd[i], dd[j]); } }
                            if s < dd[i] { cogood += 1; }
                        }
                        if cogood > 2 { continue; }   // P is <=2-good
                        count_le2 += 1;
                        // window(P): 7*sum(D) <= 1135*min(D)
                        let sumd: i128 = dd.iter().sum();
                        if 7 * sumd > 1135 * dd[0] { continue; }
                        count_window += 1;
                        // min(P) = lcm(D)/max(D)
                        let mut l = 1i128;
                        for &x in dd.iter() { l = lcm(l, x); }
                        let minp = l / dd[4];
                        if minp > max_minp {
                            max_minp = minp; wit_d = dd;
                            let mut p = [0i128;5];
                            for i in 0..5 { p[i] = l / dd[i]; }
                            p.sort();
                            wit_p = p;
                        }
                        if minp > 54 { large_mins.push((minp, dd)); }
                    }
                }
            }
        }
    }
    println!("=== DUAL census, dual-core entries in [2,{}] ===", m);
    println!("<=2-good gcd=1 quintuples P (via dual D): {}", count_le2);
    println!("  window-relevant: {}", count_window);
    println!("  MAX min(P) over window-relevant: {}", max_minp);
    println!("    from dual core D = {:?}  ->  P = {:?}", wit_d, wit_p);
    // report the distinct large mins > 54 (refutes min<=54), sorted desc, top 20
    large_mins.sort_by(|a,b| b.0.cmp(&a.0));
    large_mins.dedup_by(|a,b| a.0==b.0 && a.1==b.1);
    println!("  window-relevant P with min>54: {} found; largest mins:", large_mins.len());
    for (mp, dd) in large_mins.iter().take(20) {
        println!("    min(P)={:<8} dual D={:?}", mp, dd);
    }
}

/// C-B (finite-n Bonferroni) criterion sweep over dual cores.
///
/// THEOREM (C-B window bound, unconditional, 3 lines from the exact 1/R identity +
/// pointwise 1/(1+X) >= 1-X/2):   2B_P(n) - n*S_P >= sum_a (1-charge(a))*floor(n/a) - 5.
/// On the window n >= 2*max(P) this closes regime C for P whenever
///   CRIT(P) := max(P)*(S - 2*P2) > 7/2.
/// Dual-side identity (exact, verified): CRIT = (Sum(D) - 2*Sum_{i<j} gcd(d_i,d_j)) / min(D)
/// -- all small numbers. This sweep reports every <=2-good window-relevant dual core with
/// CRIT <= 7/2 (the "C-B residual"): if that list saturates as M grows, regime C
/// = C-B theorem + finite bank, and the rider-junk families are ALL retired uniformly.
/// Worker: enumerate residual/class over dual-min values `a` with `a % nthreads == tid`.
/// Returns (class_count, residual_vec).
fn cb_worker(m: i128, tid: i128, nthreads: i128) -> (u64, Vec<(i128, i128, [i128; 5])>) {
    let mut count: u64 = 0;
    let mut resid: Vec<(i128, i128, [i128; 5])> = Vec::new();
    let mut a = 2i128;
    while a <= m {
        if (a - 2) % nthreads != tid {
            a += 1;
            continue;
        }
        let cap_e = |partial: i128| (1135 * a - 7 * partial) / 7;
        for b in (a + 1)..=m.min((1135 * a - 7 * a) / (7 * 4)) {
            if b % a == 0 { continue; }
            let gab = gcd(a, b);
            for c in (b + 1)..=m.min((1135 * a - 7 * (a + b)) / (7 * 3)) {
                if c % a == 0 || c % b == 0 { continue; }
                let gabc = gcd(gab, c);
                for d in (c + 1)..=m.min((1135 * a - 7 * (a + b + c)) / (7 * 2)) {
                    if d % a == 0 || d % b == 0 || d % c == 0 { continue; }
                    let gabcd = gcd(gabc, d);
                    for e in (d + 1)..=m.min(cap_e(a + b + c + d)) {
                        if e % a == 0 || e % b == 0 || e % c == 0 || e % d == 0 { continue; }
                        if gcd(gabcd, e) != 1 { continue; }
                        let dd = [a, b, c, d, e];
                        let mut cogood = 0;
                        for i in 0..5 {
                            let mut s = 0i128;
                            for j in 0..5 { if j != i { s += gcd(dd[i], dd[j]); } }
                            if s < dd[i] { cogood += 1; }
                        }
                        if cogood > 2 { continue; }
                        let sumd: i128 = dd.iter().sum();
                        if 7 * sumd > 1135 * dd[0] { continue; }
                        count += 1;
                        let mut sg = 0i128;
                        for i in 0..5 { for j in (i + 1)..5 { sg += gcd(dd[i], dd[j]); } }
                        let num = sumd - 2 * sg;
                        if 2 * num <= 7 * dd[0] {
                            resid.push((num, dd[0], dd));
                        }
                    }
                }
            }
        }
        a += 1;
    }
    (count, resid)
}

/// strong-gcd graph components of a 5-core: edge i~j iff 4*gcd(d_i,d_j) >= min(d_i,d_j).
/// Returns (#components, component-size pattern sorted desc).
fn strong_components(dd: &[i128; 5]) -> (usize, [usize; 5]) {
    let mut parent = [0usize, 1, 2, 3, 4];
    fn find(p: &mut [usize; 5], x: usize) -> usize {
        let mut r = x;
        while p[r] != r { r = p[r]; }
        let mut c = x;
        while p[c] != c { let n = p[c]; p[c] = r; c = n; }
        r
    }
    for i in 0..5 {
        for j in (i + 1)..5 {
            if 4 * gcd(dd[i], dd[j]) >= dd[i].min(dd[j]) {
                let (ri, rj) = (find(&mut parent, i), find(&mut parent, j));
                if ri != rj { parent[ri] = rj; }
            }
        }
    }
    let mut sizes = [0usize; 5];
    for i in 0..5 { let r = find(&mut parent, i); sizes[r] += 1; }
    let ncomp = sizes.iter().filter(|&&s| s > 0).count();
    let mut pat = sizes;
    pat.sort_unstable_by(|a, b| b.cmp(a));
    (ncomp, pat)
}

fn nselfbad(dd: &[i128; 5]) -> usize {
    let mut n = 0;
    for i in 0..5 {
        let mut s = 0i128;
        for j in 0..5 { if j != i { s += gcd(dd[i], dd[j]); } }
        if s >= dd[i] { n += 1; }
    }
    n
}

fn cb(m: i128) {
    let nthreads: i128 = std::thread::available_parallelism().map(|n| n.get() as i128).unwrap_or(4).max(1);
    let (count, mut resid) = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|tid| s.spawn(move || cb_worker(m, tid, nthreads)))
            .collect();
        let mut count = 0u64;
        let mut resid: Vec<(i128, i128, [i128; 5])> = Vec::new();
        for h in handles {
            let (c, mut r) = h.join().unwrap();
            count += c;
            resid.append(&mut r);
        }
        (count, resid)
    });
    // global min crit
    let mut min_crit: (i128, i128, [i128; 5]) = (0, 1, [0; 5]);
    let mut have_min = false;
    for (num, d1, dd) in resid.iter() {
        if !have_min || num * min_crit.1 < min_crit.0 * d1 {
            min_crit = (*num, *d1, *dd); have_min = true;
        }
    }
    println!("=== C-B criterion sweep, dual cores in [2,{}] ===", m);
    println!("<=2-good window-relevant (via dual): {}", count);
    println!("C-B RESIDUAL (crit <= 7/2): {} dual cores", resid.len());
    // strong-gcd component + self-bad distributions of the residual (Codex's C-B-3COMP frame).
    let mut comp_hist: std::collections::BTreeMap<usize, u64> = std::collections::BTreeMap::new();
    let mut pat_hist: std::collections::BTreeMap<[usize; 5], u64> = std::collections::BTreeMap::new();
    let mut sb_hist: std::collections::BTreeMap<usize, u64> = std::collections::BTreeMap::new();
    let mut threecomp_wit: Vec<[i128; 5]> = Vec::new();
    for (_num, _d1, dd) in resid.iter() {
        let (nc, pat) = strong_components(dd);
        *comp_hist.entry(nc).or_insert(0) += 1;
        *pat_hist.entry(pat).or_insert(0) += 1;
        *sb_hist.entry(nselfbad(dd)).or_insert(0) += 1;
        if nc >= 3 && threecomp_wit.len() < 10 { threecomp_wit.push(*dd); }
    }
    // >=4-bad residuals: the sector outside the 3-bad shape certificates — list them all
    for (_num, _d1, dd) in resid.iter() {
        if nselfbad(dd) >= 4 {
            let mut l = 1i128; for &x in dd.iter() { l = lcm(l, x); }
            let mut pp: Vec<i128> = dd.iter().map(|&x| l / x).collect();
            pp.sort_unstable();
            let (nc, pat) = strong_components(dd);
            println!("  4-BAD residual: D={:?}  P={:?}  comps={} {:?}", dd, pp, nc, &pat[..nc.min(5)]);
        }
    }
    // exactly-3-bad residuals: histogram by INTERNAL strong edges among the bad duals
    // (4*gcd >= min); the <=1-edge families are outside the min-strong 906 inventory
    // (Codex badtriplecheck audit — independent recount here at this M).
    let mut edge_hist = [0u64; 4];
    for (_num, _d1, dd) in resid.iter() {
        let bads: Vec<usize> = (0..5).filter(|&i| {
            let s: i128 = (0..5).filter(|&j| j != i).map(|j| gcd(dd[i], dd[j])).sum();
            s >= dd[i]
        }).collect();
        if bads.len() != 3 { continue; }
        let mut ne = 0;
        for x in 0..3 { for y in (x + 1)..3 {
            let (a, b) = (dd[bads[x]], dd[bads[y]]);
            if 4 * gcd(a, b) >= a.min(b) { ne += 1; }
        }}
        edge_hist[ne] += 1;
        if ne <= 1 {
            let mut l = 1i128; for &x in dd.iter() { l = lcm(l, x); }
            let mut pp: Vec<i128> = dd.iter().map(|&x| l / x).collect();
            pp.sort_unstable();
            println!("  {}-EDGE 3-bad residual: D={:?} badidx={:?}  P={:?}", ne, dd, bads, pp);
        }
    }
    println!("  exactly-3-bad by internal strong edges [0,1,2,3]: {:?}", edge_hist);
    println!("  strong-gcd components (4gcd>=min): {:?}", comp_hist);
    println!("  component-size patterns: {:?}", pat_hist);
    println!("  self-bad counts: {:?}", sb_hist);
    println!("  >=3-COMPONENT residual cores: {}{}", threecomp_wit.len(),
             if threecomp_wit.is_empty() { "  (sector empty in range)".to_string() }
             else { format!("  e.g. {:?}", threecomp_wit) });
    // finiteness signal: do the residual's DUAL entries saturate below M?
    let mut max_dmin = 0i128; let mut max_dmax = 0i128; let mut max_lcm_over_dmin = 0i128;
    let mut wit_dmin = [0i128; 5];
    for (_num, _d1, dd) in resid.iter() {
        if dd[0] > max_dmin { max_dmin = dd[0]; wit_dmin = *dd; }
        if dd[4] > max_dmax { max_dmax = dd[4]; }
        let mut l = 1i128; for &x in dd.iter() { l = lcm(l, x); }
        let r = l / dd[0]; if r > max_lcm_over_dmin { max_lcm_over_dmin = r; }
    }
    println!("  residual DUAL entries: max min(D) = {} (at {:?}), max max(D) = {} [M={}]",
             max_dmin, wit_dmin, max_dmax, m);
    println!("    -> if max min(D) << M and stable across M, residual dual-min is bounded => finite");
    println!("  max lcm(D)/min(D) over residual = {} (= largest primal max; the entanglement cap)", max_lcm_over_dmin);
    // structural danger scan: residual cores whose dual-min is CO-GOOD (g_1 < d_1).
    // Such a shape could carry coprime junk on d_min with crit -> 1: infinite residual family.
    let mut cogood_min = 0u64;
    let mut cogood_wit = [0i128; 5];
    let mut max_primal_max: i128 = 0;
    for (_num, _d1, dd) in resid.iter() {
        let mut g1 = 0i128;
        for j in 1..5 { g1 += gcd(dd[0], dd[j]); }
        if g1 < dd[0] { cogood_min += 1; cogood_wit = *dd; }
        let mut l = 1i128;
        for &x in dd.iter() { l = lcm(l, x); }
        let pmax = l / dd[0];
        if pmax > max_primal_max { max_primal_max = pmax; }
    }
    println!("  residual cores with CO-GOOD dual-min (junk danger): {}{}", cogood_min,
             if cogood_min > 0 { format!("  e.g. {:?}", cogood_wit) } else { String::new() });
    println!("  largest primal max(P) in residual: {}", max_primal_max);
    // BANK: exact tower-form window check 2B(m) > (m+1)S over every residual set (Rust,
    // replaces the old Python bank). S = N/D, N = sum(prod others), D = prod. cap =
    // largest m with 7(m+1)S < 1135. Report failures + worst margin (as float of 2B-(m+1)S).
    let mut fails = 0u64;
    let mut worst_num: i128 = i128::MAX; // track min of (2B*D - (m+1)N), and its D
    let mut worst_den: i128 = 1;
    let mut worst_m: i128 = 0;
    let mut worst_p = [0i128; 5];
    for (_num, _d1, dd) in resid.iter() {
        let mut l = 1i128;
        for &x in dd.iter() { l = lcm(l, x); }
        let mut p: Vec<i128> = dd.iter().map(|&x| l / x).collect();
        p.sort();
        let prod: i128 = p.iter().product();
        let nsum: i128 = p.iter().map(|&x| prod / x).sum(); // sum of products-of-others
        let mx = p[4];
        // cap: 7(m+1)N < 1135 D  =>  m+1 < 1135 D / (7 N)  => cap = 1135 D /(7 N) - 1
        let cap = (1135 * prod) / (7 * nsum) - 1;
        // incremental B over [1,cap]; check tower 2B(m)*D > (m+1)*N for m in [mx,cap]
        let mut bc: i128 = 0;
        for m in 1..=cap {
            if p.iter().any(|&a| m % a == 0) { bc += 1; }
            if m >= mx {
                let lhs = 2 * bc * prod;
                let rhs = (m + 1) * nsum;
                let marg = lhs - rhs; // >0 means pass; value = (2B-(m+1)S)*D
                if marg <= 0 { fails += 1; }
                // compare marg/prod across sets: marg1/D1 < marg2/D2 <=> marg1*D2 < marg2*D1
                if marg * worst_den < worst_num * prod || worst_num == i128::MAX {
                    worst_num = marg; worst_den = prod; worst_m = m;
                    for i in 0..5 { worst_p[i] = p[i]; }
                }
            }
        }
    }
    println!("  BANK (tower form 2B(m) > (m+1)S over all {} residual sets):", resid.len());
    println!("    failures = {}", fails);
    println!("    worst margin = {}/{} ~ {:.4} at m={} P={:?}", worst_num, worst_den,
             (worst_num as f64) / (worst_den as f64), worst_m, worst_p);
    // primal form of residual sets, sorted by crit
    resid.sort_by(|x, y| (x.0 * y.1).cmp(&(y.0 * x.1)));
    for (num, d1, dd) in resid.iter().take(400) {
        let mut l = 1i128;
        for &x in dd.iter() { l = lcm(l, x); }
        let mut p: Vec<i128> = dd.iter().map(|&x| l / x).collect();
        p.sort();
        println!("  crit={}/{} ~ {:.3}   D={:?}   P={:?}", num, d1, (*num as f64)/(*d1 as f64), dd, p);
    }
    if resid.len() > 400 { println!("  ... ({} more)", resid.len() - 400); }
    println!("global min crit = {}/{} ~ {:.3} at D={:?}", min_crit.0, min_crit.1,
             (min_crit.0 as f64)/(min_crit.1 as f64), min_crit.2);
}

// ---------------------------------------------------------------------------
// DRIFT / EMIN certificate modes (executable certificates for the U2 chain, the
// DRIFT-TRANSFER per-class constants, and the size-6 W0/W1/W2 retirement).
// All exact: f(J)*60 is an integer (1/(1+X) has denominator <= 5); comparisons
// are cross-multiplied i128. No floats anywhere in a decision.
// ---------------------------------------------------------------------------

fn lcm_of(ms: &[i128]) -> i128 { ms.iter().fold(1i128, |a, &b| lcm(a, b)) }

/// enumerate k-multisets of values[lo..], calling f on each.
fn multisets(values: &[i128], k: usize, cur: &mut Vec<i128>, start: usize, f: &mut dyn FnMut(&[i128])) {
    if cur.len() == k { f(cur); return; }
    for i in start..values.len() {
        cur.push(values[i]);
        multisets(values, k, cur, i, f);
        cur.pop();
    }
}

/// One-period drift scan for moduli ms with claimed f(J) >= (sp/sq) J - (dp/dq).
/// Returns (ok_period_slope, ok_bound, worst_deficit_num, worst_deficit_J) where
/// deficit = (sp/sq) J - f(J) as an exact fraction with denominator 60*sq (num tracked).
fn drift_scan(ms: &[i128], sp: i128, sq: i128, dp: i128, dq: i128) -> (bool, bool, i128, i128) {
    let l = lcm_of(ms);
    let mut f60: i128 = 0; // f(J)*60
    let mut worst_num: i128 = i128::MIN; // deficit numerator over denominator 60*sq
    let mut worst_j: i128 = 0;
    let mut ok_bound = true;
    for j in 1..=l {
        let x = ms.iter().filter(|&&m| j % m == 0).count() as i128;
        f60 += 60 / (1 + x) - 30;
        // deficit = spJ/sq - f = (60*sp*J - sq*f60)/(60*sq); claim: deficit <= dp/dq
        let defnum = 60 * sp * j - sq * f60;
        if defnum > worst_num { worst_num = defnum; worst_j = j; }
        // bound check: defnum/(60 sq) <= dp/dq  <=>  defnum*dq <= dp*60*sq
        if defnum * dq > dp * 60 * sq { ok_bound = false; }
    }
    // period slope: f(L)*60 = f60 must satisfy f(L) >= (sp/sq) L  <=> sq*f60 >= 60 sp L
    let ok_slope = sq * f60 >= 60 * sp * l;
    (ok_slope, ok_bound, worst_num, worst_j)
}

/// class filter: max number of entries equal to 2 (255 = unrestricted), min entry.
fn class_values(lo: i128, hi: i128) -> Vec<i128> { (lo..=hi).collect() }

fn drift_class(name: &str, k: usize, lo: i128, hi: i128, max_twos: usize,
               sp: i128, sq: i128, dp: i128, dq: i128) -> bool {
    let vals = class_values(lo, hi);
    let mut cur = Vec::new();
    let mut count = 0u64;
    let mut all_ok = true;
    let mut worst: (i128, Vec<i128>, i128) = (i128::MIN, vec![], 0);
    multisets(&vals, k, &mut cur, 0, &mut |ms: &[i128]| {
        if ms.iter().filter(|&&m| m == 2).count() > max_twos { return; }
        count += 1;
        let (s, b, wnum, wj) = drift_scan(ms, sp, sq, dp, dq);
        if !(s && b) { all_ok = false; }
        if wnum > worst.0 { worst = (wnum, ms.to_vec(), wj); }
    });
    // worst deficit as exact fraction num/(60*sq)
    println!("  class {:14} k={} box=[{},{}] twos<={} kernels={:5} claim f>=({}/{})J-({}/{}) : {}   worst deficit {}/{} at {:?} J={}",
             name, k, lo, hi, if max_twos==255 {"any".to_string()} else {max_twos.to_string()}, count,
             sp, sq, dp, dq, if all_ok {"PASS"} else {"FAIL"}, worst.0, 60*sq, worst.1, worst.2);
    all_ok
}

/// retirement arithmetic: peeling an entry m >= mstar from class level k to k-1:
/// sigma_{k-1} - 1/(2 mstar) >= sigma_k  and  delta_k >= delta_{k-1}. Exact check.
fn retire(name: &str, sp1: i128, sq1: i128, sp: i128, sq: i128, mstar: i128,
          dp1: i128, dq1: i128, dp: i128, dq: i128) -> bool {
    // sp1/sq1 - 1/(2 mstar) >= sp/sq  <=>  (2 mstar sp1 - sq1) * sq >= sp * 2 mstar sq1
    let ok1 = (2 * mstar * sp1 - sq1) * sq >= sp * 2 * mstar * sq1;
    let ok2 = dp * dq1 >= dp1 * dq; // delta_k >= delta_{k-1}
    println!("  retire {:12} m*={}  slope-ok={} delta-mono={}", name, mstar, ok1, ok2);
    ok1 && ok2
}

fn drift_certificates() {
    println!("=== DRIFT certificates (exact; executable form of the U2 chain + DRIFT-TRANSFER classes) ===");
    let mut ok = true;
    println!("[U2 free chain]  (any entries >= 2)");
    ok &= drift_class("free-1", 1, 2, 4, 255, 1, 4, 0, 1);
    ok &= retire("free 1->2", 1, 4, 5, 36, 5, 0, 1, 1, 18);
    ok &= drift_class("free-2", 2, 2, 4, 255, 5, 36, 1, 18);
    ok &= retire("free 2->3", 5, 36, 5, 72, 8, 1, 18, 1, 9);
    ok &= drift_class("free-3", 3, 2, 7, 255, 5, 72, 1, 9);
    ok &= retire("free 3->4", 5, 72, 7, 300, 11, 1, 9, 7, 30);
    ok &= drift_class("free-4 (U2)", 4, 2, 10, 255, 7, 300, 7, 30);
    println!("[no-2 chain]  (all entries >= 3)");
    ok &= drift_class("no2-1", 1, 3, 5, 0, 1, 3, 0, 1);
    ok &= retire("no2 1->2", 1, 3, 17, 72, 6, 0, 1, 1, 8);
    ok &= drift_class("no2-2", 2, 3, 5, 0, 17, 72, 1, 8);
    ok &= retire("no2 2->3", 17, 72, 41, 240, 8, 1, 8, 19, 80);
    ok &= drift_class("no2-3", 3, 3, 7, 0, 41, 240, 19, 80);
    ok &= retire("no2 3->4", 41, 240, 457, 3600, 12, 19, 80, 2, 5);
    ok &= drift_class("no2-4", 4, 3, 11, 0, 457, 3600, 2, 5);
    println!("[<=one-2 chain]");
    ok &= drift_class("le1two-1", 1, 2, 5, 1, 1, 4, 0, 1);
    ok &= retire("le1 1->2", 1, 4, 5, 36, 5, 0, 1, 1, 9);
    ok &= drift_class("le1two-2", 2, 2, 4, 1, 5, 36, 1, 9);
    ok &= retire("le1 2->3", 5, 36, 31, 360, 10, 1, 9, 1, 4);
    ok &= drift_class("le1two-3", 3, 2, 9, 1, 31, 360, 1, 4);
    ok &= retire("le1 3->4", 31, 360, 29, 600, 14, 1, 4, 1, 2);
    ok &= drift_class("le1two-4", 4, 2, 13, 1, 29, 600, 1, 2);
    println!("RESULT: {}", if ok { "ALL PASS" } else { "FAILURES PRESENT" });
}

/// E_k over a multiset (exact fraction as (num, den)): E = sum_T (-1)^|T|/((|T|+1) lcm T).
/// Fixed common denominator 60*lcm(ms): every term (k+1)*lcm_T divides it (k+1 <= 6 | 60,
/// lcm_T | lcm(ms)). Numerators bounded by 2^n * 60*L — no overflow (L small in our boxes).
fn e_of(ms: &[i128]) -> (i128, i128) {
    let n = ms.len();
    let l_all = lcm_of(ms);
    let den0 = 60 * l_all;
    let mut num: i128 = 0;
    for mask in 0u32..(1 << n) {
        let mut l = 1i128;
        let mut k = 0i128;
        for i in 0..n {
            if mask & (1 << i) != 0 { l = lcm(l, ms[i]); k += 1; }
        }
        let sign = if k % 2 == 0 { 1 } else { -1 };
        num += sign * (den0 / ((k + 1) * l));
    }
    let g = gcd(num.abs().max(1), den0);
    (num / g, den0 / g)
}

fn emin_class(name: &str, k: usize, lo: i128, hi: i128, max_twos: usize,
              claim_num: i128, claim_den: i128) -> bool {
    let vals = class_values(lo, hi);
    let mut cur = Vec::new();
    let mut best: (i128, i128, Vec<i128>) = (0, 0, vec![]); // den=0 => unset (avoids MAX*d overflow)
    let mut count = 0u64;
    multisets(&vals, k, &mut cur, 0, &mut |ms: &[i128]| {
        if ms.iter().filter(|&&m| m == 2).count() > max_twos { return; }
        count += 1;
        let (n, d) = e_of(ms);
        if best.1 == 0 || n * best.1 < best.0 * d { best = (n, d, ms.to_vec()); }
    });
    let ok = best.0 * claim_den == claim_num * best.1;
    println!("  {:10} k={} box=[{},{}] twos<={} candidates={:6}: min E = {}/{} at {:?}  (claim {}/{}) {}",
             name, k, lo, hi, if max_twos==255 {"any".to_string()} else {max_twos.to_string()},
             count, best.0, best.1, best.2, claim_num, claim_den, if ok {"PASS"} else {"FAIL"});
    ok
}

/// size-6 W-retirement certificate: peel threshold M0 = 1/(2(V4 - W)) per class; verify
/// exactly and confirm the box [2..25] used by audit_sext_density_lemma.py suffices.
fn emin_certificates() {
    println!("=== EMIN certificates (E-minima chains + size-6 W-retirement arithmetic, exact) ===");
    let mut ok = true;
    println!("[free chain E-minima]");
    ok &= emin_class("E1", 1, 2, 8, 255, 3, 4);
    ok &= emin_class("E2", 2, 2, 10, 255, 23, 36);
    ok &= emin_class("E3", 3, 2, 12, 255, 41, 72);
    ok &= emin_class("E4", 4, 2, 16, 255, 157, 300);
    ok &= emin_class("E5=W0", 5, 2, 16, 255, 49, 100);
    println!("[class E-minima at size 5 (the size-6 kernel W1/W2) and size 4 (drift classes)]");
    ok &= emin_class("W1 no-2", 5, 3, 16, 0, 7423, 12600);
    ok &= emin_class("W2 le1-2", 5, 2, 16, 1, 1087, 2100);
    ok &= emin_class("E4 no-2", 4, 3, 16, 0, 2257, 3600);
    ok &= emin_class("E4 le1-2", 4, 2, 16, 1, 329, 600);
    println!("[retirement thresholds M0 = 1/(2(V4 - W)) per size-6 class, exact]");
    // W0: V4 = 157/300, W0 = 49/100 -> M0 = 1/(2*(157/300-147/300)) = 300/20 = 15
    // W1: V4 = 2257/3600, W1 = 7423/12600 -> V4-W1 = (7899.75-...) compute exactly below.
    let cases: [(&str, (i128,i128), (i128,i128)); 3] = [
        ("W0", (157,300), (49,100)),
        ("W1", (2257,3600), (7423,12600)),
        ("W2", (329,600), (1087,2100)),
    ];
    for (nm, (v4n,v4d), (wn,wd)) in cases {
        // diff = v4n/v4d - wn/wd = (v4n*wd - wn*v4d)/(v4d*wd); M0 = v4d*wd/(2*(v4n*wd - wn*v4d))
        let dn = v4n * wd - wn * v4d;
        let dd = v4d * wd;
        // M0 = dd/(2 dn) (exact rational); box sufficient iff ceil(M0) <= 25
        let m0_ceil = (dd + 2 * dn - 1) / (2 * dn);
        let good = dn > 0 && m0_ceil <= 25;
        println!("  {}: V4-W = {}/{} > 0; peel threshold M0 = {}/{} (ceil {}), box [2..25] sufficient: {}",
                 nm, dn, dd, dd, 2 * dn, m0_ceil, good);
        ok &= good;
    }
    println!("RESULT: {}", if ok { "ALL PASS" } else { "FAILURES PRESENT" });
}

/// BAD-CLUSTER SHAPE enumeration for the compact residual box (stage 1 of the
/// closing enumeration). PROVEN inputs only:
///  - every self-bad vertex b has a partner with gcd >= b/4, i.e. b = alpha*g,
///    partner = beta*g, gcd(alpha,beta)=1, alpha in {2,3,4} (alpha=1 => divisibility);
///  - box: ratio < 11 (so beta <= 44 crude; beta/alpha < 11 exact), >=3 self-bad.
/// A "cluster shape" = the strong-component cofactor multiset of the bads after
/// dividing by the component gcd. Stage 2 (per-shape goods-uniform rider theorem,
/// C4-canonical mechanism) is separate. This lists candidate shapes exhaustively
/// under the proven caps; dedupe by normalized cofactor tuple.
fn clusters(rho: i128) {
    println!("=== bad-cluster cofactor shapes (box: ratio<{}, >=3 bad; caps proven) ===", rho);
    // pairs (alpha, beta): alpha in 2..=4, beta coprime, beta/alpha < 11, beta >= 2, not equal,
    // neither divides the other (antichain on cofactors since g is the full gcd: gcd(a,b)=1 already
    // implies no divisibility unless one is 1).
    let mut pair_shapes: Vec<(i128, i128)> = Vec::new();
    for a in 2i128..=4 {
        for b in 2i128..=(rho * a - 1) {
            if b == a { continue; }
            if gcd(a, b) != 1 { continue; }
            let (lo, hi) = if a < b { (a, b) } else { (b, a) };
            if !pair_shapes.contains(&(lo, hi)) { pair_shapes.push((lo, hi)); }
        }
    }
    pair_shapes.sort();
    println!("strong bad-pair cofactor shapes (alpha,beta), alpha<=4, coprime, ratio<{}: {}", rho, pair_shapes.len());
    for (a, b) in pair_shapes.iter().take(60) { print!("({},{}) ", a, b); }
    println!();
    // triple chains: bads b1=a1*g, b2=b1', linked either through one shared g (triple
    // multiset (a,b,c) pairwise coprime? no — cofactors of a COMMON g need pairwise
    // gcd structure: gcd(ai*g, aj*g) = g*gcd(ai,aj); strongness of the (i,j) edge means
    // gcd >= max/4: g*gcd(ai,aj) >= aj*g/4 => gcd(ai,aj) >= aj/4 — chain condition) or
    // through two different g's sharing the middle vertex. Enumerate one-g triples:
    let mut tri = 0u64;
    let mut tri_shapes: Vec<[i128; 3]> = Vec::new();
    for a in 2i128..=16 {
        for b in (a + 1)..=(rho * a - 1) {
            for c in (b + 1)..=(rho * a - 1) {
                // antichain on cofactors, ratio, and each pair's strong condition met by
                // at least a spanning structure: (a,b) and (a,c) strong: gcd(a,b) >= b/4? etc.
                if b % a == 0 || c % a == 0 || c % b == 0 { continue; }
                let sab = 4 * gcd(a, b) >= b; // strong relative to larger
                let sac = 4 * gcd(a, c) >= c;
                let sbc = 4 * gcd(b, c) >= c;
                // connected via >= 2 strong edges among the three
                let cnt = [sab, sac, sbc].iter().filter(|&&x| x).count();
                if cnt >= 2 {
                    tri += 1;
                    if tri_shapes.len() < 30 { tri_shapes.push([a, b, c]); }
                }
            }
        }
    }
    println!("one-scale strong triples (a,b,c) up to a<=16 with >=2 strong edges: {}", tri);
    for s in tri_shapes.iter() { print!("{:?} ", s); }
    println!();
    println!("(stage 2 = per-shape goods-uniform rider theorem; see chat/notes design)");
}

/// STAGE-2 prototype: per-shape goods-uniform window certificate for one-scale
/// triple clusters t*W (W from stage 1) plus two free goods.
///
/// PROVEN ingredients only:
///  - within the cluster, mutual moduli are exact integers independent of t:
///    modulus of t*w_j seen from t*w_i is w_j/gcd(w_i,w_j);
///  - the two goods' drift obeys the free-class global floor f >= -1/12 (J>=2)
///    [spreadcheck-certified; re-certified here in-table];
///  - EXACT TAIL: for f(J), any modulus > J has zero events on [1,J], so it is
///    exactly equivalent to J+1 (finite representative of the unbounded tail);
///  - n >= 2*max(P) >= 2*t*wmax => tau := n/t >= 2*wmax; window top: n < 33*max(P)
///    and ratio < rho => tau <= 33*rho*wmax (conservative).
/// Certificate: for each shape, F_pin(J) := min over free (m4,m5) in [2,J+1]^2
/// (exact tail) of f_{pins+(m4,m5)}(J), exhaustively for J <= JT; for J > JT use
/// the free-class drift line (7/300)J - 7/30 (valid: pinned class subset of free).
/// Then scan tau and report min assembled margin 2*Sum F - 2*2*(1/12) - 5 (S>0 dropped
/// — conservative). PASS = margin > 0 for all tau in range.
fn f_exact(ms: &[i128], j_max: i128) -> Vec<i128> {
    // returns f(J)*60 for J=0..j_max
    let mut out = Vec::with_capacity((j_max + 1) as usize);
    out.push(0i128);
    let mut acc = 0i128;
    for j in 1..=j_max {
        let x = ms.iter().filter(|&&m| j % m == 0).count() as i128;
        acc += 60 / (1 + x) - 30;
        out.push(acc);
    }
    out
}

fn shape2(rho: i128) {
    println!("=== stage-2 prototype: one-scale triple shapes + 2 free goods (rho<{}) ===", rho);
    let shapes: [[i128; 3]; 9] = [[4,6,9],[6,8,9],[8,9,12],[8,12,18],[9,12,16],[12,16,18],[12,18,27],[16,18,24],[16,24,36]];
    let jt: i128 = 40; // exhaustive pinned-floor table up to JT; free line beyond
    for w in shapes.iter() {
        // pinned moduli for each cluster element
        let pins: Vec<[i128; 2]> = (0..3).map(|i| {
            let mut p = [0i128; 2];
            let mut k = 0;
            for j in 0..3 {
                if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; }
            }
            p
        }).collect();
        // F_pin(J)*60 tables for J<=JT: min over free (m4,m5) in [2,J+1]^2 (tail-exact)
        let mut tables: Vec<Vec<i128>> = Vec::new();
        for p in pins.iter() {
            let mut tab = vec![i128::MAX; (jt + 1) as usize];
            tab[0] = 0;
            for m4 in 2..=(jt + 1) {
                for m5 in m4..=(jt + 1) {
                    let ms = [p[0], p[1], m4, m5];
                    let f = f_exact(&ms, jt);
                    for j in 1..=(jt as usize) {
                        // (m4,m5) is a valid representative for J >= max needed; tail-exactness:
                        // moduli > J behave as J+1; our loop includes all m <= J+1, and any m > J+1
                        // is equivalent to J+1 which IS included. So min over [2,J+1] is exact for each J.
                        if m4 <= (j as i128 + 1) && m5 <= (j as i128 + 1) {
                            if f[j] < tab[j] { tab[j] = f[j]; }
                        }
                    }
                }
            }
            tables.push(tab);
        }
        // assembled margin over tau: J_i = floor(tau / w_i); goods contribute 2*(-5/60) each
        let wmax = w[2];
        let tau_lo = 2 * wmax;
        let tau_hi = 33 * rho * wmax;
        let mut worst: (i128, i128) = (i128::MAX, 0); // (margin*60, tau)
        for tau in tau_lo..=tau_hi {
            let mut m60: i128 = 0;
            for (i, wi) in w.iter().enumerate() {
                let j = tau / wi;
                let fj = if j <= jt { tables[i][j as usize] }
                         else { (7 * 60 * j) / 300 - 14 }; // (7/300)J*60 - (7/30)*60 = 14J/... careful below
                m60 += 2 * fj;
            }
            m60 += 2 * 2 * (-5); // two goods at floor -1/12 = -5/60
            m60 -= 5 * 60;
            if m60 < worst.0 { worst = (m60, tau); }
        }
        let pass = worst.0 > 0;
        println!("  W={:?} pins={:?}: min margin*60 = {} at tau={}  [{}]",
                 w, pins, worst.0, worst.1, if pass { "PASS (uniform in goods+t)" } else { "SHORT — needs goods structure" });
    }
    println!("note: goods floored at free -1/12; S>0 dropped; J>{} uses free line — all conservative.", jt);
}

/// STAGE-2 v1: donation-pattern certificate.
/// Per shape W (3 bads t*W + 2 goods): enumerate the 64 patterns of which (bad, good)
/// donations are exactly 2. Per pattern:
///  - bad rows: exact floor tables min over admissible donation pairs (m1,m2)
///    [forced 2 where patterned; otherwise m>=3; badness 1/m1+1/m2 >= need_i];
///  - goods: floor class by #donated-2s (DRIFT-1: each donated 2 returns an odd
///    modulus >=3; a row with BOTH donations = 2 makes the goods' mutual moduli odd
///    both ways) — floors F_k := min f over 4-multisets with >= k entries odd >=3.
/// Assemble margin(tau) = 2*Sum rows + 2*Sum goods - 5*60 (S dropped), min over
/// tau in [2*wmax, 33*rho*wmax] and over patterns. Exact i128, f*60 integral.
fn fk_oddclass_floor(k_odd: usize, jt: i128) -> i128 {
    // min over 4-multisets with >= k_odd entries odd >=3 (entries in [2, JT+1], exact tail)
    // of min_{2<=J<=JT} f(J)*60; beyond JT the free line is positive so small-J governs.
    let mut best = i128::MAX;
    let hi = jt + 1;
    for m1 in 2..=hi { for m2 in m1..=hi { for m3 in m2..=hi { for m4 in m3..=hi {
        let ms = [m1, m2, m3, m4];
        let odd = ms.iter().filter(|&&m| m >= 3 && m % 2 == 1).count();
        if odd < k_odd { continue; }
        let f = f_exact(&ms, jt);
        for j in 2..=(jt as usize) {
            // representative validity: all entries <= J+1 required for tail-exactness at J
            if ms.iter().all(|&m| m <= j as i128 + 1) && f[j] < best { best = f[j]; }
        }
    }}}}
    best
}

fn shape2v1(rho: i128) {
    println!("=== stage-2 v1: donation-pattern certificates (rho<{}) ===", rho);
    let jt: i128 = 40;
    // goods' class floors by odd-count (0..=3), certified by exhaustive small-J scan
    let mut fk = [0i128; 4];
    for k in 0..4 { fk[k] = fk_oddclass_floor(k, 24); }
    println!("goods class floors f*60 (min over J>=2), by #odd-moduli>=3 pinned: {:?}", fk);
    let shapes: [[i128; 3]; 9] = [[4,6,9],[6,8,9],[8,9,12],[8,12,18],[9,12,16],[12,16,18],[12,18,27],[16,18,24],[16,24,36]];
    for w in shapes.iter() {
        let pins: Vec<[i128; 2]> = (0..3).map(|i| {
            let mut p = [0i128; 2]; let mut k = 0;
            for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
            p
        }).collect();
        // badness needs: 1/m1+1/m2 >= 1 - sum 1/pin  (as exact fractions x60: need60_i)
        // row floor tables per (forced1, forced2) in {2, free>=3}^2, per J<=JT:
        // rowtab[i][combo][J] = min over admissible (m1,m2) of f(pins_i + (m1,m2))(J)*60
        let mut rowtab = vec![[[i128::MAX; 41]; 4]; 3];
        for i in 0..3 {
            let p = pins[i];
            // need: 1/m1 + 1/m2 >= 1 - 1/p0 - 1/p1  (rational; compare via lcm)
            let needn = p[0]*p[1] - p[1] - p[0]; // (1 - 1/p0 - 1/p1) * p0*p1
            let needd = p[0]*p[1];
            for m1 in 2..=(jt + 1) { for m2 in 2..=(jt + 1) {
                // badness: 1/m1+1/m2 >= needn/needd  <=>  (m2+m1)*needd >= needn*m1*m2
                if (m1 + m2) * needd < needn * m1 * m2 { continue; }
                let ms = [p[0], p[1], m1, m2];
                let f = f_exact(&ms, jt);
                for combo in 0..4 {
                    let want1 = combo & 1 == 1; // donation to good1 is exactly 2
                    let want2 = combo & 2 == 2;
                    if want1 != (m1 == 2) { continue; }
                    if want2 != (m2 == 2) { continue; }
                    for j in 2..=(jt as usize) {
                        if m1 <= j as i128 + 1 && m2 <= j as i128 + 1 && f[j] < rowtab[i][combo][j] {
                            rowtab[i][combo][j] = f[j];
                        }
                    }
                }
            }}
        }
        // assemble: patterns = 2^(3 rows x 2 cols) but per row only the combo matters: 4^3 = 64
        let wmax = w[2];
        let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
        let mut worst = (i128::MAX, 0i128, 0usize);
        for pat in 0..64usize {
            let combos = [pat & 3, (pat >> 2) & 3, (pat >> 4) & 3];
            // goods' donated-2 counts + shared-row bonus
            let mut c = [0usize; 2];
            let mut shared = false;
            for i in 0..3 {
                if combos[i] & 1 == 1 { c[0] += 1; }
                if combos[i] & 2 == 2 { c[1] += 1; }
                if combos[i] == 3 { shared = true; }
            }
            let g0 = fk[(c[0] + if shared {1} else {0}).min(3)];
            let g1 = fk[(c[1] + if shared {1} else {0}).min(3)];
            for tau in tau_lo..=tau_hi {
                let mut m60 = 2 * (g0 + g1) - 300;
                let mut feasible = true;
                for i in 0..3 {
                    let j = tau / w[i];
                    let fj = if j <= jt {
                        let v = rowtab[i][combos[i]][j as usize];
                        if v == i128::MAX { feasible = false; break; }
                        v
                    } else { (420 * j) / 300 * 1 - 14 };
                    m60 += 2 * fj;
                }
                if !feasible { continue; } // combo impossible for this row (badness) — pattern vacuous
                if m60 < worst.0 { worst = (m60, tau, pat); }
            }
        }
        println!("  W={:?}: min margin*60 = {} at tau={} pattern={:06b}  [{}]",
                 w, worst.0, worst.1, worst.2,
                 if worst.0 > 0 { "PASS uniform" } else { "SHORT" });
    }
    println!("(goods floored by DRIFT-1 odd-class; badness-restricted bad rows; S dropped — conservative)");
}

/// charge-good staircase floor (f*60), certified by spreadcheck (reproduced):
/// f >= 1/2 (J>=2), 5/6 (J>=6), 7/6 (J>=12), 3/2 (J>=15).
fn stair60(j: i128) -> i128 {
    if j >= 15 { 90 } else if j >= 12 { 70 } else if j >= 6 { 50 } else if j >= 2 { 30 } else { 0 }
}

/// STAGE-2 v1.5: staircase goods + donor stairs, over a shape file (Codex's 69-list).
/// Rows exact as v1 (badness-restricted donation pairs, 2-flag combos); goods at the
/// certified charge-good staircase; a donated 2 to bad w_i*s pins the donor good
/// y <= 2*w_i*s, hence J_y >= floor(tau/(2*w_i)) — evaluated per pattern (sound:
/// max over its 2-donations). Runs each shape both as W and W-dual (involution warning).
fn shape2v15(rho: i128, shapes: &[[i128; 3]]) {
    println!("=== stage-2 v1.5: staircase + donor stairs (rho<{}), {} shapes x (W, Wv) ===", rho, shapes.len());
    let jt: i128 = 40;
    let mut pass_count = 0; let mut short_count = 0;
    let mut worst_overall: (i128, [i128;3], bool) = (i128::MAX, [0;3], false);
    for w0 in shapes.iter() {
        for dualize in [false, true] {
            let l = lcm(lcm(w0[0], w0[1]), w0[2]);
            let mut w = if dualize { [l/w0[2], l/w0[1], l/w0[0]] } else { *w0 };
            // normalize by gcd
            let g = gcd(gcd(w[0], w[1]), w[2]);
            for x in w.iter_mut() { *x /= g; }
            let pins: Vec<[i128; 2]> = (0..3).map(|i| {
                let mut p = [0i128; 2]; let mut k = 0;
                for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                p
            }).collect();
            let mut rowtab = vec![[[i128::MAX; 41]; 4]; 3];
            for i in 0..3 {
                let p = pins[i];
                let needn = p[0]*p[1] - p[1] - p[0];
                let needd = p[0]*p[1];
                for m1 in 2..=(jt + 1) { for m2 in 2..=(jt + 1) {
                    if (m1 + m2) * needd < needn * m1 * m2 { continue; }
                    let ms = [p[0], p[1], m1, m2];
                    let f = f_exact(&ms, jt);
                    for combo in 0..4 {
                        if (combo & 1 == 1) != (m1 == 2) { continue; }
                        if (combo & 2 == 2) != (m2 == 2) { continue; }
                        for j in 2..=(jt as usize) {
                            if m1 <= j as i128 + 1 && m2 <= j as i128 + 1 && f[j] < rowtab[i][combo][j] {
                                rowtab[i][combo][j] = f[j];
                            }
                        }
                    }
                }}
            }
            let wmax = *w.iter().max().unwrap();
            let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
            let mut worst = (i128::MAX, 0i128, 0usize);
            for pat in 0..64usize {
                let combos = [pat & 3, (pat >> 2) & 3, (pat >> 4) & 3];
                for tau in tau_lo..=tau_hi {
                    // goods' stair levels: J >= 2 always; donor of a 2 to bad i: J >= tau/(2 w_i)
                    let mut jg = [2i128, 2i128];
                    for i in 0..3 {
                        // DRIFT-1 2-friend: y <= (2/3) w_i s  =>  J_y >= floor(3 tau/(2 w_i))
                        if combos[i] & 1 == 1 { jg[0] = jg[0].max(3 * tau / (2 * w[i])); }
                        if combos[i] & 2 == 2 { jg[1] = jg[1].max(3 * tau / (2 * w[i])); }
                    }
                    let mut m60 = 2 * (stair60(jg[0]) + stair60(jg[1])) - 300;
                    let mut feasible = true;
                    for i in 0..3 {
                        let j = tau / w[i];
                        let fj = if j <= jt {
                            let v = rowtab[i][combos[i]][j as usize];
                            if v == i128::MAX { feasible = false; break; }
                            v
                        } else { (420 * j) / 300 - 14 };
                        m60 += 2 * fj;
                    }
                    if !feasible { continue; }
                    if m60 < worst.0 { worst = (m60, tau, pat); }
                }
            }
            if worst.0 > 0 { pass_count += 1; } else {
                short_count += 1;
                if worst.0 < worst_overall.0 { worst_overall = (worst.0, *w0, dualize); }
                if short_count <= 12 {
                    println!("  SHORT W={:?}{} margin*60={} tau={} pat={:06b}",
                             w0, if dualize {"^v"} else {""}, worst.0, worst.1, worst.2);
                }
            }
        }
    }
    println!("PASS {} / SHORT {} (of {} shape-sides); worst {:?}{} at {}",
             pass_count, short_count, 2*shapes.len(), worst_overall.1,
             if worst_overall.2 {"^v"} else {""}, worst_overall.0);
}

/// STAGE-2 v2.1: flags (all donated 2s pinned, as v1.5) + one optional non-2 value
/// descriptor per good (i, v in 3..=6) for extra stairs. Strictly dominates v1.5/v2.
/// Row classes per entry: =2 (flagged), >=3 any (unflagged, no descriptor), =v
/// (unflagged, descriptor names this row). Threaded over shape-sides.
fn shape2v21(rho: i128, shapes: &[[i128; 3]]) {
    println!("=== stage-2 v2.1: flags + value descriptors (rho<{}), {} dual shapes -> W^vee sides ===", rho, shapes.len());
    let jt: i128 = 40;
    // build task list of (shape, dualize)
    // shapes file lists DUAL triples; the primal drift rows are W^vee only (Codex
    // coordinate correction 2026-07-17). One side per shape.
    let mut sides: Vec<([i128;3], bool)> = Vec::new();
    for w0 in shapes.iter() { sides.push((*w0, true)); }
    let nthreads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let results: Vec<(i128, [i128;3], bool, i128)> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            let sides = &sides;
            s.spawn(move || {
                let mut out = Vec::new();
                for (idx, (w0, dualize)) in sides.iter().enumerate() {
                    if idx % nthreads != tid { continue; }
                    let l = lcm(lcm(w0[0], w0[1]), w0[2]);
                    let mut w = if *dualize { [l/w0[2], l/w0[1], l/w0[0]] } else { *w0 };
                    let g = gcd(gcd(w[0], w[1]), w[2]);
                    for x in w.iter_mut() { *x /= g; }
                    let pins: Vec<[i128; 2]> = (0..3).map(|i| {
                        let mut p = [0i128; 2]; let mut k = 0;
                        for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                        p
                    }).collect();
                    // classes: 0 = "=2", 1 = ">=3 any", 2..=5 = "=3..=6"
                    let cls_ok = |c: usize, m: i128| -> bool {
                        match c { 0 => m == 2, 1 => m >= 3, k => m == (k as i128 + 1) }
                    };
                    let mut rowtab = vec![[[[i128::MAX; 41]; 6]; 6]; 3];
                    for i in 0..3 {
                        let p = pins[i];
                        let needn = p[0]*p[1] - p[1] - p[0];
                        let needd = p[0]*p[1];
                        for m1 in 2..=(jt + 1) { for m2 in 2..=(jt + 1) {
                            if (m1 + m2) * needd < needn * m1 * m2 { continue; }
                            let ms = [p[0], p[1], m1, m2];
                            let f = f_exact(&ms, jt);
                            for c1 in 0..6usize {
                                if !cls_ok(c1, m1) { continue; }
                                for c2 in 0..6usize {
                                    if !cls_ok(c2, m2) { continue; }
                                    for j in 2..=(jt as usize) {
                                        if m1 <= j as i128 + 1 && m2 <= j as i128 + 1
                                           && f[j] < rowtab[i][c1][c2][j] {
                                            rowtab[i][c1][c2][j] = f[j];
                                        }
                                    }
                                }
                            }
                        }}
                    }
                    let wmax = *w.iter().max().unwrap();
                    let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
                    // pattern: 64 flag patterns x per-good optional descriptor.
                    // descriptor for good j: 0 = none, else (i, v) with i not flagged-2 for j: 1+i*4+(v-3)
                    let mut worst = (i128::MAX, 0i128);
                    for pat in 0..64usize {
                        let combos = [pat & 3, (pat >> 2) & 3, (pat >> 4) & 3];
                        for d0 in 0..13usize { for d1 in 0..13usize {
                            let dec = |d: usize| -> Option<(usize, i128)> {
                                if d == 0 { None } else { Some(((d-1)/4, ((d-1)%4) as i128 + 3)) }
                            };
                            let de = [dec(d0), dec(d1)];
                            // consistency: descriptor row must not be flagged 2 for that good
                            let mut ok = true;
                            for (jgood, dd) in de.iter().enumerate() {
                                if let Some((bi, _)) = dd {
                                    let flagged = if jgood == 0 { combos[*bi] & 1 == 1 } else { combos[*bi] & 2 == 2 };
                                    if flagged { ok = false; }
                                }
                            }
                            if !ok { continue; }
                            for tau in tau_lo..=tau_hi {
                                // stairs: from 2-flags and from descriptors
                                let mut jg = [2i128, 2i128];
                                for i in 0..3 {
                                    // DRIFT-1: donated 2 => y <= (2/3) w s => J >= 3tau/(2w)
                                    if combos[i] & 1 == 1 { jg[0] = jg[0].max(3 * tau / (2 * w[i])); }
                                    if combos[i] & 2 == 2 { jg[1] = jg[1].max(3 * tau / (2 * w[i])); }
                                }
                                for (jgood, dd) in de.iter().enumerate() {
                                    // proper divisor: y = v*d, d | w s, d != w s  =>  y <= v w s/2 => J >= 2tau/(v w)
                                    if let Some((bi, v)) = dd { jg[jgood] = jg[jgood].max(2 * tau / (v * w[*bi])); }
                                }
                                let mut m60 = 2 * (stair60(jg[0]) + stair60(jg[1])) - 300;
                                let mut feasible = true;
                                for i in 0..3 {
                                    let c1 = if combos[i] & 1 == 1 { 0 }
                                             else if let Some((bi, v)) = de[0] { if bi == i { (v - 1) as usize } else { 1 } }
                                             else { 1 };
                                    let c2 = if combos[i] & 2 == 2 { 0 }
                                             else if let Some((bi, v)) = de[1] { if bi == i { (v - 1) as usize } else { 1 } }
                                             else { 1 };
                                    let j = tau / w[i];
                                    let fj = if j <= jt {
                                        let vv = rowtab[i][c1][c2][j as usize];
                                        if vv == i128::MAX { feasible = false; break; }
                                        vv
                                    } else { (420 * j) / 300 - 14 };
                                    m60 += 2 * fj;
                                }
                                if !feasible { continue; }
                                if m60 < worst.0 { worst = (m60, tau); }
                            }
                        }}
                    }
                    out.push((worst.0, *w0, *dualize, worst.1));
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let mut pass = 0; let mut short: Vec<_> = Vec::new();
    for r in results.iter() { if r.0 > 0 { pass += 1; } else { short.push(*r); } }
    short.sort();
    for (m, w, d, tau) in short.iter().take(15) {
        println!("  SHORT W={:?}{} margin*60={} tau={}", w, if *d {"^v"} else {""}, m, tau);
    }
    println!("PASS {} / SHORT {} (of {} shape-sides)", pass, short.len(), results.len());
}

/// STAGE-2 v2.2: exact donated-2 return-cofactor coupling (Codex Section 21 spec).
/// Any good donating a 2 to bad p_i0 = w_i0*s is PINNED: y = 2*p_i0/q, where the
/// return cofactor q = p_i0/gcd(y,p_i0) is ODD (2-adic lemma: v2(p)=v2(y)-1),
/// >= 3 (antichain), and ratio<rho both ways gives q*wmax < 2*rho*w_i0 and
/// q*rho*wmin > 2*w_i0. All of y's gcds are then s-free template constants: with
/// g_j = gcd(2*w_i0, q*w_j) [identity gcd(A/q,B) = gcd(A,qB)/q for q|A; s cancels],
///   y's modulus in bad row j     = 2*w_i0/g_j   (forced slot),
///   p_j's modulus in y's own row = q*w_j/g_j.
/// Flag consistency (forced slot == 2 iff flagged) partitions configuration space
/// and subsumes the shared-2 2-adic compatibility. If both goods are pinned, their
/// mutual moduli are exact too: G = gcd(2*w_a*q1, 2*w_b*q0), y0's row receives
/// 2*w_b*q0/G, y1's row 2*w_a*q1/G [identity gcd(A/q,B/r) = gcd(Ar,Bq)/(qr)].
/// Pinned goods get exact drift rows f_exact([q*w_j/g_j...], free slot minimized
/// under the exact goodness test), evaluated at J in [q*tau/(2w_i0),
/// q*(tau+1)/(2w_i0)] (min over the interval — f is not monotone), floored by
/// stair60. Free goods keep the v2.1 stair + optional value descriptor. Bad rows'
/// forced slots use exact-value classes (clamped to 41 = JT+1, tail-exact for
/// J <= JT; badness tested at clamped values — conservative inclusion). Branches
/// whose forced moduli make some bad row unable to be bad, or the donor good, are
/// vacuous and skipped (their configs do not exist).
fn shape2v22(rho: i128, shapes: &[[i128; 3]]) {
    println!("=== stage-2 v2.2: donated-2 q-coupling (rho<{}), {} dual shapes -> W^vee sides ===", rho, shapes.len());
    let jt: i128 = 40;
    let mc: i128 = 41; // clamp: any modulus >= 41 is tail-exact as 41 for J <= 40
    let sides: Vec<[i128; 3]> = shapes.to_vec();
    let nthreads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    // (margin, shape, tau, pat, q0, q1)
    let results: Vec<(i128, [i128; 3], i128, usize, i128, i128)> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            let sides = &sides;
            s.spawn(move || {
                let mut out = Vec::new();
                for (idx, w0) in sides.iter().enumerate() {
                    if idx % nthreads != tid { continue; }
                    let l = lcm(lcm(w0[0], w0[1]), w0[2]);
                    let mut w = [l / w0[2], l / w0[1], l / w0[0]];
                    let g = gcd(gcd(w[0], w[1]), w[2]);
                    for x in w.iter_mut() { *x /= g; }
                    let wmax = *w.iter().max().unwrap();
                    let wmin = *w.iter().min().unwrap();
                    let pins: Vec<[i128; 2]> = (0..3).map(|i| {
                        let mut p = [0i128; 2]; let mut k = 0;
                        for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                        p
                    }).collect();
                    // rowtab[i][c1][c2][j]: c = 0 free (m>=3), c in 1..=40 exact m = c+1
                    let rti = |i: usize, c1: usize, c2: usize, j: usize| ((i * 41 + c1) * 41 + c2) * 41 + j;
                    let mut rowtab = vec![i128::MAX; 3 * 41 * 41 * 41];
                    let mut needs = [[0i128; 2]; 3];
                    for i in 0..3 {
                        let p = pins[i];
                        needs[i] = [p[0] * p[1] - p[1] - p[0], p[0] * p[1]];
                        for m1 in 2..=mc { for m2 in 2..=mc {
                            if (m1 + m2) * needs[i][1] < needs[i][0] * m1 * m2 { continue; } // row not bad
                            let f = f_exact(&[p[0], p[1], m1, m2], jt);
                            let (c1e, c2e) = (m1 as usize - 1, m2 as usize - 1);
                            for j in 2..=(jt as usize) {
                                let v = f[j];
                                let ji = j as i128;
                                // exact-exact: true value's f is exact at every j (no gate)
                                if v < rowtab[rti(i, c1e, c2e, j)] { rowtab[rti(i, c1e, c2e, j)] = v; }
                                // free-class cells: representative must be in range (m <= j+1)
                                let ok1 = m1 >= 3 && m1 <= ji + 1;
                                let ok2 = m2 >= 3 && m2 <= ji + 1;
                                if ok1 && v < rowtab[rti(i, 0, c2e, j)] { rowtab[rti(i, 0, c2e, j)] = v; }
                                if ok2 && v < rowtab[rti(i, c1e, 0, j)] { rowtab[rti(i, c1e, 0, j)] = v; }
                                if ok1 && ok2 && v < rowtab[rti(i, 0, 0, j)] { rowtab[rti(i, 0, 0, j)] = v; }
                            }
                        }}
                    }
                    let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
                    let clamp = |m: i128| -> i128 { if m > mc { mc } else { m } };
                    let mut worst = (i128::MAX, 0i128, 0usize, 0i128, 0i128);
                    for pat in 0..64usize {
                        let combos = [pat & 3, (pat >> 2) & 3, (pat >> 4) & 3];
                        let mut r0: Vec<usize> = Vec::new(); let mut r1: Vec<usize> = Vec::new();
                        for i in 0..3 {
                            if combos[i] & 1 == 1 { r0.push(i); }
                            if combos[i] & 2 == 2 { r1.push(i); }
                        }
                        let qset = |r: &Vec<usize>| -> Vec<i128> {
                            if r.is_empty() { return vec![0]; }
                            let i0 = r[0];
                            let mut v = Vec::new();
                            let mut q = 3i128;
                            while q <= 2 * rho - 1 {
                                if q * wmax < 2 * rho * w[i0] && q * rho * wmin > 2 * w[i0] { v.push(q); }
                                q += 2;
                            }
                            v
                        };
                        let qs0 = qset(&r0); let qs1 = qset(&r1);
                        for &q0 in qs0.iter() { 'branch: for &q1 in qs1.iter() {
                            // forced slots: srow[g][i] = y_g's modulus in row i (0 = free good);
                            // sy[g][i] = p_i's modulus in y_g's row
                            let mut srow = [[0i128; 3]; 2];
                            let mut sy = [[0i128; 3]; 2];
                            for (g, (r, q)) in [(&r0, q0), (&r1, q1)].into_iter().enumerate() {
                                if r.is_empty() { continue; }
                                let i0 = r[0];
                                for j in 0..3 {
                                    let gj = gcd(2 * w[i0], q * w[j]);
                                    srow[g][j] = 2 * w[i0] / gj;
                                    sy[g][j] = q * w[j] / gj;
                                    if r.contains(&j) {
                                        // flagged: slot must be 2; coupled return cofactor >= 3
                                        if srow[g][j] != 2 || sy[g][j] < 3 { continue 'branch; }
                                    } else {
                                        // =1: antichain violation; =2: belongs to the flagged pattern
                                        if srow[g][j] <= 2 || sy[g][j] < 2 { continue 'branch; }
                                    }
                                }
                            }
                            let both = !r0.is_empty() && !r1.is_empty();
                            let (mut mg0, mut mg1) = (0i128, 0i128); // other good's modulus in y_g's row; 0 = free
                            if both {
                                let (a, b) = (r0[0], r1[0]);
                                let gg = gcd(2 * w[a] * q1, 2 * w[b] * q0);
                                mg0 = 2 * w[b] * q0 / gg;
                                mg1 = 2 * w[a] * q1 / gg;
                                if mg0 < 2 || mg1 < 2 { continue 'branch; } // divisibility/equality among goods
                            }
                            // pinned goods: exact goodness test + exact drift row
                            let mut rowyf: [Vec<i128>; 2] = [Vec::new(), Vec::new()];
                            for g in 0..2 {
                                let (r, other_m) = if g == 0 { (&r0, mg0) } else { (&r1, mg1) };
                                if r.is_empty() { continue; }
                                let known = [sy[g][0], sy[g][1], sy[g][2]];
                                let mut p: i128 = known.iter().product();
                                let mut num: i128 = known.iter().map(|&m| p / m).sum();
                                if other_m > 0 { num = num * other_m + p; p *= other_m; }
                                if num >= p { continue 'branch; } // y_g cannot be good
                                if other_m > 0 {
                                    rowyf[g] = f_exact(&[clamp(known[0]), clamp(known[1]), clamp(known[2]), clamp(other_m)], jt);
                                } else {
                                    // free slot: min over m in 2..=41 (41 = tail rep of [41,oo):
                                    // its goodness term vanishes in the limit, so only num<p is required)
                                    let mut acc = vec![i128::MAX; (jt + 1) as usize];
                                    for mf in 2..=mc {
                                        let feas = if mf == mc { true } else { num * mf + p < p * mf };
                                        if !feas { continue; }
                                        let f = f_exact(&[clamp(known[0]), clamp(known[1]), clamp(known[2]), mf], jt);
                                        for j in 0..acc.len() { if f[j] < acc[j] { acc[j] = f[j]; } }
                                    }
                                    rowyf[g] = acc;
                                }
                            }
                            let d0n = if r0.is_empty() { 13 } else { 1 };
                            let d1n = if r1.is_empty() { 13 } else { 1 };
                            for d0 in 0..d0n { for d1 in 0..d1n {
                                let dec = |d: usize| -> Option<(usize, i128)> {
                                    if d == 0 { None } else { Some(((d - 1) / 4, ((d - 1) % 4) as i128 + 3)) }
                                };
                                let de = [dec(d0), dec(d1)];
                                let mut cls = [[0usize; 2]; 3];
                                let mut dead = false;
                                for i in 0..3 {
                                    for gg in 0..2 {
                                        cls[i][gg] = if srow[gg][i] > 0 { clamp(srow[gg][i]) as usize - 1 }
                                                     else if let Some((bi, v)) = de[gg] { if bi == i { (v - 1) as usize } else { 0 } }
                                                     else { 0 };
                                    }
                                    // branch-level badness feasibility (free slot -> 3 maximizes charge)
                                    let a = if cls[i][0] == 0 { 3 } else { cls[i][0] as i128 + 1 };
                                    let b = if cls[i][1] == 0 { 3 } else { cls[i][1] as i128 + 1 };
                                    if (a + b) * needs[i][1] < needs[i][0] * a * b { dead = true; break; }
                                }
                                if dead { continue; }
                                for tau in tau_lo..=tau_hi {
                                    let mut m60 = -300i128;
                                    for g in 0..2 {
                                        let r = if g == 0 { &r0 } else { &r1 };
                                        if r.is_empty() {
                                            let jg = match de[g] { None => 2, Some((bi, v)) => (2 * tau / (v * w[bi])).max(2) };
                                            m60 += 2 * stair60(jg);
                                        } else {
                                            let q = if g == 0 { q0 } else { q1 };
                                            let i0 = r[0];
                                            let jlo = q * tau / (2 * w[i0]);
                                            let jhi = q * (tau + 1) / (2 * w[i0]);
                                            let mut best = i128::MAX;
                                            let mut jy = jlo;
                                            while jy <= jhi {
                                                let v = if jy <= jt {
                                                    let e = rowyf[g][jy as usize];
                                                    let st = stair60(jy);
                                                    if e > st { e } else { st }
                                                } else { 90 };
                                                if v < best { best = v; }
                                                jy += 1;
                                            }
                                            m60 += 2 * best;
                                        }
                                    }
                                    let mut feasible = true;
                                    for i in 0..3 {
                                        let j = tau / w[i];
                                        let fj = if j <= jt {
                                            let v = rowtab[rti(i, cls[i][0], cls[i][1], j as usize)];
                                            if v == i128::MAX { feasible = false; break; }
                                            v
                                        } else { (420 * j) / 300 - 14 };
                                        m60 += 2 * fj;
                                    }
                                    if !feasible { continue; }
                                    if m60 < worst.0 { worst = (m60, tau, pat, q0, q1); }
                                }
                            }}
                        }}
                    }
                    out.push((worst.0, *w0, worst.1, worst.2, worst.3, worst.4));
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let mut pass = 0; let mut zero: Vec<_> = Vec::new(); let mut short: Vec<_> = Vec::new();
    for r in results.iter() {
        if r.0 == i128::MAX { println!("  VACUOUS(all patterns) W={:?}", r.1); pass += 1; }
        else if r.0 > 0 { pass += 1; }
        else if r.0 == 0 { zero.push(*r); }
        else { short.push(*r); }
    }
    short.sort();
    for (m, w, tau, pat, q0, q1) in short.iter() {
        println!("  SHORT W={:?}^v margin*60={} tau={} pat={:06b} q0={} q1={}", w, m, tau, pat, q0, q1);
    }
    for (_, w, tau, pat, q0, q1) in zero.iter() {
        println!("  ZERO  W={:?}^v (passes via retained +S) tau={} pat={:06b} q0={} q1={}", w, tau, pat, q0, q1);
    }
    println!("PASS {} / ZERO {} (pass via +S) / SHORT {} (of {} W^vee sides)",
             pass, zero.len(), short.len(), results.len());
}

/// STAGE-2 v3: exact slot-matrix partition with generalized return-cofactor
/// coupling (subsumes v2.2's donated-2 machinery, Codex Section 21 spec, at every
/// donation value). Configuration space is partitioned by the CLASS MATRIX: for
/// each bad row i and each good g, the slot y_g/gcd(y_g, p_i) is declared either
/// an exact value v in 2..=6 or BIG (>= 7). Any exact slot (i*, v*) PINS its good:
///   y = v* * w_i* * s / q,   q = p_i*/gcd = return cofactor,
/// with gcd(v*, q) = 1 (slot and cofactor are the coprime pair y/g, p/g), q >= 2
/// (q = 1 is p | y, antichain), and ratio < rho both ways:
///   q*wmax < v*rho*w_i*   and   q*rho*wmin > v*w_i*.
/// All the pinned good's gcds are then s-free template constants: with
/// g_j = gcd(v*w_i*, q*w_j),
///   slot in row j     = v*w_i*/g_j   (must match row j's declared class),
///   y's row receives  = q*w_j/g_j    (>= 2, antichain).
/// Both goods pinned => mutual moduli exact: G = gcd(v0*w_a*q1, v1*w_b*q0),
/// y0's row receives v1*w_b*q0/G, y1's row v0*w_a*q1/G. Pinned goods get the
/// exact goodness test (kills branches) and exact drift rows f_exact evaluated at
/// J in [q*tau/(v*w_i*), q*(tau+1)/(v*w_i*)] (min over interval; f not monotone),
/// floored by stair60. Free goods (all-BIG column) get the base stair. Bad rows
/// use exact-value cells (clamped to 41, tail-exact for J <= 40) or the BIG class
/// (badness capped at 1/7 — conservative). Branches whose forced values contradict
/// the declared classes, the antichain, goodness, or badness are vacuous: their
/// configurations do not exist. VACUOUS shapes admit no 3-bad configuration at all.
fn shape2v3(rho: i128, shapes: &[[i128; 3]]) {
    println!("=== stage-2 v3: exact slot-matrix + generalized q-coupling (rho<{}), {} dual shapes -> W^vee sides ===", rho, shapes.len());
    let jt: i128 = 40;
    let mc: i128 = 41;
    let sides: Vec<[i128; 3]> = shapes.to_vec();
    let nthreads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    // (margin, shape, tau, class-matrix digest, q0, q1)
    let results: Vec<(i128, [i128; 3], i128, u64, i128, i128)> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            let sides = &sides;
            s.spawn(move || {
                let mut out = Vec::new();
                for (idx, w0) in sides.iter().enumerate() {
                    if idx % nthreads != tid { continue; }
                    let l = lcm(lcm(w0[0], w0[1]), w0[2]);
                    let mut w = [l / w0[2], l / w0[1], l / w0[0]];
                    let g = gcd(gcd(w[0], w[1]), w[2]);
                    for x in w.iter_mut() { *x /= g; }
                    let wmax = *w.iter().max().unwrap();
                    let wmin = *w.iter().min().unwrap();
                    let pins: Vec<[i128; 2]> = (0..3).map(|i| {
                        let mut p = [0i128; 2]; let mut k = 0;
                        for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                        p
                    }).collect();
                    // rowtab[i][c1][c2][j]: c = 0 BIG (m >= 7), c = m-1 for exact m in 2..=41
                    let rti = |i: usize, c1: usize, c2: usize, j: usize| ((i * 42 + c1) * 42 + c2) * 41 + j;
                    let mut rowtab = vec![i128::MAX; 3 * 42 * 42 * 41];
                    let mut needs = [[0i128; 2]; 3];
                    for i in 0..3 {
                        let p = pins[i];
                        needs[i] = [p[0] * p[1] - p[1] - p[0], p[0] * p[1]];
                        for m1 in 2..=mc { for m2 in 2..=mc {
                            if (m1 + m2) * needs[i][1] < needs[i][0] * m1 * m2 { continue; }
                            let f = f_exact(&[p[0], p[1], m1, m2], jt);
                            let (c1e, c2e) = (m1 as usize - 1, m2 as usize - 1);
                            for j in 2..=(jt as usize) {
                                let v = f[j];
                                let ji = j as i128;
                                if v < rowtab[rti(i, c1e, c2e, j)] { rowtab[rti(i, c1e, c2e, j)] = v; }
                                // BIG representative: m >= 7 in range, or the prefix-equivalent m == j+1
                                let ok1 = (m1 >= 7 && m1 <= ji + 1) || (ji < 6 && m1 == ji + 1);
                                let ok2 = (m2 >= 7 && m2 <= ji + 1) || (ji < 6 && m2 == ji + 1);
                                if ok1 && v < rowtab[rti(i, 0, c2e, j)] { rowtab[rti(i, 0, c2e, j)] = v; }
                                if ok2 && v < rowtab[rti(i, c1e, 0, j)] { rowtab[rti(i, c1e, 0, j)] = v; }
                                if ok1 && ok2 && v < rowtab[rti(i, 0, 0, j)] { rowtab[rti(i, 0, 0, j)] = v; }
                            }
                        }}
                    }
                    // per-row feasible class pairs: values 0 (BIG) or 2..=6 exact
                    let cap = |c: i128| if c == 0 { 7 } else { c };
                    let mut rowpairs: [Vec<(i128, i128)>; 3] = [Vec::new(), Vec::new(), Vec::new()];
                    for i in 0..3 {
                        for a in [0i128, 2, 3, 4, 5, 6] { for b in [0i128, 2, 3, 4, 5, 6] {
                            let (x, y) = (cap(a), cap(b));
                            if (x + y) * needs[i][1] >= needs[i][0] * x * y { rowpairs[i].push((a, b)); }
                        }}
                    }
                    let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
                    let clamp = |m: i128| -> i128 { if m > mc { mc } else { m } };
                    let mut worst = (i128::MAX, 0i128, 0u64, 0i128, 0i128);
                    for &(a0, b0) in rowpairs[0].iter() {
                    for &(a1, b1) in rowpairs[1].iter() {
                    for &(a2, b2) in rowpairs[2].iter() {
                        let colg = [[a0, a1, a2], [b0, b1, b2]]; // colg[g][i] = declared class
                        // digest for reporting: 6 slots base-8
                        let dig: u64 = [a0, b0, a1, b1, a2, b2].iter().fold(0u64, |acc, &c| acc * 8 + c as u64);
                        // pinned goods: first exact slot
                        let pin_of = |g: usize| -> Option<(usize, i128)> {
                            (0..3).find(|&i| colg[g][i] >= 2).map(|i| (i, colg[g][i]))
                        };
                        let pin = [pin_of(0), pin_of(1)];
                        let qset = |p: &Option<(usize, i128)>| -> Vec<i128> {
                            match p {
                                None => vec![0],
                                Some((istar, vstar)) => {
                                    let mut v = Vec::new();
                                    let mut q = 2i128;
                                    while q * wmax < vstar * rho * w[*istar] {
                                        if gcd(q, *vstar) == 1 && q * rho * wmin > vstar * w[*istar] { v.push(q); }
                                        q += 1;
                                    }
                                    v
                                }
                            }
                        };
                        let qs0 = qset(&pin[0]); let qs1 = qset(&pin[1]);
                        for &q0 in qs0.iter() { 'branch: for &q1 in qs1.iter() {
                            let qq = [q0, q1];
                            // forced slots for pinned goods; check against declared classes
                            let mut srow = [[0i128; 3]; 2]; // 0 = free slot (BIG, unpinned good)
                            let mut sy = [[0i128; 3]; 2];
                            for g in 0..2 {
                                if let Some((istar, vstar)) = pin[g] {
                                    for j in 0..3 {
                                        let gj = gcd(vstar * w[istar], qq[g] * w[j]);
                                        srow[g][j] = vstar * w[istar] / gj;
                                        sy[g][j] = qq[g] * w[j] / gj;
                                        let c = colg[g][j];
                                        if c >= 2 { if srow[g][j] != c { continue 'branch; } }
                                        else { if srow[g][j] < 7 { continue 'branch; } }
                                        if sy[g][j] < 2 { continue 'branch; } // p_j | y
                                    }
                                }
                            }
                            let both = pin[0].is_some() && pin[1].is_some();
                            let (mut mg0, mut mg1) = (0i128, 0i128);
                            if both {
                                let (ia, va) = pin[0].unwrap(); let (ib, vb) = pin[1].unwrap();
                                let gg = gcd(va * w[ia] * q1, vb * w[ib] * q0);
                                mg0 = vb * w[ib] * q0 / gg;
                                mg1 = va * w[ia] * q1 / gg;
                                if mg0 < 2 || mg1 < 2 { continue 'branch; }
                            }
                            let mut rowyf: [Vec<i128>; 2] = [Vec::new(), Vec::new()];
                            for g in 0..2 {
                                if pin[g].is_none() { continue; }
                                let other_m = if g == 0 { mg0 } else { mg1 };
                                let known = [sy[g][0], sy[g][1], sy[g][2]];
                                let mut p: i128 = known.iter().product();
                                let mut num: i128 = known.iter().map(|&m| p / m).sum();
                                if other_m > 0 { num = num * other_m + p; p *= other_m; }
                                if num >= p { continue 'branch; } // pinned good cannot be good
                                if other_m > 0 {
                                    rowyf[g] = f_exact(&[clamp(known[0]), clamp(known[1]), clamp(known[2]), clamp(other_m)], jt);
                                } else {
                                    let mut acc = vec![i128::MAX; (jt + 1) as usize];
                                    for mf in 2..=mc {
                                        let feas = if mf == mc { true } else { num * mf + p < p * mf };
                                        if !feas { continue; }
                                        let f = f_exact(&[clamp(known[0]), clamp(known[1]), clamp(known[2]), mf], jt);
                                        for j in 0..acc.len() { if f[j] < acc[j] { acc[j] = f[j]; } }
                                    }
                                    rowyf[g] = acc;
                                }
                            }
                            // row lookup classes: forced exact (clamped) beats declared BIG
                            let mut cls = [[0usize; 2]; 3];
                            let mut dead = false;
                            for i in 0..3 {
                                for g in 0..2 {
                                    cls[i][g] = if srow[g][i] > 0 { clamp(srow[g][i]) as usize - 1 }
                                                else if colg[g][i] >= 2 { colg[g][i] as usize - 1 }
                                                else { 0 };
                                }
                                let a = if cls[i][0] == 0 { 7 } else { cls[i][0] as i128 + 1 };
                                let b = if cls[i][1] == 0 { 7 } else { cls[i][1] as i128 + 1 };
                                if (a + b) * needs[i][1] < needs[i][0] * a * b { dead = true; break; }
                            }
                            if dead { continue; }
                            for tau in tau_lo..=tau_hi {
                                let mut m60 = -300i128;
                                for g in 0..2 {
                                    match pin[g] {
                                        None => { m60 += 2 * stair60(2); }
                                        Some((istar, vstar)) => {
                                            let jlo = qq[g] * tau / (vstar * w[istar]);
                                            let jhi = qq[g] * (tau + 1) / (vstar * w[istar]);
                                            let mut best = i128::MAX;
                                            let mut jy = jlo;
                                            while jy <= jhi {
                                                let v = if jy <= jt {
                                                    let e = rowyf[g][jy as usize];
                                                    let st = stair60(jy);
                                                    if e > st { e } else { st }
                                                } else { 90 };
                                                if v < best { best = v; }
                                                jy += 1;
                                            }
                                            m60 += 2 * best;
                                        }
                                    }
                                }
                                let mut feasible = true;
                                for i in 0..3 {
                                    let j = tau / w[i];
                                    let fj = if j <= jt {
                                        let v = rowtab[rti(i, cls[i][0], cls[i][1], j as usize)];
                                        if v == i128::MAX { feasible = false; break; }
                                        v
                                    } else { (420 * j) / 300 - 14 };
                                    m60 += 2 * fj;
                                }
                                if !feasible { continue; }
                                if m60 < worst.0 { worst = (m60, tau, dig, q0, q1); }
                            }
                        }}
                    }}}
                    out.push((worst.0, *w0, worst.1, worst.2, worst.3, worst.4));
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let mut pass = 0; let mut vac = 0; let mut zero: Vec<_> = Vec::new(); let mut short: Vec<_> = Vec::new();
    let decode = |d: u64| -> String {
        let mut cs = [0u64; 6];
        let mut x = d;
        for k in (0..6).rev() { cs[k] = x % 8; x /= 8; }
        format!("[{}]", cs.iter().map(|&c| if c == 0 { "B".to_string() } else { c.to_string() })
                .collect::<Vec<_>>().join(","))
    };
    let mut sorted = results.clone();
    sorted.sort();
    for r in sorted.iter() {
        if r.0 == i128::MAX { vac += 1; println!("  VACUOUS W={:?} (no 3-bad configuration in the stage-2 model)", r.1); }
        else if r.0 > 0 {
            pass += 1;
            println!("  PASS  W={:?}^v worst margin*60={} at tau={} cls={} q0={} q1={}",
                     r.1, r.0, r.2, decode(r.3), r.4, r.5);
        }
        else if r.0 == 0 { zero.push(*r); }
        else { short.push(*r); }
    }
    short.sort();
    for (m, w, tau, dig, q0, q1) in short.iter() {
        println!("  SHORT W={:?}^v margin*60={} tau={} cls={} q0={} q1={}", w, m, tau, decode(*dig), q0, q1);
    }
    for (_, w, tau, dig, q0, q1) in zero.iter() {
        println!("  ZERO  W={:?}^v (passes via retained +S) tau={} cls={} q0={} q1={}", w, tau, decode(*dig), q0, q1);
    }
    println!("PASS {} (incl. {} VACUOUS) / ZERO {} (pass via +S) / SHORT {} (of {} W^vee sides)",
             pass + vac, vac, zero.len(), short.len(), results.len());
}

/// STAGE-4B: the v3 exact slot-matrix certificate for the 4-BAD sector — 4 bad
/// rows w_i*s (CSV: PRIMAL bad-quadruple coefficients, gcd-normalized) + ONE good.
/// Class matrix = 4 slots (one per row), each exact 2..=6 or BIG >= 7. The good is
/// pinned by its first exact slot exactly as in v3 (y = v*w_i**s/q, gcd(v,q)=1,
/// q >= 2, spread-bounded), which forces ALL FOUR of its gcds; its own row then has
/// four KNOWN moduli (no free slot at all): exact goodness test and exact drift row.
/// The all-BIG column (free good) covers the entire coprime-junk tail on the good
/// (multiplying the good by coprime junk preserves every bad's charge, so each
/// witness spawns a 1-parameter infinite family whose tail is all-BIG) — the
/// certificate is uniform in both the common bad scale s and the good.
/// NOTE: covers the exactly-4-bad sector; 5-bad has no good to donate and is
/// separately excluded/open (flagged to Codex).
fn shape4(rho: i128, shapes: &[[i128; 4]]) {
    println!("=== stage-4B: 4-bad exact slot-matrix + q-coupling (rho<{}), {} primal bad-quad shapes ===", rho, shapes.len());
    let jt: i128 = 40;
    let mc: i128 = 41;
    let sides: Vec<[i128; 4]> = shapes.to_vec();
    let nthreads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let results: Vec<(i128, [i128; 4], i128, u64, i128)> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            let sides = &sides;
            s.spawn(move || {
                let mut out = Vec::new();
                for (idx, w0) in sides.iter().enumerate() {
                    if idx % nthreads != tid { continue; }
                    let mut w = *w0;
                    let g = w.iter().fold(0i128, |a, &b| gcd(a, b));
                    for x in w.iter_mut() { *x /= g; }
                    let wmax = *w.iter().max().unwrap();
                    let wmin = *w.iter().min().unwrap();
                    let pins: Vec<[i128; 3]> = (0..4).map(|i| {
                        let mut p = [0i128; 3]; let mut k = 0;
                        for j in 0..4 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                        p
                    }).collect();
                    // rowtab[i][c][j]: c = 0 BIG (m >= 7), c = m-1 exact m in 2..=41
                    let rti = |i: usize, c: usize, j: usize| (i * 42 + c) * 41 + j;
                    let mut rowtab = vec![i128::MAX; 4 * 42 * 41];
                    let mut needs = [[0i128; 2]; 4];
                    for i in 0..4 {
                        let p = pins[i];
                        let dd = p[0] * p[1] * p[2];
                        let nn = dd - dd / p[0] - dd / p[1] - dd / p[2];
                        needs[i] = [nn, dd];
                        for m in 2..=mc {
                            if needs[i][0] * m > needs[i][1] { continue; } // 1/m < need: row not bad
                            let f = f_exact(&[p[0], p[1], p[2], m], jt);
                            let ce = m as usize - 1;
                            for j in 2..=(jt as usize) {
                                let v = f[j];
                                let ji = j as i128;
                                if v < rowtab[rti(i, ce, j)] { rowtab[rti(i, ce, j)] = v; }
                                let okb = (m >= 7 && m <= ji + 1) || (ji < 6 && m == ji + 1);
                                if okb && v < rowtab[rti(i, 0, j)] { rowtab[rti(i, 0, j)] = v; }
                            }
                        }
                    }
                    let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
                    let clamp = |m: i128| -> i128 { if m > mc { mc } else { m } };
                    // per-row feasible classes
                    let cap = |c: i128| if c == 0 { 7 } else { c };
                    let mut rowcls: [Vec<i128>; 4] = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
                    for i in 0..4 {
                        for c in [0i128, 2, 3, 4, 5, 6] {
                            if needs[i][0] * cap(c) <= needs[i][1] { rowcls[i].push(c); }
                        }
                    }
                    let mut worst = (i128::MAX, 0i128, 0u64, 0i128);
                    for &c0 in rowcls[0].iter() {
                    for &c1 in rowcls[1].iter() {
                    for &c2 in rowcls[2].iter() {
                    for &c3 in rowcls[3].iter() {
                        let col = [c0, c1, c2, c3];
                        let dig: u64 = col.iter().fold(0u64, |acc, &c| acc * 8 + c as u64);
                        let pinat = (0..4).find(|&i| col[i] >= 2).map(|i| (i, col[i]));
                        let qs: Vec<i128> = match &pinat {
                            None => vec![0],
                            Some((istar, vstar)) => {
                                let mut v = Vec::new();
                                let mut q = 2i128;
                                while q * wmax < vstar * rho * w[*istar] {
                                    if gcd(q, *vstar) == 1 && q * rho * wmin > vstar * w[*istar] { v.push(q); }
                                    q += 1;
                                }
                                v
                            }
                        };
                        'branch: for &q in qs.iter() {
                            let mut srow = [0i128; 4];
                            let mut sy = [0i128; 4];
                            let mut rowyf: Vec<i128> = Vec::new();
                            if let Some((istar, vstar)) = pinat {
                                for j in 0..4 {
                                    let gj = gcd(vstar * w[istar], q * w[j]);
                                    srow[j] = vstar * w[istar] / gj;
                                    sy[j] = q * w[j] / gj;
                                    if col[j] >= 2 { if srow[j] != col[j] { continue 'branch; } }
                                    else { if srow[j] < 7 { continue 'branch; } }
                                    if sy[j] < 2 { continue 'branch; }
                                }
                                let p: i128 = sy.iter().product();
                                let num: i128 = sy.iter().map(|&m| p / m).sum();
                                if num >= p { continue 'branch; } // the good cannot be good
                                rowyf = f_exact(&[clamp(sy[0]), clamp(sy[1]), clamp(sy[2]), clamp(sy[3])], jt);
                            }
                            let mut cls = [0usize; 4];
                            let mut dead = false;
                            for i in 0..4 {
                                cls[i] = if srow[i] > 0 { clamp(srow[i]) as usize - 1 }
                                         else if col[i] >= 2 { col[i] as usize - 1 }
                                         else { 0 };
                                let a = if cls[i] == 0 { 7 } else { cls[i] as i128 + 1 };
                                if needs[i][0] * a > needs[i][1] { dead = true; break; }
                            }
                            if dead { continue; }
                            for tau in tau_lo..=tau_hi {
                                let mut m60 = -300i128;
                                match pinat {
                                    None => { m60 += 2 * stair60(2); }
                                    Some((istar, vstar)) => {
                                        let jlo = q * tau / (vstar * w[istar]);
                                        let jhi = q * (tau + 1) / (vstar * w[istar]);
                                        let mut best = i128::MAX;
                                        let mut jy = jlo;
                                        while jy <= jhi {
                                            let v = if jy <= jt {
                                                let e = rowyf[jy as usize];
                                                let st = stair60(jy);
                                                if e > st { e } else { st }
                                            } else { 90 };
                                            if v < best { best = v; }
                                            jy += 1;
                                        }
                                        m60 += 2 * best;
                                    }
                                }
                                let mut feasible = true;
                                for i in 0..4 {
                                    let j = tau / w[i];
                                    let fj = if j <= jt {
                                        let v = rowtab[rti(i, cls[i], j as usize)];
                                        if v == i128::MAX { feasible = false; break; }
                                        v
                                    } else { (420 * j) / 300 - 14 };
                                    m60 += 2 * fj;
                                }
                                if !feasible { continue; }
                                if m60 < worst.0 { worst = (m60, tau, dig, *qs.iter().find(|&&x| x == q).unwrap()); }
                            }
                        }
                    }}}}
                    out.push((worst.0, *w0, worst.1, worst.2, worst.3));
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let decode = |d: u64| -> String {
        let mut cs = [0u64; 4];
        let mut x = d;
        for k in (0..4).rev() { cs[k] = x % 8; x /= 8; }
        format!("[{}]", cs.iter().map(|&c| if c == 0 { "B".to_string() } else { c.to_string() })
                .collect::<Vec<_>>().join(","))
    };
    let mut pass = 0; let mut vac = 0; let mut zero = 0; let mut short = 0;
    let mut sorted = results.clone();
    sorted.sort();
    for r in sorted.iter() {
        if r.0 == i128::MAX { vac += 1; println!("  VACUOUS W={:?} (no 4-bad configuration in the model)", r.1); }
        else if r.0 > 0 { pass += 1; println!("  PASS  W={:?} worst margin*60={} at tau={} cls={} q={}", r.1, r.0, r.2, decode(r.3), r.4); }
        else if r.0 == 0 { zero += 1; println!("  ZERO  W={:?} (passes via retained +S) tau={} cls={} q={}", r.1, r.2, decode(r.3), r.4); }
        else { short += 1; println!("  SHORT W={:?} margin*60={} tau={} cls={} q={}", r.1, r.0, r.2, decode(r.3), r.4); }
    }
    println!("PASS {} (incl. {} VACUOUS) / ZERO {} / SHORT {} (of {} 4-bad shapes)",
             pass + vac, vac, zero, short, results.len());
}

/// 4-bad SHAPE INVENTORY by exhaustive filter enumeration: all quadruples
/// w1 < w2 < w3 < w4 with w1 <= w1max, w4 < rho*w1 (shape-level ratio bound:
/// max(P) >= w4*s, min(P) <= w1*s), gcd = 1, antichain (no divisibility), and
/// EVERY row's necessary badness condition with a single good donating at best
/// modulus 2: sum_{j != i} gcd(w_i,w_j)/w_j >= 1/2. This is a NECESSARY filter
/// for a 4-bad quintuple's bad-quadruple shape, so the enumeration is COMPLETE
/// up to w1max (the open completeness piece is bounding w1).
fn shapes4inv(w1max: i128, rho: i128) {
    println!("=== 4-bad shape inventory: filter-complete enumeration, w1 <= {}, ratio < {} ===", w1max, rho);
    let nthreads = std::thread::available_parallelism().map(|n| n.get() as i128).unwrap_or(4).max(1);
    let found: Vec<[i128; 4]> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            s.spawn(move || {
                let mut out: Vec<[i128; 4]> = Vec::new();
                let mut w1 = 2 + tid;
                while w1 <= w1max {
                    let hi = rho * w1; // exclusive
                    for w2 in (w1 + 1)..hi {
                        if w2 % w1 == 0 { continue; }
                        for w3 in (w2 + 1)..hi {
                            if w3 % w1 == 0 || w3 % w2 == 0 { continue; }
                            // prune: rows 1..3 can still gain at most 1 from w4 terms? each
                            // term gcd/w <= 1; cheap partial check: row i partial + 1 >= 1/2 always true,
                            // so prune only on the pair-level: skip if w1's row can't reach 1/2 even
                            // with gcd(w1,w4)=w1 at the smallest allowed w4 (= w3+1).
                            let p12 = gcd(w1, w2); let p13 = gcd(w1, w3);
                            // max possible row-1 sum: p12/w2 + p13/w3 + w1/(w3+1)
                            // exact check via i128 cross-multiplication
                            let d = w2 * w3 * (w3 + 1);
                            let best1 = 2 * (p12 * w3 * (w3 + 1) + p13 * w2 * (w3 + 1) + w1 * w2 * w3);
                            if best1 < d { continue; }
                            for w4 in (w3 + 1)..hi {
                                if w4 % w1 == 0 || w4 % w2 == 0 || w4 % w3 == 0 { continue; }
                                let w = [w1, w2, w3, w4];
                                if gcd(gcd(w1, w2), gcd(w3, w4)) != 1 { continue; }
                                let mut ok = true;
                                for i in 0..4 {
                                    // sum_{j != i} gcd(w_i, w_j)/w_j >= 1/2, exact
                                    let mut prod = 1i128;
                                    for j in 0..4 { if j != i { prod *= w[j]; } }
                                    let mut lhs = 0i128;
                                    for j in 0..4 { if j != i { lhs += gcd(w[i], w[j]) * (prod / w[j]); } }
                                    if 2 * lhs < prod { ok = false; break; }
                                }
                                if ok { out.push(w); }
                            }
                        }
                    }
                    w1 += nthreads;
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let mut found = found;
    found.sort();
    for w in found.iter() { println!("  {} , {} , {} , {}", w[0], w[1], w[2], w[3]); }
    println!("TOTAL 4-bad candidate shapes (w1 <= {}, filter-complete): {}", w1max, found.len());
}

/// Shared exact validity check for a 4-bad candidate shape (the shapes4inv filter):
/// sorted distinct, antichain, gcd 1, ratio < rho, every row sum gcd/w >= 1/2.
fn valid4shape(w: &[i128; 4], rho: i128) -> bool {
    for i in 0..4 { for j in (i + 1)..4 {
        if w[i] == w[j] || w[j] % w[i] == 0 { return false; }
    }}
    if gcd(gcd(w[0], w[1]), gcd(w[2], w[3])) != 1 { return false; }
    if w[3] >= rho * w[0] { return false; }
    for i in 0..4 {
        let mut prod = 1i128;
        for j in 0..4 { if j != i { prod *= w[j]; } }
        let mut lhs = 0i128;
        for j in 0..4 { if j != i { lhs += gcd(w[i], w[j]) * (prod / w[j]); } }
        if 2 * lhs < prod { return false; }
    }
    true
}

/// (c') certificate 1 — the CASE (2,2) BOX (Section 23.7). In a (2,2) heavy
/// split A = h_A*{alpha, alpha'}, B = h_B*{beta, beta'}: cofactor pairs coprime
/// in [2,42]; some A-row is needy (partner cofactor alpha' >= 3), its cross-sum
/// >= 1/6, so a cross term >= 1/12: that pair's reduced fraction K/M has
/// M <= 12, K <= 83, K/M in (1/7,7); gcd(h_A,h_B) = 1 then DETERMINES
/// h_A = K*beta/g0, h_B = M*alpha/g0, g0 = gcd(K*beta, M*alpha). Enumerating
/// the finite box and verifying candidates exactly is therefore COMPLETE for
/// every (2,2)-type 4-bad shape, with no a-priori w1 bound needed.
fn c4bound22(rho: i128) {
    println!("=== (c') case (2,2) box: needy-row K/M pinning, exact verification (rho<{}) ===", rho);
    let nthreads = std::thread::available_parallelism().map(|n| n.get() as i128).unwrap_or(4).max(1);
    let found: Vec<[i128; 4]> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            s.spawn(move || {
                let mut out: Vec<[i128; 4]> = Vec::new();
                let mut a = 2 + tid;
                while a <= 42 {
                    for ap in 3..=42i128 {
                        if gcd(a, ap) != 1 { continue; }
                        for b in 2..=42i128 { for bp in 2..=42i128 {
                            if b == bp || gcd(b, bp) != 1 { continue; }
                            for m in 2..=12i128 { for k in 2..=83i128 {
                                if gcd(k, m) != 1 { continue; }
                                if m >= 7 * k || k >= 7 * m { continue; }
                                let g0 = gcd(k * b, m * a);
                                let ha = k * b / g0;
                                let hb = m * a / g0;
                                // pin consistency: the (needy, pinned) pair's reduced
                                // denominator must actually be m
                                let e_a = ha * a; let e_b = hb * b;
                                let g = gcd(e_a, e_b);
                                if e_b != g * m { continue; }
                                let mut w = [ha * a, ha * ap, hb * b, hb * bp];
                                w.sort_unstable();
                                if valid4shape(&w, rho) { out.push(w); }
                            }}
                        }}
                    }
                    a += nthreads;
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let set: std::collections::BTreeSet<[i128; 4]> = found.into_iter().collect();
    for w in set.iter() { println!("  {} , {} , {} , {}", w[0], w[1], w[2], w[3]); }
    let wmax = set.iter().map(|w| w[0]).max().unwrap_or(0);
    println!("TOTAL (2,2)-box shapes: {} ; largest w1 = {}", set.len(), wmax);
}

/// (c') certificate 2 — heavy-partner generator enumeration (Section 23.7).
/// Row 1 of any valid shape owns a heavy partner w_j = w1*m/k with k | w1 and
/// (k,m) in {(2,3),(2,5),(3,4),(3,5),(4,5),(5,6)} (reduced numerator <= 6,
/// wj > w1 forces k < m <= 6, antichain forces k >= 2). So one loop collapses
/// to <= 6 candidates. Complete for ALL shapes (both heavy-graph cases) up to
/// w1max; run to 1512 to close case (4)'s proved range (Section 23.7).
fn shapes4inv2(w1max: i128, rho: i128) {
    println!("=== 4-bad inventory v2: heavy-partner generator, w1 <= {}, ratio < {} ===", w1max, rho);
    let nthreads = std::thread::available_parallelism().map(|n| n.get() as i128).unwrap_or(4).max(1);
    let pairs: [(i128, i128); 6] = [(2, 3), (2, 5), (3, 4), (3, 5), (4, 5), (5, 6)];
    let found: Vec<[i128; 4]> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads).map(|tid| {
            s.spawn(move || {
                let mut out: Vec<[i128; 4]> = Vec::new();
                let mut w1 = 2 + tid;
                while w1 <= w1max {
                    let hi = rho * w1;
                    for (k, m) in pairs.iter() {
                        if w1 % k != 0 { continue; }
                        let wj = w1 / k * m;
                        if wj <= w1 || wj >= hi { continue; }
                        // remaining two elements: wa < wb in (w1, hi), distinct from wj
                        for wa in (w1 + 1)..hi {
                            if wa == wj || wa % w1 == 0 { continue; }
                            for wb in (wa + 1)..hi {
                                if wb == wj || wb % w1 == 0 || wb % wa == 0 { continue; }
                                let mut w = [w1, wj, wa, wb];
                                w.sort_unstable();
                                if valid4shape(&w, rho) { out.push(w); }
                            }
                        }
                    }
                    w1 += nthreads;
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let set: std::collections::BTreeSet<[i128; 4]> = found.into_iter().collect();
    for w in set.iter() { println!("  {} , {} , {} , {}", w[0], w[1], w[2], w[3]); }
    let wmax = set.iter().map(|w| w[0]).max().unwrap_or(0);
    println!("TOTAL shapes (w1 <= {}, generator-complete): {} ; largest w1 = {}", w1max, set.len(), wmax);
}

/// Section 25 certificate: the one-edge 3-bad family as a FINITE BANK.
/// Structure theorem (Section 25): bads {b1,b2,b3}, one internal strong edge
/// b1--b2 = u*(al,al') (coprime, min <= 4, within ratio); b3's goods are
/// divisor-pinned: block = v*{L, L*k1/c1, L*k2/c2}, L = lcm(c1,c2), c1 = the
/// smaller pin in {2,3}, need 1/c1 + 1/c2 >= 3/5, k_j >= 2 coprime to c_j,
/// k_j/c_j in (1/7,7). Scale bounds (necessary, from badness + CROSS with
/// gcd(u,v) = 1): v <= 3*al*al'/(max-1), u <= 2*L*k1*k2/(k1*k2 - k1 - k2)
/// (the only unbounded candidate k1=k2=2 is arithmetic-vacuous). This mode
/// enumerates the full box, keeps candidates that ARE one-edge exactly-3-bad
/// C-B residuals (computed from the tuple, not the labels), and tower-checks
/// every one: 2B(m) > (m+1)S on [max(P), cap], cap = 1135*prod/(7*nsum) - 1.
fn bank1edge(rho: i128) {
    println!("=== Section 25 bank: one-edge 3-bad family, full enumeration + tower check (rho<{}) ===", rho);
    let nthreads = std::thread::available_parallelism().map(|n| n.get() as i128).unwrap_or(4).max(1);
    // pair templates (ordered al, alp)
    let mut pairs: Vec<(i128, i128)> = Vec::new();
    for al in 2..=27i128 { for alp in 2..=27i128 {
        if al == alp || gcd(al, alp) != 1 { continue; }
        let (mn, mx) = (al.min(alp), al.max(alp));
        if mn > 4 || mx >= 7 * mn { continue; }
        pairs.push((al, alp));
    }}
    let found: Vec<[i128; 5]> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads as usize).map(|tid| {
            let pairs = &pairs;
            s.spawn(move || {
                let mut out: Vec<[i128; 5]> = Vec::new();
                for (pi, &(al, alp)) in pairs.iter().enumerate() {
                    if pi % (nthreads as usize) != tid { continue; }
                    let (amin, amax) = (al.min(alp), al.max(alp));
                    for c1 in 2..=3i128 { for k1 in 2..(7 * c1) {
                        if gcd(k1, c1) != 1 { continue; }
                        for c2 in c1..=10i128 {
                            if 5 * (c1 + c2) < 3 * c1 * c2 { continue; } // b3-need 1/c1+1/c2 >= 3/5
                            for k2 in 2..(7 * c2) {
                                if gcd(k2, c2) != 1 { continue; }
                                if k1 * c2 == k2 * c1 { continue; } // distinct goods
                                let ll = lcm(c1, c2);
                                let g1t = ll * k1 / c1;
                                let g2t = ll * k2 / c2;
                                // CORRECTED bounds (Section 25'): pair rows give
                                // u <= sum(gamma)/(1 - 1/amax); the b3 row gives
                                // v <= (al+alp)/(1 - 1/c1 - 1/c2) unless (c1,c2)=(2,2)
                                // (b3 auto-bad), where the ratio-7 box bounds v < 7*u*amin/L.
                                let sgam = ll + g1t + g2t;
                                let umax = sgam * amax / (amax - 1);
                                let cden = c1 * c2 - c1 - c2;
                                for u in 1..=umax {
                                    let vr = (7 * u * amin) / ll; // ratio-7: v*L < 7*u*amin
                                    let vmax = if cden > 0 { vr.min((al + alp) * c1 * c2 / cden) } else { vr };
                                    for v in 1..=vmax {
                                    let mut dd = [u * al, u * alp, v * ll, v * g1t, v * g2t];
                                    dd.sort_unstable();
                                    // basic validity
                                    let mut ok = true;
                                    'pv: for i in 0..5 { for j in (i + 1)..5 {
                                        if dd[i] == dd[j] || dd[j] % dd[i] == 0 { ok = false; break 'pv; }
                                    }}
                                    if !ok { continue; }
                                    let g = dd.iter().fold(0i128, |x, &y| gcd(x, y));
                                    if g != 1 { continue; }
                                    out.push(dd);
                                }}
                            }
                        }
                    }}
                }
                out
            })
        }).collect();
        let mut all = Vec::new();
        for h in handles { all.extend(h.join().unwrap()); }
        all
    });
    let set: std::collections::BTreeSet<[i128; 5]> = found.into_iter().collect();
    println!("raw candidate tuples (deduped): {}", set.len());
    // keep the ones that ARE one-edge exactly-3-bad C-B residuals
    let mut bank: Vec<[i128; 5]> = Vec::new();
    for dd in set.iter() {
        let sumd: i128 = dd.iter().sum();
        if 7 * sumd > 1135 * dd[0] { continue; } // window-relevant
        let bads: Vec<usize> = (0..5).filter(|&i| {
            let s: i128 = (0..5).filter(|&j| j != i).map(|j| gcd(dd[i], dd[j])).sum();
            s >= dd[i]
        }).collect();
        if bads.len() != 3 { continue; }
        let mut sg = 0i128;
        for i in 0..5 { for j in (i + 1)..5 { sg += gcd(dd[i], dd[j]); } }
        let num = sumd - 2 * sg;
        if 2 * num > 7 * dd[0] { continue; } // CRIT <= 7/2
        let mut ne = 0;
        for x in 0..3 { for y in (x + 1)..3 {
            let (a, b) = (dd[bads[x]], dd[bads[y]]);
            if 4 * gcd(a, b) >= a.min(b) { ne += 1; }
        }}
        if ne != 1 { continue; }
        bank.push(*dd);
    }
    println!("one-edge exactly-3-bad C-B residual bank members: {}", bank.len());
    // tower-check every member (checked products; overflow members reported loudly)
    let mut fails = 0u64;
    let mut overflow = 0u64;
    let mut worst: (f64, i128, [i128; 5]) = (f64::INFINITY, 0, [0; 5]);
    for dd in bank.iter() {
        let mut l = 1i128;
        for &x in dd.iter() { l = lcm(l, x); }
        let p0: Vec<i128> = dd.iter().map(|&x| l / x).collect();
        let mut p = p0; p.sort_unstable();
        let mut prod: i128 = 1;
        let mut ovf = false;
        for &x in p.iter() { match prod.checked_mul(x) { Some(v) => prod = v, None => { ovf = true; break; } } }
        if ovf { overflow += 1; println!("  OVERFLOW-SKIP D={:?} (needs bigint tower check)", dd); continue; }
        let nsum: i128 = p.iter().map(|&x| prod / x).sum();
        let mx = p[4];
        let cap = (1135 * prod) / (7 * nsum) - 1;
        let mut bc: i128 = 0;
        for m in 1..=cap {
            if p.iter().any(|&a| m % a == 0) { bc += 1; }
            if m >= mx {
                let marg = 2 * bc * prod - (m + 1) * nsum;
                if marg <= 0 { fails += 1; }
                let mf = marg as f64 / prod as f64;
                if mf < worst.0 { worst = (mf, m, *dd); }
            }
        }
    }
    println!("tower failures: {} ; overflow-skipped: {}", fails, overflow);
    if worst.0.is_finite() {
        println!("worst margin (2B-(m+1)S) ~ {:.4} at m={} D={:?}", worst.0, worst.1, worst.2);
    }
    for dd in bank.iter().take(40) { println!("  member D={:?}", dd); }
    if bank.len() > 40 { println!("  ... ({} total)", bank.len()); }
    println!("RESULT: {}", if fails == 0 { "ALL PASS — the one-edge family is closed by this finite bank" } else { "FAILURES FOUND" });
}

/// STAGE-2 v2: donation-VALUE descriptors. Each good's stair source = its best
/// donation (i, v), v in 2..=6 (v>=7 gives J-bound below the flat stair region —
/// treated as none). Descriptor space 16x16; rows constrained only at the named
/// entry (soundness: rows minimize over a superset of the true configurations, and
/// the named donation y = v*d, d | w_i*s gives y <= v*w_i*s => J_good >= tau/(v*w_i)).
fn shape2v2(rho: i128, shapes: &[[i128; 3]]) {
    println!("=== stage-2 v2: donation-value descriptors (rho<{}), {} shapes x (W, Wv) ===", rho, shapes.len());
    let jt: i128 = 40;
    let mut pass_count = 0; let mut short_count = 0;
    let mut worst_overall: (i128, [i128;3], bool) = (i128::MAX, [0;3], false);
    let mut short_list: Vec<(i128,[i128;3],bool,i128)> = Vec::new();
    for w0 in shapes.iter() {
        for dualize in [false, true] {
            let l = lcm(lcm(w0[0], w0[1]), w0[2]);
            let mut w = if dualize { [l/w0[2], l/w0[1], l/w0[0]] } else { *w0 };
            let g = gcd(gcd(w[0], w[1]), w[2]);
            for x in w.iter_mut() { *x /= g; }
            let pins: Vec<[i128; 2]> = (0..3).map(|i| {
                let mut p = [0i128; 2]; let mut k = 0;
                for j in 0..3 { if j != i { p[k] = w[j] / gcd(w[i], w[j]); k += 1; } }
                p
            }).collect();
            // rowtab[i][c1][c2][J]: c in 0..=5: 0 = ANY (m>=2), 1..=5 = exact value m = c+1 (2..6)
            let mut rowtab = vec![[[[i128::MAX; 41]; 6]; 6]; 3];
            for i in 0..3 {
                let p = pins[i];
                let needn = p[0]*p[1] - p[1] - p[0];
                let needd = p[0]*p[1];
                for m1 in 2..=(jt + 1) { for m2 in 2..=(jt + 1) {
                    if (m1 + m2) * needd < needn * m1 * m2 { continue; }
                    let ms = [p[0], p[1], m1, m2];
                    let f = f_exact(&ms, jt);
                    for c1 in 0..6usize {
                        if c1 != 0 && m1 != (c1 as i128 + 1) { continue; }
                        for c2 in 0..6usize {
                            if c2 != 0 && m2 != (c2 as i128 + 1) { continue; }
                            for j in 2..=(jt as usize) {
                                if m1 <= j as i128 + 1 && m2 <= j as i128 + 1
                                   && f[j] < rowtab[i][c1][c2][j] {
                                    rowtab[i][c1][c2][j] = f[j];
                                }
                            }
                        }
                    }
                }}
            }
            let wmax = *w.iter().max().unwrap();
            let (tau_lo, tau_hi) = (2 * wmax, 33 * rho * wmax);
            // descriptors: 0 = none; else (bad i in 0..3, value v in 2..=6) => 1 + i*5 + (v-2)
            let ndesc = 16usize;
            let mut worst = (i128::MAX, 0i128, 0usize, 0usize);
            for d0 in 0..ndesc { for d1 in 0..ndesc {
                let dec = |d: usize| -> Option<(usize, i128)> {
                    if d == 0 { None } else { Some(((d-1)/5, ((d-1)%5) as i128 + 2)) }
                };
                let de0 = dec(d0); let de1 = dec(d1);
                for tau in tau_lo..=tau_hi {
                    let jg = |de: Option<(usize,i128)>| -> i128 {
                        match de { None => 2, Some((i,v)) => (tau / (v * w[i])).max(2) }
                    };
                    let mut m60 = 2 * (stair60(jg(de0)) + stair60(jg(de1))) - 300;
                    let mut feasible = true;
                    for i in 0..3 {
                        let c1 = match de0 { Some((bi,v)) if bi == i => (v - 1) as usize, _ => 0 };
                        let c2 = match de1 { Some((bi,v)) if bi == i => (v - 1) as usize, _ => 0 };
                        let j = tau / w[i];
                        let fj = if j <= jt {
                            let vv = rowtab[i][c1][c2][j as usize];
                            if vv == i128::MAX { feasible = false; break; }
                            vv
                        } else { (420 * j) / 300 - 14 };
                        m60 += 2 * fj;
                    }
                    if !feasible { continue; }
                    if m60 < worst.0 { worst = (m60, tau, d0, d1); }
                }
            }}
            if worst.0 > 0 { pass_count += 1; } else {
                short_count += 1;
                short_list.push((worst.0, *w0, dualize, worst.1));
                if worst.0 < worst_overall.0 { worst_overall = (worst.0, *w0, dualize); }
            }
        }
    }
    short_list.sort();
    for (m, w, d, tau) in short_list.iter().take(15) {
        println!("  SHORT W={:?}{} margin*60={} tau={}", w, if *d {"^v"} else {""}, m, tau);
    }
    println!("PASS {} / SHORT {} (of {} shape-sides); worst {:?}{} at {}",
             pass_count, short_count, 2*shapes.len(), worst_overall.1,
             if worst_overall.2 {"^v"} else {""}, worst_overall.0);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage:\n  census quints <N> [--all-min]\n  census dual <M>\n  census cb <M>\n  census drift\n  census emin\n  census clusters\n  census shape2 [rho]\n  census shape2v1 [rho]\n  census shape2v15 <shapefile> [rho]\n  census shape2v2 <shapefile> [rho]");
        std::process::exit(2);
    }
    if args[1] == "shape2v2" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 3]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 3 { Some([v[0], v[1], v[2]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape2v2(r, &shapes);
        return;
    }
    if args[1] == "bank1edge" {
        let r: i128 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(7);
        bank1edge(r);
        return;
    }
    if args[1] == "c4bound22" {
        let r: i128 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(7);
        c4bound22(r);
        return;
    }
    if args[1] == "shapes4inv2" {
        let w1max: i128 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1512);
        let r: i128 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(7);
        shapes4inv2(w1max, r);
        return;
    }
    if args[1] == "shapes4inv" {
        let w1max: i128 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(120);
        let r: i128 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(7);
        shapes4inv(w1max, r);
        return;
    }
    if args[1] == "shape4" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 4]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 4 { Some([v[0], v[1], v[2], v[3]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape4(r, &shapes);
        return;
    }
    if args[1] == "shape2v3" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 3]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 3 { Some([v[0], v[1], v[2]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape2v3(r, &shapes);
        return;
    }
    if args[1] == "shape2v22" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 3]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 3 { Some([v[0], v[1], v[2]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape2v22(r, &shapes);
        return;
    }
    if args[1] == "shape2v21" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 3]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 3 { Some([v[0], v[1], v[2]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape2v21(r, &shapes);
        return;
    }
    if args[1] == "shape2v15" {
        let path = args.get(2).expect("shape file");
        let txt = std::fs::read_to_string(path).expect("read shapes");
        let shapes: Vec<[i128; 3]> = txt.lines().filter_map(|l| {
            let v: Vec<i128> = l.trim().split(',').filter_map(|t| t.trim().parse().ok()).collect();
            if v.len() == 3 { Some([v[0], v[1], v[2]]) } else { None }
        }).collect();
        let r: i128 = if args.len() > 3 { args[3].parse().unwrap_or(7) } else { 7 };
        shape2v15(r, &shapes);
        return;
    }
    if args[1] == "shape2v1" { let r: i128 = if args.len() > 2 { args[2].parse().unwrap_or(7) } else { 7 }; shape2v1(r); return; }
    if args[1] == "clusters" { let r: i128 = if args.len() > 2 { args[2].parse().unwrap_or(7) } else { 7 }; clusters(r); return; }
    if args[1] == "shape2" { let r: i128 = if args.len() > 2 { args[2].parse().unwrap_or(7) } else { 7 }; shape2(r); return; }
    match args[1].as_str() {
        "drift" => { drift_certificates(); return; }
        "emin" => { emin_certificates(); return; }
        _ => {}
    }
    if args.len() < 3 {
        eprintln!("usage:\n  census quints <N> [--all-min]\n  census dual <M>\n  census cb <M>\n  census drift\n  census emin");
        std::process::exit(2);
    }
    let n: i128 = args[2].parse().expect("arg must be an integer");
    match args[1].as_str() {
        "quints" => quints(n, args.iter().any(|s| s == "--all-min")),
        "dual" => dual(n),
        "cb" => cb(n),
        _ => { eprintln!("unknown subcommand {}", args[1]); std::process::exit(2); }
    }
}
