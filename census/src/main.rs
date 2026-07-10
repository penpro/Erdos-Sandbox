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
fn cb(m: i128) {
    let mut count: u64 = 0;
    let mut resid: Vec<(i128, i128, [i128; 5])> = Vec::new(); // (crit_num, d_min, D) with crit = num/d_min <= 7/2
    let mut min_crit_num: i128 = i128::MAX; // track min of num/d1 as fraction: compare a/b vs c/d by cross-mult
    let mut min_crit: (i128, i128, [i128; 5]) = (0, 1, [0; 5]);

    for a in 2..=m {
        // window prune: 7*(a+b+c+d+e) <= 1135*a with a<b<c<d<e  =>  each of b..e < (1135-7)/7*a/4-ish;
        // use exact caps at each level: 7*(partial + remaining_count*next) <= 1135*a.
        let cap_e = |partial: i128| (1135 * a - 7 * partial) / 7; // e <= cap_e(a+b+c+d)
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
                        // <=2-good on P side == <=2 co-good on D side (g_i < d_i)
                        let mut cogood = 0;
                        for i in 0..5 {
                            let mut s = 0i128;
                            for j in 0..5 { if j != i { s += gcd(dd[i], dd[j]); } }
                            if s < dd[i] { cogood += 1; }
                        }
                        if cogood > 2 { continue; }
                        // window: 7*Sum(D) <= 1135*min(D)  (redundant after caps, kept for safety)
                        let sumd: i128 = dd.iter().sum();
                        if 7 * sumd > 1135 * dd[0] { continue; }
                        count += 1;
                        // CRIT = (SumD - 2*sum_pairs gcd)/d1  vs 7/2
                        let mut sg = 0i128;
                        for i in 0..5 { for j in (i + 1)..5 { sg += gcd(dd[i], dd[j]); } }
                        let num = sumd - 2 * sg;
                        // num/d1 <= 7/2  <=>  2*num <= 7*d1
                        if 2 * num <= 7 * dd[0] {
                            resid.push((num, dd[0], dd));
                        }
                        // track global min crit
                        if (num as i128) * min_crit.1 < min_crit_num * dd[0] || min_crit_num == i128::MAX {
                            if min_crit_num == i128::MAX || num * min_crit.1 < min_crit.0 * dd[0] {
                                min_crit = (num, dd[0], dd);
                                min_crit_num = num;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("=== C-B criterion sweep, dual cores in [2,{}] ===", m);
    println!("<=2-good window-relevant (via dual): {}", count);
    println!("C-B RESIDUAL (crit <= 7/2): {} dual cores", resid.len());
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

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage:\n  census quints <N> [--all-min]\n  census dual <M>\n  census cb <M>");
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
