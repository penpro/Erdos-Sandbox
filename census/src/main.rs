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

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage:\n  census quints <N> [--all-min]\n  census dual <M>");
        std::process::exit(2);
    }
    let n: i128 = args[2].parse().expect("arg must be an integer");
    match args[1].as_str() {
        "quints" => quints(n, args.iter().any(|s| s == "--all-min")),
        "dual" => dual(n),
        _ => { eprintln!("unknown subcommand {}", args[1]); std::process::exit(2); }
    }
}
