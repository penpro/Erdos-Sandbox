//! Fast exact-integer verification harness for Erdos Problem 488.
//!
//! EP488 (multiples version): for a finite set A of integers >= 2, with
//! B = { k >= 1 : a | k for some a in A } and B(x) = |B cap [1,x]|,
//! is it true that  n * B(m) < 2 * m * B(n)  for all  m > n >= max(A) ?
//!
//! We check this exactly (integer arithmetic, u128 products -- no floats in any
//! decision) on a *window* [max(A), W]. For a fixed n, the inequality is hardest
//! for the m > n maximizing B(m)/m; a single suffix pass maintains that champion,
//! so each set costs O(W). This is a bounded-window check = strong evidence
//! within the window (NOT a proof; the theorem for |P|<=3 is proved elsewhere --
//! see ../lean/ep488 and ../writeup). Intended use: hunt the OPEN |P| >= 4
//! frontier at a scale Python cannot reach.
//!
//! Usage:
//!   fastcheck selftest
//!   fastcheck triples <amax> [window_factor]
//!   fastcheck quads   <amax> [window_factor] [--uncovered]
//!   fastcheck quints  <amax> [window_factor] [--uncovered]
//!   fastcheck set <a,b,c,...> [window_factor]
//!   fastcheck classify <a,b,c,...>
//!   fastcheck cert <a,b,c,...> [lcm_cap]
//!   fastcheck sweep-quad-cert <amax> [lcm_cap]
//!   fastcheck bench <amax>

use std::cmp::Ordering;
use std::time::Instant;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExactRatio {
    num: u128,
    den: u128,
}

impl ExactRatio {
    fn new(num: u128, den: u128) -> Self {
        assert!(den > 0);
        let g = gcd_u128(num, den);
        Self {
            num: num / g,
            den: den / g,
        }
    }

    fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    fn add(self, other: Self) -> Self {
        Self::new(
            self.num * other.den + other.num * self.den,
            self.den * other.den,
        )
    }

    fn lt(self, other: Self) -> bool {
        self.num * other.den < other.num * self.den
    }

    fn le(self, other: Self) -> bool {
        self.num * other.den <= other.num * self.den
    }

    fn gt(self, other: Self) -> bool {
        self.num * other.den > other.num * self.den
    }

    fn as_f64(self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

impl Ord for ExactRatio {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.num * other.den).cmp(&(other.num * self.den))
    }
}

impl PartialOrd for ExactRatio {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Display for ExactRatio {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.den == 1 {
            write!(f, "{} ({:.12})", self.num, self.as_f64())
        } else {
            write!(f, "{}/{} ({:.12})", self.num, self.den, self.as_f64())
        }
    }
}

#[derive(Clone, Debug)]
struct CertWitness {
    x: Option<u64>,
    value: ExactRatio,
}

impl CertWitness {
    fn new(x: Option<u64>, value: ExactRatio) -> Self {
        Self { x, value }
    }
}

impl std::fmt::Display for CertWitness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.x {
            Some(x) => write!(f, "{} at x={}", self.value, x),
            None => write!(f, "{} at density limit", self.value),
        }
    }
}

#[derive(Clone, Debug)]
struct PeriodicCertificate {
    lcm: u64,
    density_count: u64,
    alpha: CertWitness,
    beta: CertWitness,
    beta_over_alpha: ExactRatio,
    ordering_free: bool,
    union_bound_separator: bool,
}

/// no element divides another
fn is_primitive(a: &[u64]) -> bool {
    for i in 0..a.len() {
        for j in 0..a.len() {
            if i != j && a[j] % a[i] == 0 {
                return false;
            }
        }
    }
    true
}

/// prefix counts of B on [0, w]: pref[x] = |{1<=t<=x : some d in a divides t}|
fn b_prefix(a: &[u64], w: u64) -> Vec<u32> {
    let wu = w as usize;
    let mut inb = vec![false; wu + 1];
    for &d in a {
        let mut x = d as usize;
        while x <= wu {
            inb[x] = true;
            x += d as usize;
        }
    }
    let mut pref = vec![0u32; wu + 1];
    let mut c = 0u32;
    for x in 1..=wu {
        if inb[x] {
            c += 1;
        }
        pref[x] = c;
    }
    pref
}

/// Check EP488 on the window [maxA, w]. Returns (counterexample?, worst_ratio).
/// worst ratio = (B(m)/m)/(B(n)/n) = B(m)*n / (B(n)*m), reported as (num, den).
/// A counterexample is any (n,m), m>n>=maxA, with n*B(m) >= 2*m*B(n).
fn ep488_window(a: &[u64], w: u64) -> (Option<(u64, u64)>, (u128, u128)) {
    let maxa = *a.iter().max().unwrap();
    if w <= maxa {
        return (None, (0, 1));
    }
    let pref = b_prefix(a, w);
    let mut champ: u64 = 0; // argmax_{m>n} B(m)/m over current pool; 0 = none
    let mut ce: Option<(u64, u64)> = None;
    let mut worst_num: u128 = 0;
    let mut worst_den: u128 = 1;
    let mut n = w - 1;
    loop {
        let m_new = n + 1;
        let bm_new = pref[m_new as usize] as u128;
        if champ == 0
            || bm_new * (champ as u128) > (pref[champ as usize] as u128) * (m_new as u128)
        {
            champ = m_new;
        }
        let bn = pref[n as usize] as u128;
        if bn > 0 {
            let bm = pref[champ as usize] as u128;
            let lhs = (n as u128) * bm; // n*B(m)
            let rhs = 2 * (champ as u128) * bn; // 2*m*B(n)
            if lhs >= rhs && ce.is_none() {
                ce = Some((n, champ));
            }
            let rn = bm * (n as u128);
            let rd = bn * (champ as u128);
            if rn * worst_den > worst_num * rd {
                worst_num = rn;
                worst_den = rd;
            }
        }
        if n == maxa {
            break;
        }
        n -= 1;
    }
    (ce, (worst_num, worst_den))
}

fn window_for(a: &[u64], factor: u64) -> u64 {
    let maxa = *a.iter().max().unwrap();
    (maxa.saturating_mul(factor)).min(200_000_000)
}

fn ratio_f(r: (u128, u128)) -> f64 {
    r.0 as f64 / r.1 as f64
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn lcm_checked(a: u64, b: u64, cap: u64) -> Option<u64> {
    let g = gcd_u64(a, b);
    let value = (a / g) as u128 * b as u128;
    if value > cap as u128 || value > u64::MAX as u128 {
        None
    } else {
        Some(value as u64)
    }
}

fn lcm_set(a: &[u64], cap: u64) -> Option<u64> {
    let mut out = 1u64;
    for &d in a {
        out = lcm_checked(out, d, cap)?;
    }
    Some(out)
}

fn common_gcd(a: &[u64]) -> u64 {
    a.iter().copied().reduce(gcd_u64).unwrap_or(0)
}

fn reciprocal_sum(a: &[u64]) -> ExactRatio {
    a.iter().fold(ExactRatio::zero(), |acc, &d| {
        acc.add(ExactRatio::new(1, d as u128))
    })
}

fn reciprocal_sparse(a: &[u64]) -> bool {
    let Some(&amin) = a.iter().min() else {
        return false;
    };
    reciprocal_sum(a).le(ExactRatio::new(2, amin as u128))
}

fn charge_sum_at(a: &[u64], e: u64) -> ExactRatio {
    a.iter().filter(|&&f| f != e).fold(ExactRatio::zero(), |acc, &f| {
        acc.add(ExactRatio::new(gcd_u64(e, f) as u128, f as u128))
    })
}

fn charge_positive(a: &[u64]) -> bool {
    a.iter()
        .all(|&e| charge_sum_at(a, e).lt(ExactRatio::new(1, 1)))
}

fn separator_holds(bx: u64, x: u64, s: ExactRatio) -> bool {
    2 * bx as u128 * s.den > x as u128 * s.num
}

fn update_min_witness(slot: &mut Option<CertWitness>, candidate: CertWitness) {
    let replace = match slot {
        Some(current) => candidate.value.lt(current.value),
        None => true,
    };
    if replace {
        *slot = Some(candidate);
    }
}

fn update_max_witness(slot: &mut Option<CertWitness>, candidate: CertWitness) {
    let replace = match slot {
        Some(current) => candidate.value.gt(current.value),
        None => true,
    };
    if replace {
        *slot = Some(candidate);
    }
}

fn periodic_certificate(a: &[u64], lcm_cap: u64) -> Result<PeriodicCertificate, String> {
    if a.is_empty() {
        return Err("empty set".to_string());
    }
    if a.iter().any(|&d| d == 0) {
        return Err("set entries must be positive".to_string());
    }
    let lcm = lcm_set(a, lcm_cap)
        .ok_or_else(|| format!("lcm exceeds cap {lcm_cap}; rerun with a larger cap"))?;
    periodic_certificate_with_lcm(a, lcm)
}

fn periodic_certificate_with_lcm(a: &[u64], lcm: u64) -> Result<PeriodicCertificate, String> {
    let maxa = *a.iter().max().ok_or_else(|| "empty set".to_string())?;
    if maxa > lcm {
        return Err("max element exceeds lcm; unsupported degenerate set".to_string());
    }
    if lcm > usize::MAX as u64 - 1 {
        return Err("lcm too large for this platform".to_string());
    }

    let s = reciprocal_sum(a);
    let mut inb = vec![false; lcm as usize + 1];
    for &d in a {
        let mut x = d;
        while x <= lcm {
            inb[x as usize] = true;
            x += d;
        }
    }

    let mut small_prefix = vec![0u64; maxa as usize];
    let mut count = 0u64;
    let mut alpha: Option<CertWitness> = None;
    let mut beta: Option<CertWitness> = None;
    let mut union_bound_separator = true;

    for x in 1..=lcm {
        if inb[x as usize] {
            count += 1;
        }
        if x < maxa {
            small_prefix[x as usize] = count;
        }
        if x >= maxa {
            let value = ExactRatio::new(count as u128, x as u128);
            update_min_witness(&mut alpha, CertWitness::new(Some(x), value));
            update_max_witness(&mut beta, CertWitness::new(Some(x), value));
            if !separator_holds(count, x, s) {
                union_bound_separator = false;
            }
        }
    }

    let density = ExactRatio::new(count as u128, lcm as u128);
    update_min_witness(&mut alpha, CertWitness::new(None, density));
    update_max_witness(&mut beta, CertWitness::new(None, density));
    if !separator_holds(count, lcm, s) {
        union_bound_separator = false;
    }

    for r in 1..maxa {
        let x = lcm + r;
        let bx = count + small_prefix[r as usize];
        let value = ExactRatio::new(bx as u128, x as u128);
        update_min_witness(&mut alpha, CertWitness::new(Some(x), value));
        update_max_witness(&mut beta, CertWitness::new(Some(x), value));
        if !separator_holds(bx, x, s) {
            union_bound_separator = false;
        }
    }

    let alpha = alpha.ok_or_else(|| "no alpha candidate found".to_string())?;
    let beta = beta.ok_or_else(|| "no beta candidate found".to_string())?;
    let ordering_free = beta.value.num * alpha.value.den
        < 2 * alpha.value.num * beta.value.den;
    let beta_over_alpha = ExactRatio::new(
        beta.value.num * alpha.value.den,
        beta.value.den * alpha.value.num,
    );

    Ok(PeriodicCertificate {
        lcm,
        density_count: count,
        alpha,
        beta,
        beta_over_alpha,
        ordering_free,
        union_bound_separator,
    })
}

fn parse_set_arg(raw: &str) -> Result<Vec<u64>, String> {
    let mut out = Vec::new();
    for piece in raw.split(',') {
        let trimmed = piece.trim();
        if trimmed.is_empty() {
            continue;
        }
        out.push(parse_u64_arg(trimmed)?);
    }
    if out.is_empty() {
        return Err("set must be nonempty".to_string());
    }
    if out.iter().any(|&d| d == 0) {
        return Err("set entries must be positive".to_string());
    }
    out.sort_unstable();
    out.dedup();
    Ok(out)
}

fn parse_u64_arg(raw: &str) -> Result<u64, String> {
    raw.replace('_', "")
        .parse::<u64>()
        .map_err(|_| format!("invalid integer `{raw}`"))
}

fn format_set(a: &[u64]) -> String {
    let body = a
        .iter()
        .map(|d| d.to_string())
        .collect::<Vec<_>>()
        .join(",");
    format!("{{{body}}}")
}

/// "uncovered" (reciprocal-heavy) test: sum_{d in tail} 1/d > 1/min(a).
/// Exact via common denominator; on overflow treat as hard (don't skip).
fn is_uncovered(a: &[u64]) -> bool {
    let amin = a[0] as u128;
    let tail = &a[1..];
    let mut prod: u128 = 1;
    for &d in tail {
        prod = match prod.checked_mul(d as u128) {
            Some(p) => p,
            None => return true,
        };
    }
    let mut num = 0u128;
    for &d in tail {
        num = num.saturating_add(prod / (d as u128));
    }
    match amin.checked_mul(num) {
        Some(x) => x > prod,
        None => true,
    }
}

#[allow(clippy::too_many_arguments)]
fn rec(
    depth: usize,
    start_val: u64,
    amax: u64,
    idx: &mut Vec<u64>,
    k: usize,
    factor: u64,
    uncovered_only: bool,
    tested: &mut u64,
    skipped: &mut u64,
    worst: &mut (u128, u128),
    worst_set: &mut Vec<u64>,
    ces: &mut Vec<(Vec<u64>, u64, u64)>,
) {
    if depth == k {
        if !is_primitive(idx) {
            return;
        }
        if uncovered_only && !is_uncovered(idx) {
            *skipped += 1;
            return;
        }
        let w = window_for(idx, factor);
        let (ce, r) = ep488_window(idx, w);
        *tested += 1;
        if let Some((n, m)) = ce {
            ces.push((idx.clone(), n, m));
        }
        if r.0 * worst.1 > worst.0 * r.1 {
            *worst = r;
            *worst_set = idx.clone();
        }
        return;
    }
    let mut v = start_val;
    while v <= amax {
        idx[depth] = v;
        rec(
            depth + 1, v + 1, amax, idx, k, factor, uncovered_only, tested, skipped, worst,
            worst_set, ces,
        );
        v += 1;
    }
}

fn search(k: usize, amax: u64, factor: u64, uncovered_only: bool) {
    let start = Instant::now();
    let mut tested = 0u64;
    let mut skipped = 0u64;
    let mut worst = (0u128, 1u128);
    let mut worst_set: Vec<u64> = vec![];
    let mut ces: Vec<(Vec<u64>, u64, u64)> = vec![];
    let mut idx = vec![0u64; k];
    rec(
        0, 2, amax, &mut idx, k, factor, uncovered_only, &mut tested, &mut skipped, &mut worst,
        &mut worst_set, &mut ces,
    );
    let dt = start.elapsed().as_secs_f64();
    println!("k={k} amax={amax} window_factor={factor} uncovered_only={uncovered_only}");
    println!("  primitive sets tested = {tested}   skipped(covered) = {skipped}   time = {dt:.2}s");
    println!(
        "  worst ratio = {}/{} = {:.9}   at set = {:?}",
        worst.0,
        worst.1,
        ratio_f(worst),
        worst_set
    );
    if ces.is_empty() {
        println!("  COUNTEREXAMPLES (n*B(m) >= 2*m*B(n), m>n>=maxA) : NONE in window");
    } else {
        println!("  *** COUNTEREXAMPLES FOUND: {} ***", ces.len());
        for (s, n, m) in ces.iter().take(20) {
            println!("      set={s:?}  n={n} m={m}");
        }
    }
}

fn command_classify(raw: Option<&String>) -> Result<(), String> {
    let raw = raw.ok_or_else(|| "usage: fastcheck classify <a,b,c,...>".to_string())?;
    let a = parse_set_arg(raw)?;
    println!("set = {}", format_set(&a));
    println!("primitive = {}", is_primitive(&a));
    println!("common gcd = {}", common_gcd(&a));
    println!("S = {}", reciprocal_sum(&a));
    println!("reciprocal-sparse theorem applies = {}", reciprocal_sparse(&a));
    println!("charge-positivity theorem applies = {}", charge_positive(&a));
    for &e in &a {
        println!("  charge sum at {e} = {}", charge_sum_at(&a, e));
    }
    Ok(())
}

fn command_cert(raw: Option<&String>, cap_raw: Option<&String>) -> Result<(), String> {
    let raw = raw.ok_or_else(|| "usage: fastcheck cert <a,b,c,...> [lcm_cap]".to_string())?;
    let cap = match cap_raw {
        Some(x) => parse_u64_arg(x)?,
        None => 50_000_000,
    };
    let a = parse_set_arg(raw)?;
    let cert = periodic_certificate(&a, cap)?;
    println!("set = {}", format_set(&a));
    println!("primitive = {}", is_primitive(&a));
    println!("lcm = {}", cert.lcm);
    println!(
        "density = {}/{} ({:.12})",
        cert.density_count,
        cert.lcm,
        cert.density_count as f64 / cert.lcm as f64
    );
    println!("alpha = {}", cert.alpha);
    println!("beta  = {}", cert.beta);
    println!("beta/alpha = {}", cert.beta_over_alpha);
    println!("ordering-free beta < 2*alpha = {}", cert.ordering_free);
    println!(
        "union-bound separator S < 2B(n)/n for all n>=max(A) = {}",
        cert.union_bound_separator
    );
    Ok(())
}

fn command_sweep_quad_cert(amax_raw: Option<&String>, cap_raw: Option<&String>) -> Result<(), String> {
    let amax = match amax_raw {
        Some(x) => parse_u64_arg(x)?,
        None => 30,
    };
    let cap = match cap_raw {
        Some(x) => parse_u64_arg(x)?,
        None => 3_000_000,
    };
    if amax < 5 {
        return Err("amax must be at least 5 for quadruples".to_string());
    }

    let start = Instant::now();
    let mut primitive = 0u64;
    let mut sparse = 0u64;
    let mut charge = 0u64;
    let mut symbolic = 0u64;
    let mut residual = 0u64;
    let mut attempted = 0u64;
    let mut cert_pass = 0u64;
    let mut cert_fail = 0u64;
    let mut separator_pass = 0u64;
    let mut skipped_lcm = 0u64;
    let mut worst_pass: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)> = None;
    let mut worst_fail: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)> = None;
    let mut skipped_examples: Vec<(Vec<u64>, u64)> = Vec::new();

    for a in 2..=amax - 3 {
        for b in a + 1..=amax - 2 {
            for c in b + 1..=amax - 1 {
                for d in c + 1..=amax {
                    let set = vec![a, b, c, d];
                    if !is_primitive(&set) {
                        continue;
                    }
                    primitive += 1;
                    let is_sparse = reciprocal_sparse(&set);
                    let is_charge = charge_positive(&set);
                    if is_sparse {
                        sparse += 1;
                    }
                    if is_charge {
                        charge += 1;
                    }
                    if is_sparse || is_charge {
                        symbolic += 1;
                        continue;
                    }

                    residual += 1;
                    let Some(lcm) = lcm_set(&set, cap) else {
                        skipped_lcm += 1;
                        if skipped_examples.len() < 8 {
                            if let Some(full_lcm) = lcm_set(&set, u64::MAX) {
                                skipped_examples.push((set, full_lcm));
                            }
                        }
                        continue;
                    };

                    attempted += 1;
                    let cert = periodic_certificate_with_lcm(&set, lcm)?;
                    if cert.union_bound_separator {
                        separator_pass += 1;
                    }
                    if cert.ordering_free {
                        cert_pass += 1;
                        update_cert_worst(&mut worst_pass, cert.beta_over_alpha, set, cert);
                    } else {
                        cert_fail += 1;
                        update_cert_worst(&mut worst_fail, cert.beta_over_alpha, set, cert);
                    }
                }
            }
        }
    }

    println!("primitive quadruples with entries <= {amax}: {primitive}");
    println!("reciprocal-sparse theorem applies: {sparse}");
    println!("charge-positivity theorem applies: {charge}");
    println!("symbolically done by sparse or charge: {symbolic}");
    println!("residual after those regimes: {residual}");
    println!("exact residual certificates attempted with lcm <= {cap}: {attempted}");
    println!("  ordering-free PASS: {cert_pass}");
    println!("  ordering-free FAIL: {cert_fail}");
    println!("  skipped by lcm cap: {skipped_lcm}");
    println!("  union-bound separator passes among attempted: {separator_pass}");
    println!("time = {:.2}s", start.elapsed().as_secs_f64());

    if let Some((ratio, set, cert)) = worst_pass {
        println!();
        println!("worst passing residual certificate:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {ratio}");
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
    }
    if let Some((ratio, set, cert)) = worst_fail {
        println!();
        println!("largest failed residual certificate:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {ratio}");
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
    }
    if !skipped_examples.is_empty() {
        println!();
        println!("first residual sets skipped by lcm cap:");
        for (set, lcm) in skipped_examples {
            println!("  {} lcm={}", format_set(&set), lcm);
        }
    }

    Ok(())
}

fn update_cert_worst(
    slot: &mut Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    ratio: ExactRatio,
    set: Vec<u64>,
    cert: PeriodicCertificate,
) {
    let replace = match slot {
        Some((old, _, _)) => ratio.gt(*old),
        None => true,
    };
    if replace {
        *slot = Some((ratio, set, cert));
    }
}

fn selftest() {
    println!("=== SELF-TEST (must all pass) ===");
    let mut ok = true;

    // 1) singleton A={a}: extremal ratio 2 - 1/a, no counterexample.
    for a in [2u64, 5, 50, 1000] {
        let (ce, r) = ep488_window(&[a], 4 * a);
        let expect = 2.0 - 1.0 / a as f64;
        let got = ratio_f(r);
        let pass = ce.is_none() && (got - expect).abs() < 1e-9;
        println!(
            "  single {{{a}}}: worst={got:.6} expect(2-1/a)={expect:.6} ce={ce:?}  {}",
            if pass { "ok" } else { "FAIL" }
        );
        ok &= pass;
    }

    // 2) no counterexample for any primitive triple in range (matches Python).
    {
        let start = Instant::now();
        let mut tested = 0u64;
        let mut worst = (0u128, 1u128);
        let mut ce_found = false;
        for a in 2..=20u64 {
            for b in (a + 1)..=60u64 {
                if b % a == 0 {
                    continue;
                }
                for c in (b + 1)..=120u64 {
                    if c % a == 0 || c % b == 0 {
                        continue;
                    }
                    let s = [a, b, c];
                    let (cev, r) = ep488_window(&s, 40 * c);
                    tested += 1;
                    if cev.is_some() {
                        ce_found = true;
                        println!("    triple CE {s:?} {cev:?}");
                    }
                    if r.0 * worst.1 > worst.0 * r.1 {
                        worst = r;
                    }
                }
            }
        }
        let pass = !ce_found;
        println!(
            "  triples (a<=20,b<=60,c<=120): tested={tested} worst={:.6} ce_found={ce_found} {} [{:.2}s]",
            ratio_f(worst),
            if pass { "ok" } else { "FAIL" },
            start.elapsed().as_secs_f64()
        );
        ok &= pass;
    }

    // 3) {2p : p<=13} = {4,6,10,14,22,26}: EP488 holds (all multiples even => sup<=1/2).
    {
        let s: Vec<u64> = vec![4, 6, 10, 14, 22, 26];
        let (ce, r) = ep488_window(&s, 60 * 26);
        let pass = ce.is_none() && ratio_f(r) < 2.0;
        println!(
            "  {{4,6,10,14,22,26}}: worst={:.6} ce={ce:?} {}",
            ratio_f(r),
            if pass { "ok" } else { "FAIL" }
        );
        ok &= pass;
    }

    println!("=== SELF-TEST: {} ===", if ok { "PASS" } else { "FAIL" });
    if !ok {
        std::process::exit(1);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("selftest");
    match mode {
        "selftest" => selftest(),
        "triples" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30);
            let f: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(40);
            search(3, amax, f, false);
        }
        "quads" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30);
            let f: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(40);
            let unc = args.iter().any(|s| s == "--uncovered");
            search(4, amax, f, unc);
        }
        "quints" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(24);
            let f: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(30);
            let unc = args.iter().any(|s| s == "--uncovered");
            search(5, amax, f, unc);
        }
        "set" => {
            let mut s: Vec<u64> = args
                .get(2)
                .map(|x| x.split(',').filter_map(|t| t.parse().ok()).collect())
                .unwrap_or_default();
            s.sort();
            let f: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(60);
            let w = window_for(&s, f);
            let (ce, r) = ep488_window(&s, w);
            println!(
                "set={s:?} primitive={} window=[{},{}] worst={:.9} ce={ce:?}",
                is_primitive(&s),
                s.iter().max().unwrap(),
                w,
                ratio_f(r)
            );
        }
        "classify" => {
            if let Err(err) = command_classify(args.get(2)) {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
        "cert" => {
            if let Err(err) = command_cert(args.get(2), args.get(3)) {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
        "sweep-quad-cert" => {
            if let Err(err) = command_sweep_quad_cert(args.get(2), args.get(3)) {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
        "bench" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40);
            let t = Instant::now();
            search(4, amax, 40, false);
            eprintln!("bench total {:.2}s", t.elapsed().as_secs_f64());
        }
        other => {
            eprintln!(
                "unknown mode '{other}'. modes: selftest triples quads quints set classify cert sweep-quad-cert bench"
            );
            std::process::exit(2);
        }
    }
}
