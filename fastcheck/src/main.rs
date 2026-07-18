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
//!   fastcheck density <a,b,c,...>
//!   fastcheck tower <a,b,c,d,e>
//!   fastcheck cert <a,b,c,...> [lcm_cap]
//!   fastcheck sweep-quad-cert <amax> [lcm_cap]
//!   fastcheck sweep-quint-cert <amax> [lcm_cap] [top_classes]
//!   fastcheck quint-separator <amax> [window_factor] [--uncovered] [--middle] [--cover] [--top K]
//!   fastcheck quint-density <amax> [--gcd1] [--uncovered] [--hard] [--residual] [--top K]
//!   fastcheck bench <amax>

use std::cmp::Ordering;
use std::collections::BTreeMap;
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
        self.cmp(&other) == Ordering::Less
    }

    fn le(self, other: Self) -> bool {
        self.cmp(&other) != Ordering::Greater
    }

    fn gt(self, other: Self) -> bool {
        self.cmp(&other) == Ordering::Greater
    }

    fn as_f64(self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

impl Ord for ExactRatio {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_ratio_u128(self.num, self.den, other.num, other.den)
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

/// Bounded-window check for the raw union-bound separator
/// `2*B(n) > n*sum(1/a)` on max(A) <= n <= w.
/// Returns the first failing n, and the largest value of
/// n*S/(2B(n)); values >= 1 are failures.
fn separator_window(a: &[u64], w: u64, middle_only: bool) -> (Option<u64>, (u128, u128), u64) {
    let maxa = *a.iter().max().unwrap();
    let start_n = if middle_only {
        maxa.max(2 * a[0])
    } else {
        maxa
    };
    if start_n > w {
        return (None, (0, 1), start_n);
    }
    let pref = b_prefix(a, w);
    let s = reciprocal_sum(a);
    let mut fail = None;
    let mut worst = (0u128, 1u128);
    let mut worst_n = start_n;
    for n in start_n..=w {
        let bn = pref[n as usize] as u128;
        if bn == 0 {
            continue;
        }
        if !separator_holds(bn as u64, n, s) && fail.is_none() {
            fail = Some(n);
        }
        let candidate = ((n as u128) * s.num, 2 * bn * s.den);
        if ratio_gt(candidate, worst) {
            worst = candidate;
            worst_n = n;
        }
    }
    (fail, worst, worst_n)
}

fn window_for(a: &[u64], factor: u64) -> u64 {
    let maxa = *a.iter().max().unwrap();
    (maxa.saturating_mul(factor)).min(200_000_000)
}

fn ratio_f(r: (u128, u128)) -> f64 {
    r.0 as f64 / r.1 as f64
}

fn cmp_ratio_u128(mut a: u128, mut b: u128, mut c: u128, mut d: u128) -> Ordering {
    assert!(b > 0 && d > 0);
    let mut flipped = false;
    loop {
        let qa = a / b;
        let qc = c / d;
        if qa != qc {
            let ord = qa.cmp(&qc);
            return if flipped { ord.reverse() } else { ord };
        }

        let ra = a % b;
        let rc = c % d;
        let ord = match (ra == 0, rc == 0) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => {
                a = b;
                b = ra;
                c = d;
                d = rc;
                flipped = !flipped;
                continue;
            }
        };
        return if flipped { ord.reverse() } else { ord };
    }
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

fn lcm_checked_u128(a: u128, b: u128) -> Option<u128> {
    let g = gcd_u128(a, b);
    (a / g).checked_mul(b)
}

fn lcm_set_u128(a: &[u64]) -> Option<u128> {
    let mut out = 1u128;
    for &d in a {
        out = lcm_checked_u128(out, d as u128)?;
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

fn quint_cover_candidate(a: &[u64]) -> bool {
    if common_gcd(a) != 1 || good_charge_count(a) > 2 {
        return false;
    }
    let Some(&maxa) = a.iter().max() else {
        return false;
    };
    let s = reciprocal_sum(a);
    let Some(lhs_num) = (maxa as u128).checked_mul(s.num) else {
        return false;
    };
    cmp_ratio_u128(lhs_num, s.den, 1135, 7) != Ordering::Greater
}

fn cover_partial_max(idx: &[u64], depth: usize, amax: u64) -> u64 {
    if depth == 0 {
        return amax;
    }
    let mut s = ExactRatio::zero();
    for &d in &idx[..depth] {
        s = s.add(ExactRatio::new(1, d as u128));
    }
    let remaining = 5usize.saturating_sub(depth) as u128;
    let Some(bound_num) = 1135u128.checked_sub(7 * remaining) else {
        return 0;
    };
    let numerator = bound_num * s.den;
    let denominator = 7 * s.num;
    let upper = numerator / denominator;
    upper.min(amax as u128) as u64
}

fn partial_forced_good_count(idx: &[u64], depth: usize, start_val: u64) -> usize {
    let remaining = 5usize.saturating_sub(depth);
    let mut forced_good = 0usize;
    for i in 0..depth {
        let e = idx[i];
        let mut upper_charge = ExactRatio::zero();
        for j in 0..depth {
            if i != j {
                let f = idx[j];
                upper_charge = upper_charge.add(ExactRatio::new(gcd_u64(e, f) as u128, f as u128));
            }
        }
        for offset in 0..remaining {
            upper_charge = upper_charge.add(ExactRatio::new(
                e as u128,
                (start_val + offset as u64) as u128,
            ));
        }
        if upper_charge.lt(ExactRatio::new(1, 1)) {
            forced_good += 1;
        }
    }
    forced_good
}

fn contains_two(a: &[u64]) -> bool {
    a.iter().any(|&d| d == 2)
}

fn is_scaled_family(a: &[u64], base: &[u64], min_scale: u64) -> bool {
    if a.len() != base.len() {
        return false;
    }
    let scale = common_gcd(a);
    scale >= min_scale
        && a.iter()
            .zip(base.iter())
            .all(|(&value, &base_value)| scale.checked_mul(base_value) == Some(value))
}

fn is_scaled_q_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 10, 14, 15], 1)
}

fn is_scaled_r_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 5, 7, 11], 2)
}

fn is_scaled_t_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[32, 45, 48, 72, 80], 1)
}

fn is_scaled_u_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[16, 24, 36, 40, 45], 1)
}

fn is_scaled_v_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 5, 6, 9, 14], 1)
}

fn is_scaled_w_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 10, 14], 1)
}

fn is_scaled_x_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[12, 20, 30, 45, 50], 1)
}

fn is_scaled_y_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 5, 7, 13], 2)
}

fn is_scaled_z_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 5, 11, 13], 2)
}

fn is_scaled_aa_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 7, 11, 13], 2)
}

fn is_scaled_ab_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 7, 9, 15], 1)
}

fn is_scaled_ac_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 7, 10, 15], 1)
}

fn is_scaled_ad_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 10, 15], 1)
}

fn is_scaled_ae_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 11, 15], 1)
}

fn is_scaled_af_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 13, 15], 1)
}

fn is_scaled_ag_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 14, 15], 1)
}

fn is_scaled_ah_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 15, 17], 1)
}

fn is_scaled_ai_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 15, 19], 1)
}

fn is_scaled_aj_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 7, 10, 15, 18], 1)
}

fn is_scaled_ak_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[8, 10, 12, 15, 18], 1)
}

fn is_scaled_al_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[8, 12, 15, 18, 20], 1)
}

fn is_scaled_am_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 5, 7, 17], 2)
}

fn is_scaled_an_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[2, 3, 5, 7, 19], 2)
}

fn is_scaled_ao_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[3, 4, 10, 14, 22], 1)
}

fn is_scaled_ap_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[3, 4, 10, 14, 25], 1)
}

fn is_scaled_aq_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[3, 4, 10, 22, 25], 1)
}

fn is_scaled_ar_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 5, 6, 9, 21], 1)
}

fn is_scaled_as_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 10, 22], 1)
}

fn is_scaled_at_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 10, 25], 1)
}

fn is_scaled_au_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 14, 21], 1)
}

fn is_scaled_av_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 14, 22], 1)
}

fn is_scaled_aw_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 15, 21], 1)
}

fn is_scaled_ax_family(a: &[u64]) -> bool {
    is_scaled_family(a, &[4, 6, 9, 15, 22], 1)
}

fn scaled_quint_audit_applies(a: &[u64]) -> bool {
    is_scaled_q_family(a)
        || is_scaled_r_family(a)
        || is_scaled_t_family(a)
        || is_scaled_u_family(a)
        || is_scaled_v_family(a)
        || is_scaled_w_family(a)
        || is_scaled_x_family(a)
        || is_scaled_y_family(a)
        || is_scaled_z_family(a)
        || is_scaled_aa_family(a)
        || is_scaled_ab_family(a)
        || is_scaled_ac_family(a)
        || is_scaled_ad_family(a)
        || is_scaled_ae_family(a)
        || is_scaled_af_family(a)
        || is_scaled_ag_family(a)
        || is_scaled_ah_family(a)
        || is_scaled_ai_family(a)
        || is_scaled_aj_family(a)
        || is_scaled_ak_family(a)
        || is_scaled_al_family(a)
        || is_scaled_am_family(a)
        || is_scaled_an_family(a)
        || is_scaled_ao_family(a)
        || is_scaled_ap_family(a)
        || is_scaled_aq_family(a)
        || is_scaled_ar_family(a)
        || is_scaled_as_family(a)
        || is_scaled_at_family(a)
        || is_scaled_au_family(a)
        || is_scaled_av_family(a)
        || is_scaled_aw_family(a)
        || is_scaled_ax_family(a)
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

fn at_least_two_good_charges(a: &[u64]) -> bool {
    good_charge_count(a) >= 2
}

fn at_least_three_good_charges(a: &[u64]) -> bool {
    good_charge_count(a) >= 3
}

fn good_charge_count(a: &[u64]) -> usize {
    let good = a
        .iter()
        .filter(|&&e| charge_sum_at(a, e).lt(ExactRatio::new(1, 1)))
        .count();
    good
}

fn separator_holds(bx: u64, x: u64, s: ExactRatio) -> bool {
    2 * bx as u128 * s.den > x as u128 * s.num
}

fn tower_cap(s: ExactRatio) -> Option<u64> {
    let numerator = 1135u128.checked_mul(s.den)?;
    let denominator = 7u128.checked_mul(s.num)?;
    if denominator == 0 {
        return None;
    }
    let y_max = (numerator.checked_sub(1)?) / denominator;
    y_max.checked_sub(1).and_then(|x| u64::try_from(x).ok())
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

/// Strict `>` on ratios given as `(num, den)`, `den > 0`.
fn ratio_gt(a: (u128, u128), b: (u128, u128)) -> bool {
    a.0 * b.1 > b.0 * a.1
}
/// Equality on ratios given as `(num, den)`, `den > 0`.
fn ratio_eq(a: (u128, u128), b: (u128, u128)) -> bool {
    a.0 * b.1 == b.0 * a.1
}

/// A per-thread partial result of a windowed `search`, mergeable so the search
/// can be split across cores and reduced exactly (bit-identical to serial).
#[derive(Clone)]
struct SearchPartial {
    tested: u64,
    skipped: u64,
    worst: (u128, u128),
    worst_set: Vec<u64>,
    ces: Vec<(Vec<u64>, u64, u64)>,
}

impl SearchPartial {
    fn empty() -> Self {
        SearchPartial { tested: 0, skipped: 0, worst: (0, 1), worst_set: Vec::new(), ces: Vec::new() }
    }
    /// Merge, keeping the larger worst-ratio; ties are broken by the
    /// lexicographically smaller witness set so the result is deterministic
    /// regardless of thread scheduling.
    fn merge(mut self, mut other: SearchPartial) -> SearchPartial {
        self.tested += other.tested;
        self.skipped += other.skipped;
        let take = ratio_gt(other.worst, self.worst)
            || (ratio_eq(other.worst, self.worst)
                && !other.worst_set.is_empty()
                && (self.worst_set.is_empty() || other.worst_set < self.worst_set));
        if take {
            self.worst = other.worst;
            self.worst_set = other.worst_set;
        }
        self.ces.append(&mut other.ces);
        self
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
    p: &mut SearchPartial,
) {
    if depth == k {
        if !is_primitive(idx) {
            return;
        }
        if uncovered_only && !is_uncovered(idx) {
            p.skipped += 1;
            return;
        }
        let w = window_for(idx, factor);
        let (ce, r) = ep488_window(idx, w);
        p.tested += 1;
        if let Some((n, m)) = ce {
            p.ces.push((idx.clone(), n, m));
        }
        let take = ratio_gt(r, p.worst)
            || (ratio_eq(r, p.worst)
                && (p.worst_set.is_empty() || idx.as_slice() < p.worst_set.as_slice()));
        if take {
            p.worst = r;
            p.worst_set = idx.clone();
        }
        return;
    }
    let mut v = start_val;
    while v <= amax {
        idx[depth] = v;
        rec(depth + 1, v + 1, amax, idx, k, factor, uncovered_only, p);
        v += 1;
    }
}

/// Number of worker threads. Defaults to all available cores; override with the
/// `FASTCHECK_THREADS` environment variable (e.g. `FASTCHECK_THREADS=1` to force
/// the serial path, useful for benchmarking or a loaded machine).
fn worker_count() -> usize {
    if let Ok(v) = std::env::var("FASTCHECK_THREADS") {
        if let Ok(n) = v.parse::<usize>() {
            if n >= 1 {
                return n;
            }
        }
    }
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).max(1)
}

fn search(k: usize, amax: u64, factor: u64, uncovered_only: bool) {
    let start = Instant::now();
    let nthreads = worker_count();
    // Split the first element a0 in [2, amax] across threads round-robin; each
    // thread owns disjoint a0 values, so the subtrees never overlap. Round-robin
    // (rather than contiguous blocks) balances load, since small a0 have larger
    // subtrees. The merge is exact, so the result matches the serial version.
    let partials: Vec<SearchPartial> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|t| {
                s.spawn(move || {
                    let mut p = SearchPartial::empty();
                    let mut idx = vec![0u64; k];
                    let mut a0 = 2 + t as u64;
                    while a0 <= amax {
                        idx[0] = a0;
                        rec(1, a0 + 1, amax, &mut idx, k, factor, uncovered_only, &mut p);
                        a0 += nthreads as u64;
                    }
                    p
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let result = partials.into_iter().fold(SearchPartial::empty(), SearchPartial::merge);
    let dt = start.elapsed().as_secs_f64();
    println!("k={k} amax={amax} window_factor={factor} uncovered_only={uncovered_only} threads={nthreads}");
    println!(
        "  primitive sets tested = {}   skipped(covered) = {}   time = {dt:.2}s",
        result.tested, result.skipped
    );
    println!(
        "  worst ratio = {}/{} = {:.9}   at set = {:?}",
        result.worst.0,
        result.worst.1,
        ratio_f(result.worst),
        result.worst_set
    );
    if result.ces.is_empty() {
        println!("  COUNTEREXAMPLES (n*B(m) >= 2*m*B(n), m>n>=maxA) : NONE in window");
    } else {
        println!("  *** COUNTEREXAMPLES FOUND: {} ***", result.ces.len());
        for (s, n, m) in result.ces.iter().take(20) {
            println!("      set={s:?}  n={n} m={m}");
        }
    }
}

#[derive(Clone)]
struct SeparatorRecord {
    ratio: (u128, u128),
    set: Vec<u64>,
    n: u64,
}

fn update_separator_top(
    top: &mut Vec<SeparatorRecord>,
    limit: usize,
    ratio: (u128, u128),
    set: Vec<u64>,
    n: u64,
) {
    if limit == 0 {
        return;
    }
    top.push(SeparatorRecord { ratio, set, n });
    top.sort_by(|a, b| {
        if ratio_gt(a.ratio, b.ratio) {
            Ordering::Less
        } else if ratio_gt(b.ratio, a.ratio) {
            Ordering::Greater
        } else {
            a.set.cmp(&b.set).then_with(|| a.n.cmp(&b.n))
        }
    });
    top.truncate(limit);
}

#[derive(Clone)]
struct SeparatorPartial {
    tested: u64,
    skipped: u64,
    pruned: u64,
    min_gt_54: u64,
    fourth_gt_120: u64,
    max_min_value: u64,
    min_gt_examples: Vec<Vec<u64>>,
    fourth_gt_examples: Vec<Vec<u64>>,
    worst: (u128, u128),
    worst_set: Vec<u64>,
    worst_n: u64,
    fails: Vec<(Vec<u64>, u64)>,
    top_limit: usize,
    top: Vec<SeparatorRecord>,
}

impl SeparatorPartial {
    fn empty(top_limit: usize) -> Self {
        Self {
            tested: 0,
            skipped: 0,
            pruned: 0,
            min_gt_54: 0,
            fourth_gt_120: 0,
            max_min_value: 0,
            min_gt_examples: Vec::new(),
            fourth_gt_examples: Vec::new(),
            worst: (0, 1),
            worst_set: Vec::new(),
            worst_n: 0,
            fails: Vec::new(),
            top_limit,
            top: Vec::new(),
        }
    }

    fn merge(mut self, mut other: SeparatorPartial) -> SeparatorPartial {
        self.tested += other.tested;
        self.skipped += other.skipped;
        self.pruned += other.pruned;
        self.min_gt_54 += other.min_gt_54;
        self.fourth_gt_120 += other.fourth_gt_120;
        self.max_min_value = self.max_min_value.max(other.max_min_value);
        for example in other.min_gt_examples {
            if self.min_gt_examples.len() < 8 {
                self.min_gt_examples.push(example);
            }
        }
        for example in other.fourth_gt_examples {
            if self.fourth_gt_examples.len() < 8 {
                self.fourth_gt_examples.push(example);
            }
        }
        let take = ratio_gt(other.worst, self.worst)
            || (ratio_eq(other.worst, self.worst)
                && !other.worst_set.is_empty()
                && (self.worst_set.is_empty() || other.worst_set < self.worst_set));
        if take {
            self.worst = other.worst;
            self.worst_set = other.worst_set;
            self.worst_n = other.worst_n;
        }
        self.fails.append(&mut other.fails);
        for record in other.top {
            update_separator_top(
                &mut self.top,
                self.top_limit,
                record.ratio,
                record.set,
                record.n,
            );
        }
        self
    }
}

fn rec_separator(
    depth: usize,
    start_val: u64,
    amax: u64,
    idx: &mut Vec<u64>,
    factor: u64,
    uncovered_only: bool,
    middle_only: bool,
    cover_only: bool,
    p: &mut SeparatorPartial,
) {
    if cover_only && partial_forced_good_count(idx, depth, start_val) > 2 {
        p.pruned += 1;
        return;
    }
    if depth == 5 {
        if !is_primitive(idx) {
            return;
        }
        if uncovered_only && !is_uncovered(idx) {
            p.skipped += 1;
            return;
        }
        if cover_only && !quint_cover_candidate(idx) {
            p.skipped += 1;
            return;
        }
        if cover_only {
            p.max_min_value = p.max_min_value.max(idx[0]);
            if idx[0] > 54 {
                p.min_gt_54 += 1;
                if p.min_gt_examples.len() < 8 {
                    p.min_gt_examples.push(idx.clone());
                }
            }
            if idx[3] > 120 {
                p.fourth_gt_120 += 1;
                if p.fourth_gt_examples.len() < 8 {
                    p.fourth_gt_examples.push(idx.clone());
                }
            }
        }
        let w = window_for(idx, factor);
        let (fail, r, n) = separator_window(idx, w, middle_only);
        p.tested += 1;
        if let Some(n_fail) = fail {
            p.fails.push((idx.clone(), n_fail));
        }
        update_separator_top(&mut p.top, p.top_limit, r, idx.clone(), n);
        let take = ratio_gt(r, p.worst)
            || (ratio_eq(r, p.worst)
                && (p.worst_set.is_empty() || idx.as_slice() < p.worst_set.as_slice()));
        if take {
            p.worst = r;
            p.worst_set = idx.clone();
            p.worst_n = n;
        }
        return;
    }
    let loop_max = if cover_only {
        cover_partial_max(idx, depth, amax)
    } else {
        amax
    };
    let remaining_after = 5usize.saturating_sub(depth + 1) as u64;
    let mut v = start_val;
    while v.saturating_add(remaining_after) <= loop_max {
        idx[depth] = v;
        rec_separator(
            depth + 1,
            v + 1,
            amax,
            idx,
            factor,
            uncovered_only,
            middle_only,
            cover_only,
            p,
        );
        v += 1;
    }
}

fn search_quint_separator(
    amax: u64,
    factor: u64,
    uncovered_only: bool,
    middle_only: bool,
    cover_only: bool,
    top_limit: usize,
) {
    let start = Instant::now();
    let nthreads = worker_count();
    let partials: Vec<SeparatorPartial> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|t| {
                s.spawn(move || {
                    let mut p = SeparatorPartial::empty(top_limit);
                    let mut idx = vec![0u64; 5];
                    let mut a0 = 2 + t as u64;
                    while a0 <= amax {
                        idx[0] = a0;
                        rec_separator(
                            1,
                            a0 + 1,
                            amax,
                            &mut idx,
                            factor,
                            uncovered_only,
                            middle_only,
                            cover_only,
                            &mut p,
                        );
                        a0 += nthreads as u64;
                    }
                    p
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let result = partials
        .into_iter()
        .fold(SeparatorPartial::empty(top_limit), SeparatorPartial::merge);
    let dt = start.elapsed().as_secs_f64();
    println!(
        "raw separator sweep: primitive quintuples, amax={amax}, window_factor={factor}, uncovered_only={uncovered_only}, middle_only={middle_only}, cover_only={cover_only}, threads={nthreads}"
    );
    println!(
        "  primitive quintuples tested = {}   skipped(filter) = {}   pruned(partial) = {}   time = {dt:.2}s",
        result.tested, result.skipped, result.pruned
    );
    println!(
        "  worst n*S/(2B(n)) = {}/{} = {:.9}   at set = {:?}, n = {}",
        result.worst.0,
        result.worst.1,
        ratio_f(result.worst),
        result.worst_set,
        result.worst_n
    );
    if result.fails.is_empty() {
        println!("  raw separator failures (2B(n) <= nS): NONE in window");
    } else {
        println!("  *** raw separator failures found: {} ***", result.fails.len());
        for (s, n) in result.fails.iter().take(20) {
            println!("      set={s:?}  n={n}");
        }
    }
    if cover_only {
        println!(
            "  cover stats: max min(A) = {}, min(A)>54 count = {}, fourth(A)>120 count = {}",
            result.max_min_value, result.min_gt_54, result.fourth_gt_120
        );
        if !result.min_gt_examples.is_empty() {
            println!("  first min(A)>54 cover candidates:");
            for example in &result.min_gt_examples {
                println!("      {example:?}");
            }
        }
        if !result.fourth_gt_examples.is_empty() {
            println!("  first fourth(A)>120 cover candidates:");
            for example in &result.fourth_gt_examples {
                println!("      {example:?}");
            }
        }
    }
    if !result.top.is_empty() {
        println!("  top separator witnesses:");
        for record in result.top {
            println!(
                "      {}/{} = {:.9}   set = {:?}, n = {}",
                record.ratio.0,
                record.ratio.1,
                ratio_f(record.ratio),
                record.set,
                record.n
            );
        }
    }
}

/// Exact density gap for a finite set:
///   gap = 2*delta - S = (2*|B mod L| - sum(L/a))/L.
/// Returns (gap numerator, L, density count) when the gap is positive.
fn density_gap_positive(a: &[u64]) -> Option<(u128, u128, u128)> {
    let l = lcm_set_u128(a)?;
    if l > i128::MAX as u128 {
        return None;
    }
    let mut covered: i128 = 0;
    for mask in 1usize..(1usize << a.len()) {
        let mut sub_lcm = 1u128;
        let mut bits = 0usize;
        for (i, &d) in a.iter().enumerate() {
            if (mask & (1usize << i)) != 0 {
                sub_lcm = lcm_checked_u128(sub_lcm, d as u128)?;
                bits += 1;
            }
        }
        let term = (l / sub_lcm) as i128;
        if bits % 2 == 1 {
            covered += term;
        } else {
            covered -= term;
        }
    }
    if covered < 0 {
        return Some((0, l, 0));
    }
    let covered = covered as u128;
    let rhs: u128 = a.iter().map(|&d| l / d as u128).sum();
    let lhs = 2 * covered;
    if lhs > rhs {
        Some((lhs - rhs, l, covered))
    } else {
        Some((0, l, covered))
    }
}

#[derive(Clone)]
struct DensityPartial {
    tested: u64,
    skipped: u64,
    skipped_lcm: u64,
    min_gap: Option<(ExactRatio, Vec<u64>, u128, u128)>,
    top_count: usize,
    top_gaps: Vec<(ExactRatio, Vec<u64>, u128, u128)>,
    fails: Vec<(Vec<u64>, u128, u128)>,
}

impl DensityPartial {
    fn empty(top_count: usize) -> Self {
        Self {
            tested: 0,
            skipped: 0,
            skipped_lcm: 0,
            min_gap: None,
            top_count,
            top_gaps: Vec::new(),
            fails: Vec::new(),
        }
    }

    fn update_min_gap(&mut self, gap: ExactRatio, set: Vec<u64>, lcm: u128, count: u128) {
        let replace = match &self.min_gap {
            Some((old, _, _, _)) => gap.lt(*old),
            None => true,
        };
        if replace {
            self.min_gap = Some((gap, set, lcm, count));
        }
    }

    fn record_positive_gap(&mut self, gap: ExactRatio, set: Vec<u64>, lcm: u128, count: u128) {
        self.update_min_gap(gap, set.clone(), lcm, count);
        self.top_gaps.push((gap, set, lcm, count));
        self.top_gaps
            .sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        if self.top_gaps.len() > self.top_count {
            self.top_gaps.truncate(self.top_count);
        }
    }

    fn merge(mut self, other: DensityPartial) -> DensityPartial {
        self.tested += other.tested;
        self.skipped += other.skipped;
        self.skipped_lcm += other.skipped_lcm;
        for (gap, set, lcm, count) in other.top_gaps {
            self.record_positive_gap(gap, set, lcm, count);
        }
        self.fails.extend(other.fails);
        self
    }
}

fn rec_density(
    depth: usize,
    start_val: u64,
    amax: u64,
    idx: &mut Vec<u64>,
    gcd1_only: bool,
    uncovered_only: bool,
    hard_only: bool,
    residual_only: bool,
    p: &mut DensityPartial,
) {
    if depth == 5 {
        if !is_primitive(idx) {
            return;
        }
        if gcd1_only && common_gcd(idx) != 1 {
            p.skipped += 1;
            return;
        }
        if uncovered_only && !is_uncovered(idx) {
            p.skipped += 1;
            return;
        }
        if hard_only || residual_only {
            let easy = contains_two(idx) || reciprocal_sparse(idx) || at_least_three_good_charges(idx);
            if easy || (residual_only && scaled_quint_audit_applies(idx)) {
                p.skipped += 1;
                return;
            }
        }
        p.tested += 1;
        let Some((gap_num, lcm, count)) = density_gap_positive(idx) else {
            p.skipped_lcm += 1;
            return;
        };
        if gap_num == 0 {
            if p.fails.len() < 20 {
                p.fails.push((idx.clone(), lcm, count));
            }
        } else {
            p.record_positive_gap(ExactRatio::new(gap_num, lcm), idx.clone(), lcm, count);
        }
        return;
    }
    let mut v = start_val;
    while v <= amax {
        idx[depth] = v;
        rec_density(
            depth + 1,
            v + 1,
            amax,
            idx,
            gcd1_only,
            uncovered_only,
            hard_only,
            residual_only,
            p,
        );
        v += 1;
    }
}

fn search_quint_density(
    amax: u64,
    gcd1_only: bool,
    uncovered_only: bool,
    hard_only: bool,
    residual_only: bool,
    top_count: usize,
) {
    let start = Instant::now();
    let nthreads = worker_count();
    let partials: Vec<DensityPartial> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|t| {
                s.spawn(move || {
                    let mut p = DensityPartial::empty(top_count);
                    let mut idx = vec![0u64; 5];
                    let mut a0 = 2 + t as u64;
                    while a0 <= amax {
                        idx[0] = a0;
                        rec_density(
                            1,
                            a0 + 1,
                            amax,
                            &mut idx,
                            gcd1_only,
                            uncovered_only,
                            hard_only,
                            residual_only,
                            &mut p,
                        );
                        a0 += nthreads as u64;
                    }
                    p
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let result = partials
        .into_iter()
        .fold(DensityPartial::empty(top_count), DensityPartial::merge);
    let dt = start.elapsed().as_secs_f64();
    println!(
        "density gap sweep: primitive quintuples, amax={amax}, gcd1_only={gcd1_only}, uncovered_only={uncovered_only}, hard_only={hard_only}, residual_only={residual_only}, threads={nthreads}"
    );
    println!(
        "  tested = {}   skipped = {}   skipped_lcm = {}   time = {dt:.2}s",
        result.tested, result.skipped, result.skipped_lcm
    );
    if result.fails.is_empty() {
        println!("  failures (2*delta <= S): NONE");
    } else {
        println!("  *** density failures found: {} shown ***", result.fails.len());
        for (set, lcm, count) in result.fails.iter().take(20) {
            println!("      set={set:?}  lcm={lcm} covered_count={count}");
        }
    }
    if let Some((gap, set, lcm, count)) = &result.min_gap {
        println!(
            "  smallest positive 2*delta-S = {} at set={:?} (lcm={lcm}, covered_count={count})",
            gap, set
        );
    }
    if top_count > 1 && !result.top_gaps.is_empty() {
        println!("  top {top_count} smallest positive density gaps:");
        for (rank, (gap, set, lcm, count)) in result.top_gaps.iter().enumerate() {
            println!(
                "    {:>2}. {} at set={:?} (lcm={lcm}, covered_count={count})",
                rank + 1,
                gap,
                set
            );
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
    println!("2-in-A theorem applies = {}", contains_two(&a));
    println!("scaled Q-family audit applies = {}", is_scaled_q_family(&a));
    println!("scaled R-family audit applies = {}", is_scaled_r_family(&a));
    println!("scaled T-family audit applies = {}", is_scaled_t_family(&a));
    println!("scaled U-family audit applies = {}", is_scaled_u_family(&a));
    println!("scaled V-family audit applies = {}", is_scaled_v_family(&a));
    println!("scaled W-family audit applies = {}", is_scaled_w_family(&a));
    println!("scaled X-family audit applies = {}", is_scaled_x_family(&a));
    println!("scaled Y-family audit applies = {}", is_scaled_y_family(&a));
    println!("scaled Z-family audit applies = {}", is_scaled_z_family(&a));
    println!("scaled AA-family audit applies = {}", is_scaled_aa_family(&a));
    println!("scaled AB-family audit applies = {}", is_scaled_ab_family(&a));
    println!("scaled AC-family audit applies = {}", is_scaled_ac_family(&a));
    println!("scaled AD-family audit applies = {}", is_scaled_ad_family(&a));
    println!("scaled AE-family audit applies = {}", is_scaled_ae_family(&a));
    println!("scaled AF-family audit applies = {}", is_scaled_af_family(&a));
    println!("scaled AG-family audit applies = {}", is_scaled_ag_family(&a));
    println!("scaled AH-family audit applies = {}", is_scaled_ah_family(&a));
    println!("scaled AI-family audit applies = {}", is_scaled_ai_family(&a));
    println!("scaled AJ-family audit applies = {}", is_scaled_aj_family(&a));
    println!("scaled AK-family audit applies = {}", is_scaled_ak_family(&a));
    println!("scaled AL-family audit applies = {}", is_scaled_al_family(&a));
    println!("scaled AM-family audit applies = {}", is_scaled_am_family(&a));
    println!("scaled AN-family audit applies = {}", is_scaled_an_family(&a));
    println!("scaled AO-family audit applies = {}", is_scaled_ao_family(&a));
    println!("scaled AP-family audit applies = {}", is_scaled_ap_family(&a));
    println!("scaled AQ-family audit applies = {}", is_scaled_aq_family(&a));
    println!("scaled AR-family audit applies = {}", is_scaled_ar_family(&a));
    println!("scaled AS-family audit applies = {}", is_scaled_as_family(&a));
    println!("scaled AT-family audit applies = {}", is_scaled_at_family(&a));
    println!("scaled AU-family audit applies = {}", is_scaled_au_family(&a));
    println!("scaled AV-family audit applies = {}", is_scaled_av_family(&a));
    println!("scaled AW-family audit applies = {}", is_scaled_aw_family(&a));
    println!("scaled AX-family audit applies = {}", is_scaled_ax_family(&a));
    println!("reciprocal-sparse theorem applies = {}", reciprocal_sparse(&a));
    println!("charge-positivity theorem applies = {}", charge_positive(&a));
    println!(
        "quadruple two-good-charge rescue condition applies = {}",
        a.len() == 4 && at_least_two_good_charges(&a)
    );
    println!(
        "quintuple three-good-charge rescue condition applies = {}",
        a.len() == 5 && at_least_three_good_charges(&a)
    );
    println!("good charge count = {}", good_charge_count(&a));
    for &e in &a {
        println!("  charge sum at {e} = {}", charge_sum_at(&a, e));
    }
    Ok(())
}

fn command_density(raw: Option<&String>) -> Result<(), String> {
    let raw = raw.ok_or_else(|| "usage: fastcheck density <a,b,c,...>".to_string())?;
    let a = parse_set_arg(raw)?;
    let Some((gap_num, lcm, count)) = density_gap_positive(&a) else {
        return Err("lcm overflow while computing density".to_string());
    };
    let rhs: u128 = a.iter().map(|&d| lcm / d as u128).sum();
    let lhs = 2 * count;

    println!("set = {}", format_set(&a));
    println!("primitive = {}", is_primitive(&a));
    println!("common gcd = {}", common_gcd(&a));
    println!("lcm = {lcm}");
    println!("covered_count = {count}");
    println!("density delta = {}", ExactRatio::new(count, lcm));
    println!("S = {}", reciprocal_sum(&a));
    match lhs.cmp(&rhs) {
        Ordering::Greater => {
            println!("2*delta-S = {}", ExactRatio::new(gap_num, lcm));
            println!("density inequality 2*delta > S = true");
        }
        Ordering::Equal => {
            println!("2*delta-S = 0");
            println!("density inequality 2*delta > S = false (equality)");
        }
        Ordering::Less => {
            println!("S-2*delta = {}", ExactRatio::new(rhs - lhs, lcm));
            println!("density inequality 2*delta > S = false");
        }
    }
    Ok(())
}

fn command_tower(raw: Option<&String>) -> Result<(), String> {
    let raw = raw.ok_or_else(|| "usage: fastcheck tower <a,b,c,d,e>".to_string())?;
    let a = parse_set_arg(raw)?;
    let maxa = *a.iter().max().ok_or_else(|| "empty set".to_string())?;
    let s = reciprocal_sum(&a);
    let Some(cap) = tower_cap(s) else {
        return Err("could not compute tower cap".to_string());
    };
    println!("set = {}", format_set(&a));
    println!("primitive = {}", is_primitive(&a));
    println!("common gcd = {}", common_gcd(&a));
    println!("S = {s}");
    println!("tower cap = {cap}");
    if cap < maxa {
        println!("tower window is empty");
        return Ok(());
    }
    if cap > 200_000_000 {
        return Err(format!("tower cap {cap} exceeds the safety limit"));
    }

    let pref = b_prefix(&a, cap);
    let mut first_fail = None;
    let mut zero_count = 0u64;
    let mut min_margin_num: Option<u128> = None;
    let mut min_margin_m = maxa;
    for m in maxa..=cap {
        let bm = pref[m as usize] as u128;
        let lhs = 2 * bm * s.den;
        let rhs = (m as u128 + 1) * s.num;
        if lhs < rhs && first_fail.is_none() {
            first_fail = Some(m);
        }
        if lhs == rhs {
            zero_count += 1;
        }
        if lhs >= rhs {
            let margin = lhs - rhs;
            let take = match min_margin_num {
                Some(current) => margin < current,
                None => true,
            };
            if take {
                min_margin_num = Some(margin);
                min_margin_m = m;
            }
        }
    }

    match min_margin_num {
        Some(num) => println!(
            "minimum tower margin 2B(m)-(m+1)S = {} at m={}",
            ExactRatio::new(num, s.den),
            min_margin_m
        ),
        None => println!("no nonnegative tower margin in the window"),
    }
    println!("zero margins = {zero_count}");
    match first_fail {
        Some(m) => println!("tower inequality 2B(m) >= (m+1)S: FAIL first at m={m}"),
        None => println!("tower inequality 2B(m) >= (m+1)S: PASS"),
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

/// Per-thread accumulator for the quadruple certificate sweep, mergeable so the
/// sweep can be split across cores and reduced exactly.
struct SweepPartial {
    primitive: u64,
    sparse: u64,
    charge: u64,
    two_good_rescued: u64,
    symbolic: u64,
    residual: u64,
    attempted: u64,
    cert_pass: u64,
    cert_fail: u64,
    separator_pass: u64,
    skipped_lcm: u64,
    worst_pass: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    worst_fail: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    skipped_examples: Vec<(Vec<u64>, u64)>,
}

impl SweepPartial {
    fn empty() -> Self {
        SweepPartial {
            primitive: 0, sparse: 0, charge: 0, two_good_rescued: 0, symbolic: 0,
            residual: 0, attempted: 0, cert_pass: 0, cert_fail: 0, separator_pass: 0,
            skipped_lcm: 0, worst_pass: None, worst_fail: None, skipped_examples: Vec::new(),
        }
    }
    fn merge(mut self, other: SweepPartial) -> SweepPartial {
        self.primitive += other.primitive;
        self.sparse += other.sparse;
        self.charge += other.charge;
        self.two_good_rescued += other.two_good_rescued;
        self.symbolic += other.symbolic;
        self.residual += other.residual;
        self.attempted += other.attempted;
        self.cert_pass += other.cert_pass;
        self.cert_fail += other.cert_fail;
        self.separator_pass += other.separator_pass;
        self.skipped_lcm += other.skipped_lcm;
        if let Some((r, set, cert)) = other.worst_pass {
            update_cert_worst(&mut self.worst_pass, r, set, cert);
        }
        if let Some((r, set, cert)) = other.worst_fail {
            update_cert_worst(&mut self.worst_fail, r, set, cert);
        }
        for e in other.skipped_examples {
            if self.skipped_examples.len() < 8 {
                self.skipped_examples.push(e);
            }
        }
        self
    }
}

/// The `b<c<d` sweep for a fixed smallest element `a` (one parallel unit).
fn sweep_quad_for_a(a: u64, amax: u64, cap: u64) -> Result<SweepPartial, String> {
    let mut p = SweepPartial::empty();
    for b in a + 1..=amax - 2 {
        for c in b + 1..=amax - 1 {
            for d in c + 1..=amax {
                let set = vec![a, b, c, d];
                if !is_primitive(&set) {
                    continue;
                }
                p.primitive += 1;
                let is_sparse = reciprocal_sparse(&set);
                if charge_positive(&set) {
                    p.charge += 1;
                }
                let is_two_good_rescued = at_least_two_good_charges(&set);
                if is_sparse {
                    p.sparse += 1;
                }
                if is_two_good_rescued {
                    p.two_good_rescued += 1;
                }
                if is_sparse || is_two_good_rescued {
                    p.symbolic += 1;
                    continue;
                }

                p.residual += 1;
                let Some(lcm) = lcm_set(&set, cap) else {
                    p.skipped_lcm += 1;
                    if p.skipped_examples.len() < 8 {
                        if let Some(full_lcm) = lcm_set(&set, u64::MAX) {
                            p.skipped_examples.push((set, full_lcm));
                        }
                    }
                    continue;
                };

                p.attempted += 1;
                let cert = periodic_certificate_with_lcm(&set, lcm)?;
                if cert.union_bound_separator {
                    p.separator_pass += 1;
                }
                if cert.ordering_free {
                    p.cert_pass += 1;
                    update_cert_worst(&mut p.worst_pass, cert.beta_over_alpha, set, cert);
                } else {
                    p.cert_fail += 1;
                    update_cert_worst(&mut p.worst_fail, cert.beta_over_alpha, set, cert);
                }
            }
        }
    }
    Ok(p)
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
    let nthreads = worker_count();
    let a_hi = amax - 3;
    // Split the smallest element `a` across threads round-robin; the b<c<d sweeps
    // for distinct `a` are independent, and the merge is exact — the counts and
    // worst certificates match the serial version.
    let thread_results: Vec<Result<SweepPartial, String>> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|t| {
                s.spawn(move || {
                    let mut acc = SweepPartial::empty();
                    let mut a = 2 + t as u64;
                    while a <= a_hi {
                        acc = acc.merge(sweep_quad_for_a(a, amax, cap)?);
                        a += nthreads as u64;
                    }
                    Ok(acc)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut merged = SweepPartial::empty();
    for tr in thread_results {
        merged = merged.merge(tr?);
    }
    let SweepPartial {
        primitive, sparse, charge, two_good_rescued, symbolic, residual, attempted,
        cert_pass, cert_fail, separator_pass, skipped_lcm, worst_pass, worst_fail,
        skipped_examples,
    } = merged;

    println!("primitive quadruples with entries <= {amax}: {primitive}");
    println!("reciprocal-sparse theorem applies: {sparse}");
    println!("charge-positivity theorem applies: {charge}");
    println!("two-good-charge rescue condition applies: {two_good_rescued}");
    println!("symbolically done by sparse or two-good-charge rescue: {symbolic}");
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

struct QuintSweepPartial {
    primitive: u64,
    sparse: u64,
    two_in_a: u64,
    scaled_q: u64,
    scaled_r: u64,
    scaled_t: u64,
    scaled_u: u64,
    scaled_v: u64,
    scaled_w: u64,
    scaled_x: u64,
    scaled_y: u64,
    scaled_z: u64,
    scaled_aa: u64,
    scaled_ab: u64,
    scaled_ac: u64,
    scaled_ad: u64,
    scaled_ae: u64,
    scaled_af: u64,
    scaled_ag: u64,
    scaled_ah: u64,
    scaled_ai: u64,
    scaled_aj: u64,
    scaled_ak: u64,
    scaled_al: u64,
    scaled_am: u64,
    scaled_an: u64,
    scaled_ao: u64,
    scaled_ap: u64,
    scaled_aq: u64,
    scaled_ar: u64,
    scaled_as: u64,
    scaled_at: u64,
    scaled_au: u64,
    scaled_av: u64,
    scaled_aw: u64,
    scaled_ax: u64,
    charge: u64,
    three_good_rescued: u64,
    symbolic: u64,
    residual: u64,
    attempted: u64,
    cert_pass: u64,
    cert_fail: u64,
    separator_pass: u64,
    separator_fail: u64,
    skipped_lcm: u64,
    worst_pass: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    worst_fail: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    worst_separator_pass: Option<(ExactRatio, Vec<u64>, PeriodicCertificate)>,
    skipped_examples: Vec<(Vec<u64>, u64)>,
    first_separator_fail: Option<(Vec<u64>, PeriodicCertificate)>,
    residual_classes: BTreeMap<Vec<u64>, u64>,
}

impl QuintSweepPartial {
    fn empty() -> Self {
        Self {
            primitive: 0,
            sparse: 0,
            two_in_a: 0,
            scaled_q: 0,
            scaled_r: 0,
            scaled_t: 0,
            scaled_u: 0,
            scaled_v: 0,
            scaled_w: 0,
            scaled_x: 0,
            scaled_y: 0,
            scaled_z: 0,
            scaled_aa: 0,
            scaled_ab: 0,
            scaled_ac: 0,
            scaled_ad: 0,
            scaled_ae: 0,
            scaled_af: 0,
            scaled_ag: 0,
            scaled_ah: 0,
            scaled_ai: 0,
            scaled_aj: 0,
            scaled_ak: 0,
            scaled_al: 0,
            scaled_am: 0,
            scaled_an: 0,
            scaled_ao: 0,
            scaled_ap: 0,
            scaled_aq: 0,
            scaled_ar: 0,
            scaled_as: 0,
            scaled_at: 0,
            scaled_au: 0,
            scaled_av: 0,
            scaled_aw: 0,
            scaled_ax: 0,
            charge: 0,
            three_good_rescued: 0,
            symbolic: 0,
            residual: 0,
            attempted: 0,
            cert_pass: 0,
            cert_fail: 0,
            separator_pass: 0,
            separator_fail: 0,
            skipped_lcm: 0,
            worst_pass: None,
            worst_fail: None,
            worst_separator_pass: None,
            skipped_examples: Vec::new(),
            first_separator_fail: None,
            residual_classes: BTreeMap::new(),
        }
    }

    fn merge(mut self, other: QuintSweepPartial) -> QuintSweepPartial {
        self.primitive += other.primitive;
        self.sparse += other.sparse;
        self.two_in_a += other.two_in_a;
        self.scaled_q += other.scaled_q;
        self.scaled_r += other.scaled_r;
        self.scaled_t += other.scaled_t;
        self.scaled_u += other.scaled_u;
        self.scaled_v += other.scaled_v;
        self.scaled_w += other.scaled_w;
        self.scaled_x += other.scaled_x;
        self.scaled_y += other.scaled_y;
        self.scaled_z += other.scaled_z;
        self.scaled_aa += other.scaled_aa;
        self.scaled_ab += other.scaled_ab;
        self.scaled_ac += other.scaled_ac;
        self.scaled_ad += other.scaled_ad;
        self.scaled_ae += other.scaled_ae;
        self.scaled_af += other.scaled_af;
        self.scaled_ag += other.scaled_ag;
        self.scaled_ah += other.scaled_ah;
        self.scaled_ai += other.scaled_ai;
        self.scaled_aj += other.scaled_aj;
        self.scaled_ak += other.scaled_ak;
        self.scaled_al += other.scaled_al;
        self.scaled_am += other.scaled_am;
        self.scaled_an += other.scaled_an;
        self.scaled_ao += other.scaled_ao;
        self.scaled_ap += other.scaled_ap;
        self.scaled_aq += other.scaled_aq;
        self.scaled_ar += other.scaled_ar;
        self.scaled_as += other.scaled_as;
        self.scaled_at += other.scaled_at;
        self.scaled_au += other.scaled_au;
        self.scaled_av += other.scaled_av;
        self.scaled_aw += other.scaled_aw;
        self.scaled_ax += other.scaled_ax;
        self.charge += other.charge;
        self.three_good_rescued += other.three_good_rescued;
        self.symbolic += other.symbolic;
        self.residual += other.residual;
        self.attempted += other.attempted;
        self.cert_pass += other.cert_pass;
        self.cert_fail += other.cert_fail;
        self.separator_pass += other.separator_pass;
        self.separator_fail += other.separator_fail;
        self.skipped_lcm += other.skipped_lcm;
        if let Some((r, set, cert)) = other.worst_pass {
            update_cert_worst(&mut self.worst_pass, r, set, cert);
        }
        if let Some((r, set, cert)) = other.worst_fail {
            update_cert_worst(&mut self.worst_fail, r, set, cert);
        }
        if let Some((r, set, cert)) = other.worst_separator_pass {
            update_cert_worst(&mut self.worst_separator_pass, r, set, cert);
        }
        for e in other.skipped_examples {
            if self.skipped_examples.len() < 8 {
                self.skipped_examples.push(e);
            }
        }
        if self.first_separator_fail.is_none() {
            self.first_separator_fail = other.first_separator_fail;
        }
        for (class, count) in other.residual_classes {
            *self.residual_classes.entry(class).or_insert(0) += count;
        }
        self
    }
}

fn normalized_by_common_gcd(set: &[u64]) -> Vec<u64> {
    let g = common_gcd(set);
    if g <= 1 {
        set.to_vec()
    } else {
        set.iter().map(|x| x / g).collect()
    }
}

fn sweep_quint_for_a(a: u64, amax: u64, cap: u64) -> Result<QuintSweepPartial, String> {
    let mut p = QuintSweepPartial::empty();
    for b in a + 1..=amax - 3 {
        for c in b + 1..=amax - 2 {
            for d in c + 1..=amax - 1 {
                for e in d + 1..=amax {
                    let set = vec![a, b, c, d, e];
                    if !is_primitive(&set) {
                        continue;
                    }
                    p.primitive += 1;
                    let is_sparse = reciprocal_sparse(&set);
                    let is_two_in_a = contains_two(&set);
                    let is_scaled_q = is_scaled_q_family(&set);
                    let is_scaled_r = is_scaled_r_family(&set);
                    let is_scaled_t = is_scaled_t_family(&set);
                    let is_scaled_u = is_scaled_u_family(&set);
                    let is_scaled_v = is_scaled_v_family(&set);
                    let is_scaled_w = is_scaled_w_family(&set);
                    let is_scaled_x = is_scaled_x_family(&set);
                    let is_scaled_y = is_scaled_y_family(&set);
                    let is_scaled_z = is_scaled_z_family(&set);
                    let is_scaled_aa = is_scaled_aa_family(&set);
                    let is_scaled_ab = is_scaled_ab_family(&set);
                    let is_scaled_ac = is_scaled_ac_family(&set);
                    let is_scaled_ad = is_scaled_ad_family(&set);
                    let is_scaled_ae = is_scaled_ae_family(&set);
                    let is_scaled_af = is_scaled_af_family(&set);
                    let is_scaled_ag = is_scaled_ag_family(&set);
                    let is_scaled_ah = is_scaled_ah_family(&set);
                    let is_scaled_ai = is_scaled_ai_family(&set);
                    let is_scaled_aj = is_scaled_aj_family(&set);
                    let is_scaled_ak = is_scaled_ak_family(&set);
                    let is_scaled_al = is_scaled_al_family(&set);
                    let is_scaled_am = is_scaled_am_family(&set);
                    let is_scaled_an = is_scaled_an_family(&set);
                    let is_scaled_ao = is_scaled_ao_family(&set);
                    let is_scaled_ap = is_scaled_ap_family(&set);
                    let is_scaled_aq = is_scaled_aq_family(&set);
                    let is_scaled_ar = is_scaled_ar_family(&set);
                    let is_scaled_as = is_scaled_as_family(&set);
                    let is_scaled_at = is_scaled_at_family(&set);
                    let is_scaled_au = is_scaled_au_family(&set);
                    let is_scaled_av = is_scaled_av_family(&set);
                    let is_scaled_aw = is_scaled_aw_family(&set);
                    let is_scaled_ax = is_scaled_ax_family(&set);
                    let is_charge = charge_positive(&set);
                    let is_three_good = at_least_three_good_charges(&set);
                    if is_sparse {
                        p.sparse += 1;
                    }
                    if is_two_in_a {
                        p.two_in_a += 1;
                    }
                    if is_scaled_q {
                        p.scaled_q += 1;
                    }
                    if is_scaled_r {
                        p.scaled_r += 1;
                    }
                    if is_scaled_t {
                        p.scaled_t += 1;
                    }
                    if is_scaled_u {
                        p.scaled_u += 1;
                    }
                    if is_scaled_v {
                        p.scaled_v += 1;
                    }
                    if is_scaled_w {
                        p.scaled_w += 1;
                    }
                    if is_scaled_x {
                        p.scaled_x += 1;
                    }
                    if is_scaled_y {
                        p.scaled_y += 1;
                    }
                    if is_scaled_z {
                        p.scaled_z += 1;
                    }
                    if is_scaled_aa {
                        p.scaled_aa += 1;
                    }
                    if is_scaled_ab {
                        p.scaled_ab += 1;
                    }
                    if is_scaled_ac {
                        p.scaled_ac += 1;
                    }
                    if is_scaled_ad {
                        p.scaled_ad += 1;
                    }
                    if is_scaled_ae {
                        p.scaled_ae += 1;
                    }
                    if is_scaled_af {
                        p.scaled_af += 1;
                    }
                    if is_scaled_ag {
                        p.scaled_ag += 1;
                    }
                    if is_scaled_ah {
                        p.scaled_ah += 1;
                    }
                    if is_scaled_ai {
                        p.scaled_ai += 1;
                    }
                    if is_scaled_aj {
                        p.scaled_aj += 1;
                    }
                    if is_scaled_ak {
                        p.scaled_ak += 1;
                    }
                    if is_scaled_al {
                        p.scaled_al += 1;
                    }
                    if is_scaled_am {
                        p.scaled_am += 1;
                    }
                    if is_scaled_an {
                        p.scaled_an += 1;
                    }
                    if is_scaled_ao {
                        p.scaled_ao += 1;
                    }
                    if is_scaled_ap {
                        p.scaled_ap += 1;
                    }
                    if is_scaled_aq {
                        p.scaled_aq += 1;
                    }
                    if is_scaled_ar {
                        p.scaled_ar += 1;
                    }
                    if is_scaled_as {
                        p.scaled_as += 1;
                    }
                    if is_scaled_at {
                        p.scaled_at += 1;
                    }
                    if is_scaled_au {
                        p.scaled_au += 1;
                    }
                    if is_scaled_av {
                        p.scaled_av += 1;
                    }
                    if is_scaled_aw {
                        p.scaled_aw += 1;
                    }
                    if is_scaled_ax {
                        p.scaled_ax += 1;
                    }
                    if is_charge {
                        p.charge += 1;
                    }
                    if is_three_good {
                        p.three_good_rescued += 1;
                    }
                    if is_sparse
                        || is_two_in_a
                        || is_scaled_q
                        || is_scaled_r
                        || is_scaled_t
                        || is_scaled_u
                        || is_scaled_v
                        || is_scaled_w
                        || is_scaled_x
                        || is_scaled_y
                        || is_scaled_z
                        || is_scaled_aa
                        || is_scaled_ab
                        || is_scaled_ac
                        || is_scaled_ad
                        || is_scaled_ae
                        || is_scaled_af
                        || is_scaled_ag
                        || is_scaled_ah
                        || is_scaled_ai
                        || is_scaled_aj
                        || is_scaled_ak
                        || is_scaled_al
                        || is_scaled_am
                        || is_scaled_an
                        || is_scaled_ao
                        || is_scaled_ap
                        || is_scaled_aq
                        || is_scaled_ar
                        || is_scaled_as
                        || is_scaled_at
                        || is_scaled_au
                        || is_scaled_av
                        || is_scaled_aw
                        || is_scaled_ax
                        || is_three_good
                    {
                        p.symbolic += 1;
                        continue;
                    }

                    p.residual += 1;
                    let class = normalized_by_common_gcd(&set);
                    *p.residual_classes.entry(class).or_insert(0) += 1;
                    let Some(lcm) = lcm_set(&set, cap) else {
                        p.skipped_lcm += 1;
                        if p.skipped_examples.len() < 8 {
                            if let Some(full_lcm) = lcm_set(&set, u64::MAX) {
                                p.skipped_examples.push((set, full_lcm));
                            }
                        }
                        continue;
                    };

                    p.attempted += 1;
                    let cert = periodic_certificate_with_lcm(&set, lcm)?;
                    if cert.union_bound_separator {
                        p.separator_pass += 1;
                        update_cert_worst(
                            &mut p.worst_separator_pass,
                            cert.beta_over_alpha,
                            set.clone(),
                            cert.clone(),
                        );
                    } else {
                        p.separator_fail += 1;
                        if p.first_separator_fail.is_none() {
                            p.first_separator_fail = Some((set.clone(), cert.clone()));
                        }
                    }
                    if cert.ordering_free {
                        p.cert_pass += 1;
                        update_cert_worst(&mut p.worst_pass, cert.beta_over_alpha, set, cert);
                    } else {
                        p.cert_fail += 1;
                        update_cert_worst(&mut p.worst_fail, cert.beta_over_alpha, set, cert);
                    }
                }
            }
        }
    }
    Ok(p)
}

fn command_sweep_quint_cert(
    amax_raw: Option<&String>,
    cap_raw: Option<&String>,
    top_raw: Option<&String>,
) -> Result<(), String> {
    let amax = match amax_raw {
        Some(x) => parse_u64_arg(x)?,
        None => 35,
    };
    let cap = match cap_raw {
        Some(x) => parse_u64_arg(x)?,
        None => 3_000_000,
    };
    let top_classes = match top_raw {
        Some(x) => parse_u64_arg(x)? as usize,
        None => 10,
    };
    if amax < 6 {
        return Err("amax must be at least 6 for quintuples".to_string());
    }

    let start = Instant::now();
    let nthreads = worker_count();
    let a_hi = amax - 4;
    let thread_results: Vec<Result<QuintSweepPartial, String>> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|t| {
                s.spawn(move || {
                    let mut acc = QuintSweepPartial::empty();
                    let mut a = 2 + t as u64;
                    while a <= a_hi {
                        acc = acc.merge(sweep_quint_for_a(a, amax, cap)?);
                        a += nthreads as u64;
                    }
                    Ok(acc)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut merged = QuintSweepPartial::empty();
    for tr in thread_results {
        merged = merged.merge(tr?);
    }

    println!(
        "primitive quintuples with entries <= {amax}: {}",
        merged.primitive
    );
    println!("2-in-A theorem applies: {}", merged.two_in_a);
    println!(
        "scaled Q-family audit applies: {}",
        merged.scaled_q
    );
    println!(
        "scaled R-family audit applies: {}",
        merged.scaled_r
    );
    println!(
        "scaled T-family audit applies: {}",
        merged.scaled_t
    );
    println!(
        "scaled U-family audit applies: {}",
        merged.scaled_u
    );
    println!(
        "scaled V-family audit applies: {}",
        merged.scaled_v
    );
    println!(
        "scaled W-family audit applies: {}",
        merged.scaled_w
    );
    println!(
        "scaled X-family audit applies: {}",
        merged.scaled_x
    );
    println!(
        "scaled Y-family audit applies: {}",
        merged.scaled_y
    );
    println!(
        "scaled Z-family audit applies: {}",
        merged.scaled_z
    );
    println!(
        "scaled AA-family audit applies: {}",
        merged.scaled_aa
    );
    println!(
        "scaled AB-family audit applies: {}",
        merged.scaled_ab
    );
    println!(
        "scaled AC-family audit applies: {}",
        merged.scaled_ac
    );
    println!(
        "scaled AD-family audit applies: {}",
        merged.scaled_ad
    );
    println!(
        "scaled AE-family audit applies: {}",
        merged.scaled_ae
    );
    println!(
        "scaled AF-family audit applies: {}",
        merged.scaled_af
    );
    println!(
        "scaled AG-family audit applies: {}",
        merged.scaled_ag
    );
    println!(
        "scaled AH-family audit applies: {}",
        merged.scaled_ah
    );
    println!(
        "scaled AI-family audit applies: {}",
        merged.scaled_ai
    );
    println!(
        "scaled AJ-family audit applies: {}",
        merged.scaled_aj
    );
    println!(
        "scaled AK-family audit applies: {}",
        merged.scaled_ak
    );
    println!(
        "scaled AL-family audit applies: {}",
        merged.scaled_al
    );
    println!(
        "scaled AM-family audit applies: {}",
        merged.scaled_am
    );
    println!(
        "scaled AN-family audit applies: {}",
        merged.scaled_an
    );
    println!(
        "scaled AO-family audit applies: {}",
        merged.scaled_ao
    );
    println!(
        "scaled AP-family audit applies: {}",
        merged.scaled_ap
    );
    println!(
        "scaled AQ-family audit applies: {}",
        merged.scaled_aq
    );
    println!(
        "scaled AR-family audit applies: {}",
        merged.scaled_ar
    );
    println!(
        "scaled AS-family audit applies: {}",
        merged.scaled_as
    );
    println!(
        "scaled AT-family audit applies: {}",
        merged.scaled_at
    );
    println!(
        "scaled AU-family audit applies: {}",
        merged.scaled_au
    );
    println!(
        "scaled AV-family audit applies: {}",
        merged.scaled_av
    );
    println!(
        "scaled AW-family audit applies: {}",
        merged.scaled_aw
    );
    println!(
        "scaled AX-family audit applies: {}",
        merged.scaled_ax
    );
    println!("reciprocal-sparse theorem applies: {}", merged.sparse);
    println!("charge-positivity theorem applies: {}", merged.charge);
    println!(
        "three-good-charge rescue condition applies: {}",
        merged.three_good_rescued
    );
    println!(
        "handled by 2-in-A, scaled-family audits, sparse, or three-good-charge rescue: {}",
        merged.symbolic
    );
    println!("residual after those regimes: {}", merged.residual);
    println!(
        "exact residual certificates attempted with lcm <= {cap}: {}",
        merged.attempted
    );
    println!("  ordering-free PASS: {}", merged.cert_pass);
    println!("  ordering-free FAIL: {}", merged.cert_fail);
    println!("  skipped by lcm cap: {}", merged.skipped_lcm);
    println!("  union-bound separator PASS: {}", merged.separator_pass);
    println!("  union-bound separator FAIL: {}", merged.separator_fail);
    println!("residual classes up to common scaling: {}", merged.residual_classes.len());
    println!("time = {:.2}s", start.elapsed().as_secs_f64());

    if let Some((ratio, set, cert)) = merged.worst_pass {
        println!();
        println!("worst passing residual certificate:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {ratio}");
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
        println!("  union-bound separator = {}", cert.union_bound_separator);
    }
    if let Some((ratio, set, cert)) = merged.worst_separator_pass {
        println!();
        println!("worst residual with union-bound separator:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {ratio}");
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
    }
    if let Some((ratio, set, cert)) = merged.worst_fail {
        println!();
        println!("largest failed residual certificate:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {ratio}");
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
    }
    if let Some((set, cert)) = merged.first_separator_fail {
        println!();
        println!("first residual failing the union-bound separator:");
        println!("  set = {}", format_set(&set));
        println!("  beta/alpha = {}", cert.beta_over_alpha);
        println!("  alpha = {}", cert.alpha);
        println!("  beta  = {}", cert.beta);
    }
    if !merged.skipped_examples.is_empty() {
        println!();
        println!("first residual sets skipped by lcm cap:");
        for (set, lcm) in merged.skipped_examples {
            println!("  {} lcm={}", format_set(&set), lcm);
        }
    }
    if !merged.residual_classes.is_empty() {
        let mut classes: Vec<_> = merged.residual_classes.into_iter().collect();
        classes.sort_by(|(set_a, count_a), (set_b, count_b)| {
            count_b.cmp(count_a).then_with(|| set_a.cmp(set_b))
        });
        println!();
        println!("top residual classes up to common scaling:");
        for (class, count) in classes.into_iter().take(top_classes) {
            println!("  {:>5} x {}", count, format_set(&class));
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
        "density" => {
            if let Err(err) = command_density(args.get(2)) {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
        "tower" => {
            if let Err(err) = command_tower(args.get(2)) {
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
        "sweep-quint-cert" => {
            if let Err(err) = command_sweep_quint_cert(args.get(2), args.get(3), args.get(4)) {
                eprintln!("{err}");
                std::process::exit(2);
            }
        }
        "quint-separator" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30);
            let f: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(80);
            let unc = args.iter().any(|s| s == "--uncovered");
            let middle = args.iter().any(|s| s == "--middle");
            let cover = args.iter().any(|s| s == "--cover");
            let mut top_count = 0usize;
            for (i, arg) in args.iter().enumerate() {
                if arg == "--top" {
                    top_count = args
                        .get(i + 1)
                        .and_then(|s| s.parse::<usize>().ok())
                        .unwrap_or(10);
                } else if let Some(raw) = arg.strip_prefix("--top=") {
                    top_count = raw.parse::<usize>().unwrap_or(10);
                }
            }
            search_quint_separator(amax, f, unc, middle, cover, top_count);
        }
        "quint-density" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(42);
            let gcd1 = args.iter().any(|s| s == "--gcd1");
            let unc = args.iter().any(|s| s == "--uncovered");
            let hard = args.iter().any(|s| s == "--hard");
            let residual = args.iter().any(|s| s == "--residual");
            let mut top_count = 1usize;
            for (i, arg) in args.iter().enumerate() {
                if arg == "--top" {
                    top_count = args
                        .get(i + 1)
                        .and_then(|s| s.parse::<usize>().ok())
                        .unwrap_or(10);
                } else if let Some(raw) = arg.strip_prefix("--top=") {
                    top_count = raw.parse::<usize>().unwrap_or(10);
                }
            }
            top_count = top_count.max(1);
            search_quint_density(amax, gcd1, unc, hard, residual, top_count);
        }
        "bench" => {
            let amax: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40);
            let t = Instant::now();
            search(4, amax, 40, false);
            eprintln!("bench total {:.2}s", t.elapsed().as_secs_f64());
        }
        other => {
            eprintln!(
                "unknown mode '{other}'. modes: selftest triples quads quints set classify density tower cert sweep-quad-cert sweep-quint-cert quint-separator quint-density bench"
            );
            std::process::exit(2);
        }
    }
}
