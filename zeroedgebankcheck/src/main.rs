use std::collections::{BTreeMap, BTreeSet};

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.abs()
}

fn lcm(a: i128, b: i128) -> i128 {
    a / gcd(a, b) * b
}

fn reduce(n: i128, d: i128) -> (i128, i128) {
    let g = gcd(n, d);
    (n / g, d / g)
}

fn bad_indices(dd: &[i128; 5]) -> Vec<usize> {
    (0..5)
        .filter(|&i| {
            (0..5)
                .filter(|&j| j != i)
                .map(|j| gcd(dd[i], dd[j]))
                .sum::<i128>()
                >= dd[i]
        })
        .collect()
}

fn induced_strong_edges(dd: &[i128; 5], vertices: &[usize]) -> usize {
    let mut edges = 0;
    for x in 0..vertices.len() {
        for y in (x + 1)..vertices.len() {
            let (i, j) = (vertices[x], vertices[y]);
            if 4 * gcd(dd[i], dd[j]) >= dd[i].min(dd[j]) {
                edges += 1;
            }
        }
    }
    edges
}

fn normalize(fractions: &[(i128, i128); 5]) -> [i128; 5] {
    let denominator_lcm = fractions.iter().fold(1, |l, &(_, d)| lcm(l, d));
    let mut values: [i128; 5] =
        std::array::from_fn(|i| fractions[i].0 * (denominator_lcm / fractions[i].1));
    let common = values.iter().fold(0, |g, &value| gcd(g, value));
    for value in &mut values {
        *value /= common;
    }
    values.sort_unstable();
    values
}

fn is_antichain(dd: &[i128; 5]) -> bool {
    for i in 0..5 {
        for j in (i + 1)..5 {
            if dd[i] == dd[j] || dd[j] % dd[i] == 0 {
                return false;
            }
        }
    }
    true
}

fn parse_bank(text: &str) -> BTreeSet<[i128; 5]> {
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let values: Vec<_> = line
                .split(',')
                .map(|value| value.parse::<i128>().expect("invalid bank value"))
                .collect();
            assert_eq!(values.len(), 5, "invalid bank row: {line}");
            [values[0], values[1], values[2], values[3], values[4]]
        })
        .collect()
}

fn is_zero_edge_residual(dd: &[i128; 5]) -> bool {
    if dd[4] >= 7 * dd[0] || !is_antichain(dd) {
        return false;
    }
    let bad = bad_indices(dd);
    if bad.len() != 3 || induced_strong_edges(dd, &bad) != 0 {
        return false;
    }
    let sum_d: i128 = dd.iter().sum();
    if 7 * sum_d > 1135 * dd[0] {
        return false;
    }
    let mut sum_gcd = 0i128;
    for i in 0..5 {
        for j in (i + 1)..5 {
            sum_gcd += gcd(dd[i], dd[j]);
        }
    }
    2 * (sum_d - 2 * sum_gcd) <= 7 * dd[0]
}

fn tower_margin(dd: &[i128; 5]) -> (i128, i128, i128) {
    let l = dd.iter().fold(1, |value, &d| lcm(value, d));
    let mut p: Vec<_> = dd.iter().map(|&d| l / d).collect();
    p.sort_unstable();
    let prod: i128 = p.iter().product();
    let nsum: i128 = p.iter().map(|&a| prod / a).sum();
    let cap = (1135 * prod) / (7 * nsum) - 1;
    let mut count = 0i128;
    let mut worst = i128::MAX;
    let mut worst_m = 0i128;
    for m in 1..=cap {
        if p.iter().any(|&a| m % a == 0) {
            count += 1;
        }
        if m >= p[4] {
            let margin = 2 * count * prod - (m + 1) * nsum;
            if margin < worst {
                worst = margin;
                worst_m = m;
            }
        }
    }
    (worst, prod, worst_m)
}

fn main() {
    // Anchor the first good at 1. Each entry maps t=g2/g1 to every possible
    // r=b/g1 compatible with the same bad vertex's two good pins.
    let mut compatible: BTreeMap<(i128, i128), BTreeSet<(i128, i128)>> = BTreeMap::new();
    let mut descriptors = 0u64;
    for c1 in 2..=10i128 {
        for c2 in 2..=10i128 {
            if 5 * (c1 + c2) < 3 * c1 * c2 {
                continue;
            }
            for k1 in 2..(7 * c1) {
                if gcd(c1, k1) != 1 || c1 >= 7 * k1 {
                    continue;
                }
                for k2 in 2..(7 * c2) {
                    if gcd(c2, k2) != 1 || c2 >= 7 * k2 {
                        continue;
                    }
                    let r = (c1, k1); // b/g1
                    let t = reduce(c1 * k2, k1 * c2); // g2/g1
                    if t == (1, 1) {
                        continue;
                    }
                    descriptors += 1;
                    compatible.entry(t).or_default().insert(r);
                }
            }
        }
    }

    let mut rational_triples = 0u64;
    let mut normalized = BTreeSet::new();
    let mut bank = BTreeSet::new();
    for (&t, bad_ratios) in &compatible {
        let ratios: Vec<_> = bad_ratios.iter().copied().collect();
        for i in 0..ratios.len() {
            for j in (i + 1)..ratios.len() {
                for k in (j + 1)..ratios.len() {
                    rational_triples += 1;
                    let fractions = [(1, 1), t, ratios[i], ratios[j], ratios[k]];
                    let dd = normalize(&fractions);
                    normalized.insert(dd);
                    if is_zero_edge_residual(&dd) {
                        bank.insert(dd);
                    }
                }
            }
        }
    }

    let expected = parse_bank(include_str!("../bank4.csv"));
    assert_eq!(bank, expected, "generated bank differs from bank4.csv");

    println!("=== zero-edge rational-template bank ===");
    println!("pin descriptors: {descriptors}");
    println!("distinct good ratios: {}", compatible.len());
    println!("rational bad triples tested: {rational_triples}");
    println!("normalized five-cores: {}", normalized.len());
    println!(
        "zero-edge exactly-3-bad compact C-B residuals: {}",
        bank.len()
    );

    let mut failures = 0u64;
    for dd in &bank {
        let (margin, den, m) = tower_margin(dd);
        if margin <= 0 {
            failures += 1;
        }
        println!("  member D={dd:?}, worst tower margin={margin}/{den} at m={m}");
    }
    println!("tower failures: {failures}");
    assert_eq!(failures, 0);
    println!("RESULT: ALL PASS");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_bank_members_are_exact_and_tower_positive() {
        let bank = parse_bank(include_str!("../bank4.csv"));
        assert_eq!(bank.len(), 4);
        for dd in bank {
            assert!(is_zero_edge_residual(&dd), "invalid fixture member: {dd:?}");
            let (margin, _, _) = tower_margin(&dd);
            assert!(margin > 0, "nonpositive tower margin: {dd:?}");
        }
    }
}
