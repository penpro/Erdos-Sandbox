use std::collections::BTreeSet;

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

fn is_one_edge_residual(dd: &[i128; 5]) -> bool {
    if dd[4] >= 7 * dd[0] || !is_antichain(dd) {
        return false;
    }
    if dd.iter().fold(0, |g, &d| gcd(g, d)) != 1 {
        return false;
    }

    let bad = bad_indices(dd);
    if bad.len() != 3 || induced_strong_edges(dd, &bad) != 1 {
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

fn tower_margin(dd: &[i128; 5]) -> Result<(i128, i128, i128), String> {
    let mut l = 1i128;
    for &d in dd {
        l = lcm(l, d);
    }
    let mut p: Vec<_> = dd.iter().map(|&d| l / d).collect();
    p.sort_unstable();

    let mut prod = 1i128;
    for &a in &p {
        prod = prod
            .checked_mul(a)
            .ok_or_else(|| format!("product overflow for D={dd:?}"))?;
    }
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
    Ok((worst, prod, worst_m))
}

fn main() {
    let mut raw = 0u64;
    let mut bank = BTreeSet::new();

    for alpha in 2..=27i128 {
        for alpha2 in (alpha + 1)..=27i128 {
            if gcd(alpha, alpha2) != 1 || alpha.min(alpha2) > 4 {
                continue;
            }
            if alpha.max(alpha2) >= 7 * alpha.min(alpha2) {
                continue;
            }

            for c1 in 2..=3i128 {
                for c2 in c1..=10i128 {
                    if 5 * (c1 + c2) < 3 * c1 * c2 {
                        continue;
                    }
                    let l = lcm(c1, c2);
                    for k1 in 2..(7 * c1) {
                        if gcd(k1, c1) != 1 {
                            continue;
                        }
                        for k2 in 2..(7 * c2) {
                            if gcd(k2, c2) != 1 {
                                continue;
                            }
                            let beta1 = l * k1 / c1;
                            let beta2 = l * k2 / c2;
                            if beta1 == beta2 || beta1 == l || beta2 == l {
                                continue;
                            }
                            let beta_sum = l + beta1 + beta2;
                            let u_max_1 = beta_sum * alpha / (alpha - 1);
                            let u_max_2 = beta_sum * alpha2 / (alpha2 - 1);
                            let u_max = u_max_1.min(u_max_2);

                            for u in 1..=u_max {
                                let spread_v_max = (7 * u * alpha.min(alpha2) - 1) / l;
                                let c_den = c1 * c2 - c1 - c2;
                                let row_v_max = if c_den > 0 {
                                    (alpha + alpha2) * c1 * c2 / c_den
                                } else {
                                    spread_v_max
                                };
                                let v_max = spread_v_max.min(row_v_max);
                                for v in 1..=v_max {
                                    raw += 1;
                                    let mut dd =
                                        [u * alpha, u * alpha2, v * l, v * beta1, v * beta2];
                                    dd.sort_unstable();
                                    if is_one_edge_residual(&dd) {
                                        bank.insert(dd);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let expected = parse_bank(include_str!("../bank19.csv"));
    assert_eq!(bank, expected, "generated bank differs from bank19.csv");

    println!("=== corrected one-edge finite bank ===");
    println!("raw parameter tuples: {raw}");
    println!(
        "one-edge exactly-3-bad compact C-B residuals: {}",
        bank.len()
    );

    let mut failures = 0u64;
    let mut worst: Option<(i128, i128, i128, [i128; 5])> = None;
    for dd in &bank {
        let (margin, den, m) = tower_margin(dd).unwrap_or_else(|e| panic!("{e}"));
        if margin <= 0 {
            failures += 1;
        }
        if worst
            .as_ref()
            .map(|(old, old_den, _, _)| margin * old_den < *old * den)
            .unwrap_or(true)
        {
            worst = Some((margin, den, m, *dd));
        }
        println!("  member D={dd:?}");
    }

    println!("tower failures: {failures}");
    if let Some((margin, den, m, dd)) = worst {
        println!(
            "worst margin = {margin}/{den} ~ {:.6} at m={m}, D={dd:?}",
            margin as f64 / den as f64
        );
    }
    assert_eq!(failures, 0);
    println!("RESULT: ALL PASS");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_bank_members_are_exact_and_tower_positive() {
        let bank = parse_bank(include_str!("../bank19.csv"));
        assert_eq!(bank.len(), 19);
        assert!(bank.contains(&[30, 52, 78, 130, 195]));
        for dd in bank {
            assert!(is_one_edge_residual(&dd), "invalid fixture member: {dd:?}");
            let (margin, _, _) = tower_margin(&dd).expect("tower arithmetic overflow");
            assert!(margin > 0, "nonpositive tower margin: {dd:?}");
        }
    }
}
