use std::env;

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.abs()
}

fn lcm(a: i128, b: i128) -> i128 {
    a / gcd(a, b) * b
}

fn primitive(p: &[i128; 5]) -> bool {
    for i in 0..5 {
        for j in (i + 1)..5 {
            if p[j] % p[i] == 0 {
                return false;
            }
        }
    }
    p.iter().copied().reduce(gcd) == Some(1)
}

fn good_count(p: &[i128; 5]) -> usize {
    (0..5)
        .filter(|&i| {
            let mut den = 1i128;
            for j in 0..5 {
                if i != j {
                    den *= p[j];
                }
            }
            let mut num = 0i128;
            for j in 0..5 {
                if i != j {
                    num += gcd(p[i], p[j]) * (den / p[j]);
                }
            }
            num < den
        })
        .count()
}

fn common_data(p: &[i128; 5]) -> (i128, i128) {
    let l = p.iter().copied().fold(1, lcm);
    let s_num: i128 = p.iter().map(|&a| l / a).sum();
    let pair_num: i128 = (0..5)
        .flat_map(|i| ((i + 1)..5).map(move |j| l / lcm(p[i], p[j])))
        .sum();
    (l, s_num - 2 * pair_num)
}

fn phi(p: &[i128; 5], n: i128) -> i128 {
    let singles: i128 = p.iter().map(|&a| n / a).sum();
    let pairs: i128 = (0..5)
        .flat_map(|i| ((i + 1)..5).map(move |j| n / lcm(p[i], p[j])))
        .sum();
    singles - 2 * pairs
}

fn b_count(p: &[i128; 5], n: i128) -> i128 {
    (1..=n).filter(|&x| p.iter().any(|&a| x % a == 0)).count() as i128
}

fn main() {
    let limit: i128 = env::args()
        .nth(1)
        .unwrap_or_else(|| "80".to_string())
        .parse()
        .expect("limit must be an integer");

    let mut class_count = 0u64;
    let mut crit_count = 0u64;
    let mut points = 0u64;
    let mut bound_fail: Option<([i128; 5], i128, i128, i128)> = None;
    let mut cover_fail: Option<([i128; 5], i128, i128)> = None;
    let mut separator_fail: Option<([i128; 5], i128, i128, i128)> = None;
    let mut worst_err = (i128::MAX, 1i128, [0i128; 5], 0i128);

    'sets: for a in 2..=limit {
        for b in (a + 1)..=limit {
            for c in (b + 1)..=limit {
                for d in (c + 1)..=limit {
                    for e in (d + 1)..=limit {
                        let p = [a, b, c, d, e];
                        if !primitive(&p) || good_count(&p) > 2 {
                            continue;
                        }
                        let (l, c_num) = common_data(&p);
                        let s_num: i128 = p.iter().map(|&x| l / x).sum();
                        if 7 * e * s_num > 1135 * l {
                            continue;
                        }
                        class_count += 1;
                        if 2 * e * c_num <= 7 * l {
                            continue;
                        }
                        crit_count += 1;

                        let bridge_rhs = 1135 * l - 157 * s_num;
                        let cap = bridge_rhs / (7 * s_num);
                        if 2 * e > cap {
                            continue;
                        }
                        for n in (2 * e)..=cap {
                            points += 1;
                            let ph = phi(&p, n);
                            let err_num = ph * l - n * c_num;
                            if worst_err.0 == i128::MAX || err_num * worst_err.1 < worst_err.0 * l {
                                worst_err = (err_num, l, p, n);
                            }
                            if err_num < -2 * l && bound_fail.is_none() {
                                bound_fail = Some((p, n, err_num, l));
                            }
                            if ph < 5 && cover_fail.is_none() {
                                cover_fail = Some((p, n, ph));
                            }
                            let bc = b_count(&p, n);
                            if 2 * bc * l <= n * s_num && separator_fail.is_none() {
                                separator_fail = Some((p, n, 2 * bc * l, n * s_num));
                            }
                            if bound_fail.is_some()
                                || cover_fail.is_some()
                                || separator_fail.is_some()
                            {
                                break 'sets;
                            }
                        }
                    }
                }
            }
        }
    }

    println!("limit={limit} class={class_count} crit>7/2={crit_count} points={points}");
    println!(
        "worst phi-nC = {}/{} at P={:?}, n={}",
        worst_err.0, worst_err.1, worst_err.2, worst_err.3
    );
    println!("bound failure: {bound_fail:?}");
    println!("cover failure: {cover_fail:?}");
    println!("separator failure: {separator_fail:?}");
}
