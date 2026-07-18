fn gcd(mut a: i32, mut b: i32) -> i32 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn f60(ms: &[i32; 4], j_max: i32) -> i32 {
    (1..=j_max)
        .map(|j| {
            let hits = ms.iter().filter(|&&m| j % m == 0).count() as i32;
            60 / (1 + hits) - 30
        })
        .sum()
}

fn reciprocal_sum_at_least_one(ms: &[i32; 4]) -> bool {
    let den: i128 = ms.iter().map(|&m| m as i128).product();
    let num: i128 = ms.iter().map(|&m| den / m as i128).sum();
    num >= den
}

fn good_charge_possible(pin: i32, others: &[i32; 3], j: i32) -> bool {
    // Truncated unpinned entries j+1 represent arbitrary actual values >j,
    // whose reciprocal contributions can be made arbitrarily small.
    let finite: Vec<i32> = std::iter::once(pin)
        .chain(others.iter().copied().filter(|&m| m <= j))
        .collect();
    let den: i128 = finite.iter().map(|&m| m as i128).product();
    let num: i128 = finite.iter().map(|&m| den / m as i128).sum();
    num < den
}

fn bad_min(pin: i32, j: i32) -> (i32, [i32; 4]) {
    let mut best = (i32::MAX, [0; 4]);
    for a in 2..=j + 1 {
        for b in a..=j + 1 {
            for c in b..=j + 1 {
                let ms = [pin, a, b, c];
                // For an unpinned tail entry, j+1 is the largest possible
                // reciprocal among actual values >j. Hence this is exactly
                // the feasibility test for charge >=1 in the relaxed row.
                if !reciprocal_sum_at_least_one(&ms) {
                    continue;
                }
                let value = f60(&ms, j);
                if value < best.0 {
                    best = (value, ms);
                }
            }
        }
    }
    best
}

fn good_min(pin: i32, j: i32) -> (i32, [i32; 4]) {
    let mut best = (i32::MAX, [0; 4]);
    for a in 2..=j + 1 {
        for b in a..=j + 1 {
            for c in b..=j + 1 {
                let others = [a, b, c];
                if !good_charge_possible(pin, &others, j) {
                    continue;
                }
                let ms = [pin, a, b, c];
                let value = f60(&ms, j);
                if value < best.0 {
                    best = (value, ms);
                }
            }
        }
    }
    best
}

fn coupled(j_bad: i32, j_good: i32, m: i32, q: i32) -> bool {
    // The half-open intervals for x in J_bad=floor(mx), J_good=floor(qx)
    // intersect exactly when both strict cross-inequalities hold.
    j_bad * q < (j_good + 1) * m && j_good * m < (j_bad + 1) * q
}

fn main() {
    const J_MAX: i32 = 80;
    let mut global = (i32::MAX, 0, 0, 0, 0, [0; 4], [0; 4]);
    let mut by_m = [(i32::MAX, 0, 0, 0, [0; 4], [0; 4]); 5];
    let mut pair_types = 0u64;
    let mut coupled_layers = 0u64;

    for m in 2..=4 {
        let bad: Vec<_> = (2..=J_MAX).map(|j| bad_min(m, j)).collect();
        for q in 2..7 * m {
            if gcd(m, q) != 1 {
                continue;
            }
            pair_types += 1;
            let good: Vec<_> = (2..=J_MAX).map(|j| good_min(q, j)).collect();
            for j_bad in 2..=J_MAX {
                for j_good in 2..=J_MAX {
                    if !coupled(j_bad, j_good, m, q) {
                        continue;
                    }
                    coupled_layers += 1;
                    let b = bad[(j_bad - 2) as usize];
                    let g = good[(j_good - 2) as usize];
                    if b.0 == i32::MAX || g.0 == i32::MAX {
                        continue;
                    }
                    let value = b.0 + g.0;
                    if value < global.0 {
                        global = (value, m, q, j_bad, j_good, b.1, g.1);
                    }
                    if value < by_m[m as usize].0 {
                        by_m[m as usize] = (value, q, j_bad, j_good, b.1, g.1);
                    }
                }
            }
        }
    }

    println!("pair types: {pair_types}; coupled layers through J={J_MAX}: {coupled_layers}");
    println!(
        "global min f_bad+f_good = {}/60 at m={}, q={}, J=({},{}), bad={:?}, good={:?}",
        global.0, global.1, global.2, global.3, global.4, global.5, global.6
    );
    for m in 2..=4 {
        let row = by_m[m as usize];
        println!(
            "m={m}: min {}/60 at q={}, J=({},{}), bad={:?}, good={:?}",
            row.0, row.1, row.2, row.3, row.4, row.5
        );
    }

    // For J_good>80, combine the certified good drift line with the
    // universal free floor -5/60. For J_bad>80, combine the free drift
    // line with the universal good floor 30/60. Integer division rounds
    // both positive drift bounds downward, so these are conservative.
    let good_tail60 = (29 * 81 - 300) / 10;
    let bad_tail60 = (7 * 81 - 70) / 5;
    let tail_floor60 = (good_tail60 - 5).min(bad_tail60 + 30);
    let expected = [(2, 40), (3, 25), (4, 35)];
    let finite_exact = pair_types == 32
        && coupled_layers == 2887
        && expected
            .iter()
            .all(|&(m, value)| by_m[m as usize].0 == value);
    let tail_safe = expected.iter().all(|&(_, value)| tail_floor60 >= value);
    println!(
        "finite minima and tail takeover (tail floor {tail_floor60}/60): {}",
        if finite_exact && tail_safe {
            "PASS"
        } else {
            "FAIL"
        }
    );
    println!(
        "RESULT: {}",
        if finite_exact && tail_safe {
            "ALL PASS"
        } else {
            "FAILURES PRESENT"
        }
    );
    if !finite_exact || !tail_safe {
        std::process::exit(1);
    }
}
