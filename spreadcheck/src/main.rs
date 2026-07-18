fn f60(ms: &[i32; 4], j_max: i32) -> i32 {
    let mut total = 0;
    for j in 1..=j_max {
        let x = ms.iter().filter(|&&m| j % m == 0).count() as i32;
        total += 60 / (1 + x) - 30;
    }
    total
}

fn scan_class(name: &str, j_first: i32, j_last: i32, max_twos: usize, claim60: i32) -> bool {
    let mut checked = 0u64;
    let mut best = (i32::MAX, [0; 4], 0);
    let mut ok = true;

    for j in j_first..=j_last {
        // Every modulus greater than j has the same empty divisibility pattern
        // on [1,j], so j+1 is an exact stand-in for the unbounded tail.
        for a in 2..=j + 1 {
            for b in a..=j + 1 {
                for c in b..=j + 1 {
                    for d in c..=j + 1 {
                        let ms = [a, b, c, d];
                        if ms.iter().filter(|&&m| m == 2).count() > max_twos {
                            continue;
                        }
                        checked += 1;
                        let value = f60(&ms, j);
                        if value < best.0 {
                            best = (value, ms, j);
                        }
                        if value < claim60 {
                            ok = false;
                        }
                    }
                }
            }
        }
    }

    println!(
        "{name}: checked={checked}, min f60={} at {:?}, J={}, claim f60>={}: {}",
        best.0,
        best.1,
        best.2,
        claim60,
        if ok { "PASS" } else { "FAIL" }
    );
    ok
}

fn scan_no2_with_large_modulus(
    j_first: i32,
    j_last: i32,
    large_min: i32,
    claim60: i32,
) -> (bool, u64, i32, [i32; 4], i32) {
    let mut checked = 0u64;
    let mut best = (i32::MAX, [0; 4], 0);
    let mut ok = true;

    for j in j_first..=j_last {
        for a in 3..=j + 1 {
            for b in a..=j + 1 {
                for c in b..=j + 1 {
                    for d in c..=j + 1 {
                        if d < large_min {
                            continue;
                        }
                        checked += 1;
                        let ms = [a, b, c, d];
                        let value = f60(&ms, j);
                        if value < best.0 {
                            best = (value, ms, j);
                        }
                        if value < claim60 {
                            ok = false;
                        }
                    }
                }
            }
        }
    }

    (ok, checked, best.0, best.1, best.2)
}

fn gcd_i32(mut a: i32, mut b: i32) -> i32 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn exact_max_modulus_possible(m: i32, j: i32, rho2: i32) -> bool {
    (2..m).any(|k| gcd_i32(m, k) == 1 && 2 * m >= rho2 * k && m < 8 * k && 2 * m < (j + 1) * k)
}

fn scan_ratio_band(rho2: i32, claim60: i32) -> (bool, u64, i32, [i32; 4], i32) {
    let mut checked = 0u64;
    let mut best = (i32::MAX, [0; 4], 0);
    let mut ok = true;

    for j in rho2.max(2)..=21 {
        for a in 3..=j + 1 {
            for b in a..=j + 1 {
                for c in b..=j + 1 {
                    for d in c..=j + 1 {
                        let ms = [a, b, c, d];
                        let has_max_friend = ms
                            .iter()
                            .any(|&m| m == j + 1 || exact_max_modulus_possible(m, j, rho2));
                        if !has_max_friend {
                            continue;
                        }
                        checked += 1;
                        let value = f60(&ms, j);
                        if value < best.0 {
                            best = (value, ms, j);
                        }
                        if value < claim60 {
                            ok = false;
                        }
                    }
                }
            }
        }
    }

    (ok, checked, best.0, best.1, best.2)
}

fn charge_good_representative(ms: &[i32; 4], j: i32) -> bool {
    let tail = j + 1;
    let den: i128 = ms
        .iter()
        .filter(|&&m| m < tail)
        .map(|&m| m as i128)
        .product();
    let num: i128 = ms
        .iter()
        .filter(|&&m| m < tail)
        .map(|&m| den / m as i128)
        .sum();
    num < den
}

fn scan_charge_good(j_first: i32, j_last: i32) -> (u64, i32, [i32; 4], i32) {
    let mut checked = 0u64;
    let mut best = (i32::MAX, [0; 4], 0);

    for j in j_first..=j_last {
        for a in 2..=j + 1 {
            for b in a..=j + 1 {
                for c in b..=j + 1 {
                    for d in c..=j + 1 {
                        let ms = [a, b, c, d];
                        if !charge_good_representative(&ms, j) {
                            continue;
                        }
                        checked += 1;
                        let value = f60(&ms, j);
                        if value < best.0 {
                            best = (value, ms, j);
                        }
                    }
                }
            }
        }
    }

    (checked, best.0, best.1, best.2)
}

fn main() {
    let mut ok = true;

    // census drift proves f >= (7/300)J - 7/30 for the free class.
    // At J=7 this is -7/100 > -1/12, and the slope is positive.
    let free_takeover = 12 * (7 * 7 - 70) >= -300; // denominator 300 vs 12
    println!(
        "free drift takeover at J=7: {}",
        if free_takeover { "PASS" } else { "FAIL" }
    );
    ok &= free_takeover;
    ok &= scan_class("free small-J", 2, 6, 4, -5); // -1/12 * 60

    // census drift proves f >= (29/600)J - 1/2 for the <=one-2 class.
    // At J=13 this is 77/600 > 1/12, again with positive slope.
    let le1_takeover = 12 * (29 * 13 - 300) >= 600;
    println!(
        "<=one-2 drift takeover at J=13: {}",
        if le1_takeover { "PASS" } else { "FAIL" }
    );
    ok &= le1_takeover;
    ok &= scan_class("<=one-2 small-J", 2, 12, 1, 5); // 1/12 * 60

    // The no-2 linear drift is already >= 8/3 at J=25. Check the only
    // remaining layers needed to make that floor universal for J>=22.
    let no2_takeover = 457 * 25 - 1440 >= 9600;
    println!(
        "no-2 drift takeover at J=25: {}",
        if no2_takeover { "PASS" } else { "FAIL" }
    );
    ok &= no2_takeover;
    ok &= scan_class("no-2 J=21 barrier", 21, 21, 0, 140); // 7/3 * 60
    ok &= scan_class("no-2 J=22..24", 22, 24, 0, 160); // 8/3 * 60
    ok &= scan_class("free max-row J=2..3", 2, 3, 4, 10); // 1/6 * 60

    // Charge < 1 permits at most one modulus 2. The <=one-2 drift line is
    // at least 1/2 from J=21 onward; scan the finite prefix exactly.
    let good_takeover = 29 * 21 - 300 >= 300;
    println!(
        "charge-good drift takeover at J=21: {}",
        if good_takeover { "PASS" } else { "FAIL" }
    );
    ok &= good_takeover;
    let (good_checked, good_min60, good_ms, good_j) = scan_charge_good(2, 20);
    let good_small = good_min60 >= 30;
    println!(
        "charge-good rows J=2..20: checked={good_checked}, min f60={good_min60} at {:?}, J={good_j}, claim f60>=30: {}",
        good_ms,
        if good_small { "PASS" } else { "FAIL" }
    );
    ok &= good_small;

    for (name, j_first, j_last, claim60, takeover_j) in [
        ("J>=6", 6, 27, 50, 28),
        ("J>=12", 12, 34, 70, 35),
        ("J>=15", 15, 41, 90, 42),
    ] {
        let takeover = 29 * takeover_j - 300 >= 10 * claim60;
        let (checked, min60, ms, j) = scan_charge_good(j_first, j_last);
        let finite = min60 >= claim60;
        println!(
            "charge-good {name}: finite J={j_first}..{j_last} checked={checked}, min f60={min60} at {:?}, J={j}; drift takeover J={takeover_j}; claim f60>={claim60}: {}",
            ms,
            if finite && takeover { "PASS" } else { "FAIL" }
        );
        ok &= finite && takeover;
    }

    println!("[largest-element modulus constraint]");
    for large_min in 17..=22 {
        let j_first = (large_min - 1).max(2);
        let (pass, checked, min60, ms, j) =
            scan_no2_with_large_modulus(j_first, 21, large_min, 160);
        println!(
            "large modulus >= {large_min}, J={j_first}..21: checked={checked}, min f60={min60} at {:?}, J={j}: {}",
            ms,
            if pass { "PASS" } else { "FAIL" }
        );
        ok &= pass;
    }

    println!("[exact coprime ratio bands below 8]");
    for (rho2, claim60) in [(13, 110), (14, 155)] {
        let (pass, checked, min60, ms, j) = scan_ratio_band(rho2, claim60);
        println!(
            "rho >= {rho2}/2: checked={checked}, min f60={min60} at {:?}, J={j}: {}",
            ms,
            if pass { "PASS" } else { "FAIL" }
        );
        ok &= pass;
    }
    // With f_no2 >= 8/3, f_le1 >= 1/12, and three free floors >= -1/12,
    // the total constant is exactly zero before the retained positive +S.
    let spread_step = 2 * 160 + 2 * 5 + 6 * -5 - 5 * 60 == 0;
    println!(
        "spread step: J1>=22 gives constant 0 plus S: {}",
        if spread_step { "PASS" } else { "FAIL" }
    );
    ok &= spread_step;

    let spread7_step = 2 * (155 + 5 - 5 - 5 + 10) - 5 * 60 == 20;
    println!(
        "spread step: 7<=rho<8 gives 20/60 plus S: {}",
        if spread7_step { "PASS" } else { "FAIL" }
    );
    ok &= spread7_step;

    println!(
        "RESULT: {}",
        if ok { "ALL PASS" } else { "FAILURES PRESENT" }
    );
    if !ok {
        std::process::exit(1);
    }
}
