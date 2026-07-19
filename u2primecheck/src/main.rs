const PRIMES: [i128; 4] = [2, 3, 5, 7];

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn lcm(a: i128, b: i128) -> i128 {
    a / gcd(a, b) * b
}

#[derive(Clone, Copy)]
struct Scan {
    period: i128,
    worst_slack: i128,
    worst_j: i128,
    slope_slack: i128,
}

fn scan(ms: [i128; 4]) -> Scan {
    let period = ms.into_iter().fold(1, lcm);
    let mut f60 = 0i128;
    let mut worst_slack = 70i128;
    let mut worst_j = 0i128;

    for j in 1..=period {
        let covered = ms.into_iter().filter(|m| j % m == 0).count() as i128;
        f60 += 60 / (1 + covered) - 30;

        // U2 prefix line: 7*j - 70 <= 300*f(j) = 5*(60*f(j)).
        let slack = 5 * f60 - (7 * j - 70);
        assert!(
            slack >= 0,
            "prefix failure at {:?}, period {}, j {}, slack {}",
            ms, period, j, slack
        );
        if slack < worst_slack {
            worst_slack = slack;
            worst_j = j;
        }
    }

    // One full period must advance by at least the target slope.
    let slope_slack = 5 * f60 - 7 * period;
    assert!(
        slope_slack >= 0,
        "period-slope failure at {:?}, period {}, slack {}",
        ms, period, slope_slack
    );

    Scan { period, worst_slack, worst_j, slope_slack }
}

fn main() {
    let mut ordered = 0u64;
    let mut unordered = 0u64;
    let mut global = (i128::MAX, [0i128; 4], 0i128, 0i128, 0i128);

    for &a in &PRIMES {
        for &b in &PRIMES {
            for &c in &PRIMES {
                for &d in &PRIMES {
                    let ms = [a, b, c, d];
                    let out = scan(ms);
                    ordered += 1;
                    if out.worst_slack < global.0 {
                        global = (out.worst_slack, ms, out.worst_j, out.period, out.slope_slack);
                    }
                }
            }
        }
    }

    for i in 0..PRIMES.len() {
        for j in i..PRIMES.len() {
            for k in j..PRIMES.len() {
                for l in k..PRIMES.len() {
                    scan([PRIMES[i], PRIMES[j], PRIMES[k], PRIMES[l]]);
                    unordered += 1;
                }
            }
        }
    }

    assert_eq!(ordered, 256);
    assert_eq!(unordered, 35);
    println!("U2 PRIME PERIOD CERTIFICATE: PASS");
    println!("ordered tuples checked: {ordered}");
    println!("unordered multisets checked: {unordered}");
    println!(
        "global minimum prefix slack: {} at {:?}, J={}, period={}, period-slope slack={}",
        global.0, global.1, global.2, global.3, global.4
    );
}
