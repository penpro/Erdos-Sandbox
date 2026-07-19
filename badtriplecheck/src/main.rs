use std::collections::BTreeSet;
use std::env;
use std::fs;

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

fn induced_strong_edges(dd: &[i128; 5], bad: &[usize]) -> usize {
    let mut edges = 0;
    for u in 0..bad.len() {
        for v in (u + 1)..bad.len() {
            let (i, j) = (bad[u], bad[v]);
            if 4 * gcd(dd[i], dd[j]) >= dd[i].min(dd[j]) {
                edges += 1;
            }
        }
    }
    edges
}

fn normalized_bad_triple(dd: &[i128; 5], bad: &[usize; 3]) -> [i128; 3] {
    let g = gcd(gcd(dd[bad[0]], dd[bad[1]]), dd[bad[2]]);
    [dd[bad[0]] / g, dd[bad[1]] / g, dd[bad[2]] / g]
}

fn load_shapes(path: &str) -> BTreeSet<[i128; 3]> {
    fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {path}: {e}"))
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let values: Vec<_> = line
                .split(',')
                .map(|value| value.trim().parse::<i128>().expect("invalid shape value"))
                .collect();
            assert_eq!(values.len(), 3, "invalid shape row: {line}");
            [values[0], values[1], values[2]]
        })
        .collect()
}

#[derive(Default)]
struct WorkerResult {
    class_count: u64,
    residual_count: u64,
    self_bad_hist: [u64; 6],
    exactly_three: Vec<([i128; 5], [usize; 3], usize)>,
}

fn worker(m: i128, tid: i128, nthreads: i128) -> WorkerResult {
    let mut out = WorkerResult::default();
    let mut a = 2i128;
    while a <= m {
        if (a - 2) % nthreads != tid {
            a += 1;
            continue;
        }

        let cap_e = |partial: i128| (1135 * a - 7 * partial) / 7;
        for b in (a + 1)..=m.min((1135 * a - 7 * a) / (7 * 4)) {
            if b % a == 0 {
                continue;
            }
            let gab = gcd(a, b);
            for c in (b + 1)..=m.min((1135 * a - 7 * (a + b)) / (7 * 3)) {
                if c % a == 0 || c % b == 0 {
                    continue;
                }
                let gabc = gcd(gab, c);
                for d in (c + 1)..=m.min((1135 * a - 7 * (a + b + c)) / (7 * 2)) {
                    if d % a == 0 || d % b == 0 || d % c == 0 {
                        continue;
                    }
                    let gabcd = gcd(gabc, d);
                    for e in (d + 1)..=m.min(cap_e(a + b + c + d)) {
                        if e % a == 0 || e % b == 0 || e % c == 0 || e % d == 0 {
                            continue;
                        }
                        if gcd(gabcd, e) != 1 {
                            continue;
                        }

                        let dd = [a, b, c, d, e];
                        let bad = bad_indices(&dd);
                        if bad.len() < 3 {
                            continue;
                        }
                        out.class_count += 1;

                        let sum_d: i128 = dd.iter().sum();
                        let mut sum_gcd = 0i128;
                        for i in 0..5 {
                            for j in (i + 1)..5 {
                                sum_gcd += gcd(dd[i], dd[j]);
                            }
                        }
                        let crit_num = sum_d - 2 * sum_gcd;
                        if 2 * crit_num > 7 * dd[0] {
                            continue;
                        }

                        out.residual_count += 1;
                        out.self_bad_hist[bad.len()] += 1;
                        if bad.len() == 3 {
                            let bad3 = [bad[0], bad[1], bad[2]];
                            let edges = induced_strong_edges(&dd, &bad3);
                            out.exactly_three.push((dd, bad3, edges));
                        }
                    }
                }
            }
        }
        a += 1;
    }
    out
}

fn main() {
    let args: Vec<_> = env::args().collect();
    let m = args
        .get(1)
        .map(|s| s.parse::<i128>().expect("M must be an integer"))
        .unwrap_or(120);
    assert!(m >= 2);

    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get() as i128)
        .unwrap_or(4)
        .max(1);
    let parts = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..nthreads)
            .map(|tid| scope.spawn(move || worker(m, tid, nthreads)))
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("worker panicked"))
            .collect::<Vec<_>>()
    });

    let mut class_count = 0u64;
    let mut residual_count = 0u64;
    let mut self_bad_hist = [0u64; 6];
    let mut rows = Vec::new();
    for mut part in parts {
        class_count += part.class_count;
        residual_count += part.residual_count;
        for (dst, src) in self_bad_hist.iter_mut().zip(part.self_bad_hist) {
            *dst += src;
        }
        rows.append(&mut part.exactly_three);
    }
    rows.sort_unstable_by_key(|row| row.0);

    let mut edge_hist = [0u64; 4];
    for row in &rows {
        edge_hist[row.2] += 1;
    }

    println!("=== exact C-B bad-triple audit, dual entries <= {m} ===");
    println!("<=2-good window class: {class_count}");
    println!("C-B residual: {residual_count}");
    println!("self-bad histogram [0..5]: {self_bad_hist:?}");
    println!("exactly-3-bad induced strong edges [0,1,2,3]: {edge_hist:?}");

    if let Some(path) = args.get(2) {
        let shapes = load_shapes(path);
        let covered = rows
            .iter()
            .filter(|row| row.2 >= 2)
            .filter(|row| shapes.contains(&normalized_bad_triple(&row.0, &row.1)))
            .count();
        let expected = edge_hist[2] + edge_hist[3];
        println!(">=2-edge residual coverage by {path}: {covered}/{expected}");
        assert_eq!(covered as u64, expected);
    }

    for edge_count in 0..=1 {
        let shapes: BTreeSet<_> = rows
            .iter()
            .filter(|row| row.2 == edge_count)
            .map(|row| normalized_bad_triple(&row.0, &row.1))
            .collect();
        println!(
            "{edge_count}-edge normalized shapes ({}): {shapes:?}",
            shapes.len()
        );

        let examples: Vec<_> = rows
            .iter()
            .filter(|row| row.2 == edge_count)
            .take(20)
            .collect();
        println!("{edge_count}-edge witnesses: {}", examples.len());
        for (dd, bad, _) in examples {
            let row_sums: [i128; 5] = std::array::from_fn(|i| {
                (0..5).filter(|&j| j != i).map(|j| gcd(dd[i], dd[j])).sum()
            });
            let mut l = 1i128;
            for &d in dd {
                l = lcm(l, d);
            }
            let mut primal: Vec<_> = dd.iter().map(|&d| l / d).collect();
            primal.sort_unstable();
            println!("  D={dd:?} bad={bad:?} gcd-sums={row_sums:?} P={primal:?}");
        }
    }

    assert_eq!(rows.len() as u64, self_bad_hist[3]);
    println!("RESULT: ALL PASS");
}
