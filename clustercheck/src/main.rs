fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn main() {
    let mut total = 0u64;
    let mut old_max_connected = 0u64;
    let mut needs_small_owner = 0u64;
    let mut largest_owns_inside_count = 0u64;
    let mut forced_outside_hist = [0u64; 4];
    let mut internal_forced_outside_hist = [0u64; 4];
    let mut all_three_own_inside = 0u64;
    let mut some_owner_outside_needed = 0u64;
    let mut by_min = [0u64; 112];
    let mut digest = 0u128;
    let mut sealed_internal_shapes = Vec::new();
    let mut first_missed = Vec::new();
    let mut all_internal_shapes = Vec::new();
    let mut all_shapes = Vec::new();

    for a in 2i64..=111 {
        for b in (a + 1)..=(7 * a - 2) {
            for c in (b + 1)..=(7 * a - 1) {
                if gcd(gcd(a, b), c) != 1 {
                    continue;
                }
                if b % a == 0 || c % a == 0 || c % b == 0 {
                    continue;
                }

                let gab = gcd(a, b);
                let gac = gcd(a, c);
                let gbc = gcd(b, c);
                let min_edges = [4 * gab >= a, 4 * gac >= a, 4 * gbc >= b];
                if min_edges.iter().filter(|&&x| x).count() < 2 {
                    continue;
                }

                let max_edges = [4 * gab >= b, 4 * gac >= c, 4 * gbc >= c];
                let old = max_edges.iter().filter(|&&x| x).count() >= 2;
                let owner_has_internal = [
                    min_edges[0] || min_edges[1],
                    max_edges[0] || min_edges[2],
                    max_edges[1] || max_edges[2],
                ];
                let internal_gcd_sums = [gab + gac, gab + gbc, gac + gbc];
                // If a source x has no strong outside edge, each of the two
                // outside gcds is at most x/5: x/gcd is an integer greater
                // than 4. Thus an internal sum below 3x/5 forces another
                // strong outside owner edge whenever x is bad, independently
                // of the common scale.
                let bad_forces_outside = [
                    !owner_has_internal[0] || 5 * internal_gcd_sums[0] < 3 * a,
                    !owner_has_internal[1] || 5 * internal_gcd_sums[1] < 3 * b,
                    !owner_has_internal[2] || 5 * internal_gcd_sums[2] < 3 * c,
                ];
                let forced_count = bad_forces_outside.iter().filter(|&&x| x).count();
                let largest_owns_inside = owner_has_internal[2];

                total += 1;
                all_shapes.push((a, b, c));
                by_min[a as usize] += 1;
                forced_outside_hist[forced_count] += 1;
                digest = digest
                    .wrapping_mul(0x100000001b3)
                    .wrapping_add((a as u128) << 32 | (b as u128) << 16 | c as u128);

                if old {
                    old_max_connected += 1;
                } else {
                    needs_small_owner += 1;
                    if first_missed.len() < 30 {
                        first_missed.push((a, b, c, min_edges, max_edges));
                    }
                }
                if largest_owns_inside {
                    largest_owns_inside_count += 1;
                }
                if owner_has_internal.iter().all(|&x| x) {
                    all_three_own_inside += 1;
                    all_internal_shapes.push((a, b, c));
                    internal_forced_outside_hist[forced_count] += 1;
                    if forced_count == 0 {
                        sealed_internal_shapes.push((a, b, c));
                    }
                } else {
                    some_owner_outside_needed += 1;
                }
            }
        }
    }

    let documented_shapes: Vec<(i64, i64, i64)> = include_str!("../shapes69.csv")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let mut values = line.split(',').map(|value| value.parse::<i64>().unwrap());
            let row = (
                values.next().unwrap(),
                values.next().unwrap(),
                values.next().unwrap(),
            );
            assert!(values.next().is_none());
            row
        })
        .collect();
    let documented_all_shapes: Vec<(i64, i64, i64)> = include_str!("../shapes906.csv")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let mut values = line.split(',').map(|value| value.parse::<i64>().unwrap());
            let row = (
                values.next().unwrap(),
                values.next().unwrap(),
                values.next().unwrap(),
            );
            assert!(values.next().is_none());
            row
        })
        .collect();
    let args: Vec<String> = std::env::args().collect();
    if let Some(path) = args.get(1) {
        let mut csv = String::new();
        for &(a, b, c) in &all_shapes {
            csv.push_str(&format!("{a},{b},{c}\n"));
        }
        std::fs::write(path, csv).expect("write full 906-shape CSV");
        println!(
            "wrote {} exhaustive min-strong shapes to {}",
            all_shapes.len(),
            path
        );
    }
    let exact = total == 906
        && old_max_connected == 4
        && needs_small_owner == 902
        && largest_owns_inside_count == 71
        && all_three_own_inside == 69
        && some_owner_outside_needed == 837
        && forced_outside_hist == [0, 20, 258, 628]
        && internal_forced_outside_hist == [0, 6, 17, 46]
        && sealed_internal_shapes.is_empty()
        && documented_shapes == all_internal_shapes
        && documented_all_shapes == all_shapes
        && digest == 0xacecafc73c9c3ea4f2ca565f56bb5111;
    println!("ratio<7 normalized antichain triples with >=2 min-strong edges: {total}");
    println!("old >=2 max-strong subset: {old_max_connected}");
    println!("missed by old generator: {needs_small_owner}");
    println!("largest can own an internal edge: {largest_owns_inside_count}");
    println!("all three can own internal edges: {all_three_own_inside}");
    println!(
        "some vertex needs an outside owner edge if all three are bad: {some_owner_outside_needed}"
    );
    println!(
        "all 906 by vertices forced outside from owner/deficit: {:?}",
        forced_outside_hist
    );
    println!(
        "69 internal-owner shapes by additional deficit-forced vertices: {:?}",
        internal_forced_outside_hist
    );
    println!(
        "sealed internal shapes (no outside strong edge forced): {}",
        sealed_internal_shapes.len()
    );
    println!("digest: {digest:032x}");
    println!("first missed shapes (min-edge bits; max-edge bits):");
    for row in first_missed {
        println!("  {:?}", row);
    }
    println!("all-internal-owner shapes:");
    for chunk in all_internal_shapes.chunks(8) {
        println!("  {:?}", chunk);
    }
    println!("sealed all-internal-owner shapes:");
    for chunk in sealed_internal_shapes.chunks(8) {
        println!("  {:?}", chunk);
    }

    println!("nonzero counts by minimum coefficient:");
    for (a, &count) in by_min.iter().enumerate() {
        if count != 0 {
            println!("  a={a}: {count}");
        }
    }
    println!(
        "RESULT: {}",
        if exact {
            "ALL PASS"
        } else {
            "FAILURES PRESENT"
        }
    );
    if !exact {
        std::process::exit(1);
    }
}
