use std::collections::BTreeSet;

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

fn valid_shape(w: &[i128; 4]) -> bool {
    for i in 0..4 {
        for j in (i + 1)..4 {
            if w[i] == w[j] || w[j] % w[i] == 0 {
                return false;
            }
        }
    }
    if gcd(gcd(w[0], w[1]), gcd(w[2], w[3])) != 1 || w[3] >= 7 * w[0] {
        return false;
    }
    for i in 0..4 {
        let mut den = 1;
        for j in 0..4 {
            if i != j {
                den *= w[j];
            }
        }
        let mut num = 0;
        for j in 0..4 {
            if i != j {
                num += gcd(w[i], w[j]) * (den / w[j]);
            }
        }
        if 2 * num < den {
            return false;
        }
    }
    true
}

fn heavy_edge(a: i128, b: i128) -> bool {
    let g = gcd(a, b);
    a / g <= 6 || b / g <= 6
}

fn heavy_connected(w: &[i128; 4]) -> bool {
    let mut seen = [false; 4];
    seen[0] = true;
    loop {
        let mut changed = false;
        for i in 0..4 {
            if !seen[i] {
                continue;
            }
            for j in 0..4 {
                if !seen[j] && heavy_edge(w[i], w[j]) {
                    seen[j] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    seen.iter().all(|&x| x)
}

fn canonical_shapes() -> BTreeSet<[i128; 4]> {
    include_str!("../../census/shapes4inv120.csv")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let values: Vec<i128> = line
                .split(',')
                .map(|value| value.parse::<i128>().unwrap())
                .collect();
            assert_eq!(values.len(), 4);
            [values[0], values[1], values[2], values[3]]
        })
        .collect()
}

fn prufer_tree(a: usize, b: usize) -> [(usize, usize); 3] {
    let sequence = [a, b];
    let mut degree = [1usize; 4];
    for &v in &sequence {
        degree[v] += 1;
    }
    let mut edges = [(0, 0); 3];
    for (slot, &v) in sequence.iter().enumerate() {
        let leaf = (0..4).find(|&i| degree[i] == 1).unwrap();
        edges[slot] = (leaf, v);
        degree[leaf] -= 1;
        degree[v] -= 1;
    }
    let leaves: Vec<usize> = (0..4).filter(|&i| degree[i] == 1).collect();
    edges[2] = (leaves[0], leaves[1]);
    edges
}

fn reduced_fraction(num: i128, den: i128) -> (i128, i128) {
    let g = gcd(num, den);
    (num / g, den / g)
}

fn shape_from_tree(edges: &[(usize, usize); 3], ratios: &[(i128, i128); 3]) -> [i128; 4] {
    // For edge (u,v) with ratio (a,b), x_u/x_v=a/b.
    let mut value: [Option<(i128, i128)>; 4] = [None; 4];
    value[0] = Some((1, 1));
    while value.iter().any(Option::is_none) {
        let mut changed = false;
        for (edge, &(a, b)) in edges.iter().zip(ratios.iter()) {
            let (u, v) = *edge;
            match (value[u], value[v]) {
                (Some((num, den)), None) => {
                    value[v] = Some(reduced_fraction(num * b, den * a));
                    changed = true;
                }
                (None, Some((num, den))) => {
                    value[u] = Some(reduced_fraction(num * a, den * b));
                    changed = true;
                }
                _ => {}
            }
        }
        assert!(changed);
    }

    let common_den = value.iter().map(|entry| entry.unwrap().1).fold(1, lcm);
    let mut w = [0; 4];
    for (slot, entry) in w.iter_mut().zip(value.iter()) {
        let (num, den) = entry.unwrap();
        *slot = num * (common_den / den);
    }
    let common_gcd = gcd(gcd(w[0], w[1]), gcd(w[2], w[3]));
    for x in &mut w {
        *x /= common_gcd;
    }
    w.sort_unstable();
    w
}

fn connected_shapes() -> BTreeSet<[i128; 4]> {
    let mut types = Vec::new();
    for a in 2..=41i128 {
        for b in 2..=41i128 {
            if a != b && gcd(a, b) == 1 && (a <= 6 || b <= 6) && a < 7 * b && b < 7 * a {
                types.push((a, b));
            }
        }
    }

    let mut found = BTreeSet::new();
    for p0 in 0..4 {
        for p1 in 0..4 {
            let edges = prufer_tree(p0, p1);
            for &r0 in &types {
                for &r1 in &types {
                    for &r2 in &types {
                        let w = shape_from_tree(&edges, &[r0, r1, r2]);
                        if valid_shape(&w) {
                            found.insert(w);
                        }
                    }
                }
            }
        }
    }
    found
}

fn pair_box_shapes() -> BTreeSet<[i128; 4]> {
    let mut found = BTreeSet::new();
    for a in 2..=42i128 {
        for ap in 3..=42i128 {
            if gcd(a, ap) != 1 {
                continue;
            }
            for b in 2..=42i128 {
                for bp in 2..=42i128 {
                    if b == bp || gcd(b, bp) != 1 {
                        continue;
                    }
                    for m in 2..=12i128 {
                        for k in 2..=83i128 {
                            if gcd(k, m) != 1 || m >= 7 * k || k >= 7 * m {
                                continue;
                            }
                            let scale_gcd = gcd(k * b, m * a);
                            let ha = k * b / scale_gcd;
                            let hb = m * a / scale_gcd;
                            let chosen_a = ha * a;
                            let chosen_b = hb * b;
                            let pair_gcd = gcd(chosen_a, chosen_b);
                            if chosen_b != pair_gcd * m {
                                continue;
                            }
                            let mut w = [ha * a, ha * ap, hb * b, hb * bp];
                            w.sort_unstable();
                            if valid_shape(&w) {
                                found.insert(w);
                            }
                        }
                    }
                }
            }
        }
    }
    found
}

fn max_min(shapes: &BTreeSet<[i128; 4]>) -> i128 {
    shapes.iter().map(|w| w[0]).max().unwrap_or(0)
}

fn main() {
    let expected = canonical_shapes();
    assert_eq!(expected.len(), 174);
    assert!(expected.iter().all(valid_shape));

    let expected_connected: BTreeSet<_> =
        expected.iter().copied().filter(heavy_connected).collect();
    let expected_two_pair: BTreeSet<_> = expected
        .iter()
        .copied()
        .filter(|w| !heavy_connected(w))
        .collect();

    let tree = connected_shapes();
    let pair_box = pair_box_shapes();

    let tree_outside: Vec<_> = tree.difference(&expected).collect();
    let tree_missing: Vec<_> = expected_connected.difference(&tree).collect();
    let pair_outside: Vec<_> = pair_box.difference(&expected).collect();
    let pair_missing: Vec<_> = expected_two_pair.difference(&pair_box).collect();

    println!("canonical necessary-filter shapes: {}", expected.len());
    println!(
        "heavy-graph split: connected={}, two-pair={}",
        expected_connected.len(),
        expected_two_pair.len()
    );
    println!(
        "connected spanning-tree box: {} shapes, largest w1={}, outside={}, missing={}",
        tree.len(),
        max_min(&tree),
        tree_outside.len(),
        tree_missing.len()
    );
    println!(
        "two-pair scale box: {} shapes, largest w1={}, outside={}, missing-two-pair={}",
        pair_box.len(),
        max_min(&pair_box),
        pair_outside.len(),
        pair_missing.len()
    );

    let ok = tree == expected_connected
        && pair_outside.is_empty()
        && pair_missing.is_empty()
        && max_min(&tree) <= 40
        && max_min(&pair_box) <= 40;
    println!(
        "RESULT: {}",
        if ok { "ALL PASS" } else { "FAILURES PRESENT" }
    );
    if !ok {
        std::process::exit(1);
    }
}
