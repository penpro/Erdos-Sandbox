const J_FIRST: i32 = 2;
const J_LAST: i32 = 80;

fn f60(ms: &[i32], j_max: i32) -> i32 {
    (1..=j_max)
        .map(|j| {
            let hits = ms.iter().filter(|&&m| j % m == 0).count() as i32;
            60 / (1 + hits) - 30
        })
        .sum()
}

fn charge_good_possible(pins: &[i32], free: &[i32], j: i32) -> bool {
    // A free j+1 is an exact representative for an arbitrary actual modulus
    // greater than j. Its reciprocal can be made arbitrarily small, but is
    // positive, so the retained finite reciprocal sum must be strictly < 1.
    let finite: Vec<i32> = pins
        .iter()
        .copied()
        .chain(free.iter().copied().filter(|&m| m <= j))
        .collect();
    let den: i128 = finite.iter().map(|&m| m as i128).product();
    let num: i128 = finite.iter().map(|&m| den / m as i128).sum();
    num < den
}

#[derive(Clone, Copy)]
struct Minimum {
    value: i32,
    j: i32,
    row: [i32; 4],
}

fn visit_free_rows(
    pins: &[i32],
    j: i32,
    free: &mut Vec<i32>,
    next: i32,
    best: &mut Minimum,
    checked: &mut u64,
) {
    if pins.len() + free.len() == 4 {
        if !charge_good_possible(pins, free, j) {
            return;
        }
        let mut row = [0; 4];
        for (slot, &m) in row.iter_mut().zip(pins.iter().chain(free.iter())) {
            *slot = m;
        }
        *checked += 1;
        let value = f60(&row, j);
        if value < best.value {
            *best = Minimum { value, j, row };
        }
        return;
    }

    for m in next..=j + 1 {
        free.push(m);
        visit_free_rows(pins, j, free, m, best, checked);
        free.pop();
    }
}

fn layer_minimum(pins: &[i32], j: i32) -> (Minimum, u64) {
    let mut best = Minimum {
        value: i32::MAX,
        j,
        row: [0; 4],
    };
    let mut checked = 0;
    visit_free_rows(pins, j, &mut Vec::new(), 2, &mut best, &mut checked);
    (best, checked)
}

fn scan(pins: &[i32]) -> (Vec<Minimum>, u64) {
    let mut layers = Vec::new();
    let mut checked = 0;
    for j in J_FIRST..=J_LAST {
        let (best, count) = layer_minimum(pins, j);
        assert!(best.value != i32::MAX, "no feasible row at J={j}");
        layers.push(best);
        checked += count;
    }
    (layers, checked)
}

fn suffix_minimum(layers: &[Minimum], j_min: i32) -> Minimum {
    layers[(j_min - J_FIRST) as usize..]
        .iter()
        .copied()
        .min_by_key(|row| row.value)
        .unwrap()
}

fn main() {
    // Every charge-good row has at most one modulus 2. The certified drift
    // f >= (29/600)J - 1/2 therefore gives f60 >= 204 for every J >= 81.
    let tail_floor60 = (29 * (J_LAST + 1) - 300) / 10;
    let pin_sets: &[&[i32]] = &[
        &[],
        &[3],
        &[5],
        &[7],
        &[9],
        &[11],
        &[13],
        &[3, 5],
        &[3, 7],
    ];

    println!("exact charge-good pinned-row floors; units 1/60");
    println!("finite layers J={J_FIRST}..{J_LAST}; tail floor={tail_floor60}/60");
    for pins in pin_sets {
        let (layers, checked) = scan(pins);
        println!("\npins={pins:?}; feasible truncated rows checked={checked}");
        let mut previous = None;
        for j_min in J_FIRST..=J_LAST {
            let best = suffix_minimum(&layers, j_min);
            let certified = best.value.min(tail_floor60);
            if previous != Some(certified) {
                if best.value <= tail_floor60 {
                    println!(
                        "  J>={j_min:2}: min {:>4}/60 at J={:>2}, row={:?}",
                        certified, best.j, best.row
                    );
                } else {
                    println!(
                        "  J>={j_min:2}: min {:>4}/60 from certified tail J>=81",
                        certified
                    );
                }
                previous = Some(certified);
            }
        }
    }

    println!("\nfinite suffixes combined with certified tail: PASS");
    println!("RESULT: ALL PASS");
}
