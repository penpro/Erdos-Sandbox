import Ep488.Certificate

/-!
# Worked example: EP488 for a size-4 primitive core, by certificate

`A = {4, 6, 10, 15}` is a `∣`-antichain of size 4 (the smallest-lcm primitive core
of size 4, `lcm = 60`), so it lies OUTSIDE the `|core| ≤ 3` theorem.  We certify
EP488 for it, sorry-free, purely by `ep488_of_window`: one period `L = 60`, the
density slopes `4·60 ≤ 12·B(60) ≤ 6·60`, and the ratio bounds on the single window
`[15, 75)` — all discharged by kernel `decide` (no `native_decide`, so the axiom
set stays `propext, Classical.choice, Quot.sound`).
-/

namespace Erdos488

/-- **EP488 holds for `A = {4,6,10,15}`** (a size-4 primitive core), for all
`m > n ≥ 15`.  Certified end-to-end via `ep488_of_window`. -/
theorem ep488_example_4_6_10_15 {n m : ℕ} (hn : 15 ≤ n) (hm : n < m) :
    n * (Bgen {4, 6, 10, 15} m).card < 2 * m * (Bgen {4, 6, 10, 15} n).card := by
  refine ep488_of_window (N := 15) (L := 60) (c := 4) (e := 6) (d := 12)
    (by norm_num) (by norm_num) (by decide) (by decide) (by decide) ?_ ?_ (by norm_num) hn hm
  · intro x h1 h2; interval_cases x <;> decide
  · intro x h1 h2; interval_cases x <;> decide

end Erdos488
