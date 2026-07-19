import Ep488.DriftKernelReduction

/-!
# U2 retirement reduction

This module formalizes the last `m >= 11` peel in the U2 chain. Under the
sorted-multiset convention, the four-modulus line follows from the
three-modulus line unless all four entries lie in the terminal `[2,10]` box.
The latter is discharged by `U2PrimePeriodKernel`.
-/

namespace Erdos488

def u2Count3 (m1 m2 m3 j : ℕ) : ℕ :=
  (if m1 ∣ j then 1 else 0) + (if m2 ∣ j then 1 else 0)
    + (if m3 ∣ j then 1 else 0)

def u2Term3 (m1 m2 m3 j : ℕ) : ℚ :=
  1 / (1 + u2Count3 m1 m2 m3 j : ℕ) - 1 / 2

def u2Drift3 (m1 m2 m3 J : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ioc 0 J, u2Term3 m1 m2 m3 j

/-- Adding one modulus decreases each summand by at most one half, and only
at a multiple of the added modulus. -/
lemma u2Term4_peel_last (m1 m2 m3 m4 j : ℕ) :
    u2Term3 m1 m2 m3 j - (if m4 ∣ j then (1 : ℚ) / 2 else 0)
      ≤ u2Term4 m1 m2 m3 m4 j := by
  by_cases h1 : m1 ∣ j <;> by_cases h2 : m2 ∣ j <;>
    by_cases h3 : m3 ∣ j <;> by_cases h4 : m4 ∣ j <;>
    norm_num [u2Term3, u2Count3, u2Term4, u2Count4, h1, h2, h3, h4]

/-- Exact floor-count form of the last-coordinate peel. -/
lemma u2Drift4_peel_floor (m1 m2 m3 m4 J : ℕ) :
    u2Drift3 m1 m2 m3 J - ((J / m4 : ℕ) : ℚ) / 2
      ≤ u2Drift4 m1 m2 m3 m4 J := by
  have hind :
      (∑ j ∈ Finset.Ioc 0 J, if m4 ∣ j then (1 : ℚ) / 2 else 0)
        = ((J / m4 : ℕ) : ℚ) / 2 := by
    calc
      (∑ j ∈ Finset.Ioc 0 J, if m4 ∣ j then (1 : ℚ) / 2 else 0)
          = ∑ j ∈ Finset.Ioc 0 J,
              (1 / 2 : ℚ) * (if m4 ∣ j then 1 else 0) := by
                refine Finset.sum_congr rfl (fun j _hj => ?_)
                by_cases h : m4 ∣ j <;> simp [h]
      _ = (1 / 2 : ℚ) *
            (∑ j ∈ Finset.Ioc 0 J, if m4 ∣ j then (1 : ℚ) else 0) := by
              rw [Finset.mul_sum]
      _ = ((J / m4 : ℕ) : ℚ) / 2 := by
              rw [← cast_div_eq_sum_indicator_q m4 J]
              ring
  have hsum :
      (∑ j ∈ Finset.Ioc 0 J,
          (u2Term3 m1 m2 m3 j - (if m4 ∣ j then (1 : ℚ) / 2 else 0)))
        ≤ ∑ j ∈ Finset.Ioc 0 J, u2Term4 m1 m2 m3 m4 j := by
    exact Finset.sum_le_sum (fun j _hj => u2Term4_peel_last m1 m2 m3 m4 j)
  rw [Finset.sum_sub_distrib, hind] at hsum
  simpa only [u2Drift3, u2Drift4] using hsum

lemma floor_cast_upper (n a : ℕ) (ha : 0 < a) :
    ((n / a : ℕ) : ℚ) ≤ (n : ℚ) / a := by
  have hdiv : (n : ℚ) = (a : ℚ) * (n / a : ℕ) + (n % a : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n a).symm
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  rw [hdiv]
  field_simp [ne_of_gt haQ]
  have hr : (0 : ℚ) ≤ (n % a : ℕ) := by positivity
  linarith

/-- Rational-slope form used by retirement: the added modulus costs at most
`J/(2m)`. -/
theorem u2Drift4_peel (m1 m2 m3 m4 J : ℕ) (h4 : 0 < m4) :
    u2Drift3 m1 m2 m3 J - (J : ℚ) / (2 * (m4 : ℚ))
      ≤ u2Drift4 m1 m2 m3 m4 J := by
  have hf := floor_cast_upper J m4 h4
  have hmQ : (0 : ℚ) < m4 := by exact_mod_cast h4
  have hscale : ((J / m4 : ℕ) : ℚ) / 2 ≤ (J : ℚ) / (2 * (m4 : ℚ)) := by
    calc
      ((J / m4 : ℕ) : ℚ) / 2 ≤ ((J : ℚ) / (m4 : ℚ)) / 2 := by linarith
      _ = (J : ℚ) / (2 * (m4 : ℚ)) := by field_simp [ne_of_gt hmQ]
  exact (sub_le_sub_left hscale (u2Drift3 m1 m2 m3 J)).trans
    (u2Drift4_peel_floor m1 m2 m3 m4 J)

/-- The three-modulus line in cleared form. The existing `census drift`
certificate proves this via its lower retirement chain. -/
def U2ThreeKernel : Prop :=
  ∀ m1 m2 m3 J : ℕ,
    2 ≤ m1 → 2 ≤ m2 → 2 ≤ m3 →
      5 * (J : ℚ) - 8 ≤ 72 * u2Drift3 m1 m2 m3 J

/-- For a sorted four-multiset, the `m4 >= 11` retirement plus the terminal
prime-period certificate proves the full four-modulus U2 line. -/
theorem u2_sorted4_of_threeKernel_and_primePeriod
    (hthree : U2ThreeKernel) (hperiod : U2PrimePeriodKernel)
    (m1 m2 m3 m4 J : ℕ)
    (h1lo : 2 ≤ m1) (h2lo : 2 ≤ m2) (h3lo : 2 ≤ m3)
    (h12 : m1 ≤ m2) (h23 : m2 ≤ m3) (h34 : m3 ≤ m4) :
    7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 J := by
  have h4lo : 2 ≤ m4 := h1lo.trans (h12.trans (h23.trans h34))
  by_cases hsmall : m4 ≤ 10
  · exact u2_terminal_box_of_primePeriodKernel hperiod m1 m2 m3 m4 J
      h1lo h2lo h3lo h4lo
      (h12.trans (h23.trans (h34.trans hsmall)))
      (h23.trans (h34.trans hsmall)) (h34.trans hsmall) hsmall
  · have h11 : 11 ≤ m4 := by omega
    have hmQ : (11 : ℚ) ≤ (m4 : ℚ) := by exact_mod_cast h11
    have hden : (22 : ℚ) ≤ 2 * (m4 : ℚ) := by linarith
    have hinv : (1 : ℚ) / (2 * (m4 : ℚ)) ≤ 1 / 22 :=
      one_div_le_one_div_of_le (by norm_num) hden
    have hJ : (0 : ℚ) ≤ (J : ℚ) := by positivity
    have hloss : (J : ℚ) / (2 * (m4 : ℚ)) ≤ (J : ℚ) / 22 := by
      calc
        (J : ℚ) / (2 * (m4 : ℚ))
            = (J : ℚ) * (1 / (2 * (m4 : ℚ))) := by ring
        _ ≤ (J : ℚ) * (1 / 22) := mul_le_mul_of_nonneg_left hinv hJ
        _ = (J : ℚ) / 22 := by ring
    have h3 := hthree m1 m2 m3 J h1lo h2lo h3lo
    have hp := u2Drift4_peel m1 m2 m3 m4 J (by omega)
    have hcompare :
        (7 * (J : ℚ) - 70) / 300
          ≤ (5 * (J : ℚ) - 8) / 72 - (J : ℚ) / 22 := by
      nlinarith
    nlinarith

end Erdos488
