import Ep488.DriftBridge

/-!
# Finite U2 kernel reduction

This module checks the divisor-monotonicity step that reduces the terminal
four-modulus U2 box `[2,10]^4` to moduli in `{2,3,5,7}`. Thus the terminal
certificate needs only 35 multisets up to permutation, rather than 495
multisets from the full interval. The one-period prime-kernel checks remain
an explicit certificate hypothesis.
-/

namespace Erdos488

def IsU2SmallPrime (q : ℕ) : Prop :=
  q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7

/-- Every integer in the terminal box has a prime divisor in `{2,3,5,7}`. -/
lemma exists_smallPrime_dvd (m : ℕ) (hlo : 2 ≤ m) (hhi : m ≤ 10) :
    ∃ q, IsU2SmallPrime q ∧ q ∣ m := by
  interval_cases m <;> simp_all [IsU2SmallPrime]

/-- Replacing the first modulus by a divisor can only decrease the drift term. -/
lemma u2Term4_dvd_mono_first (q m b c d j : ℕ) (hqm : q ∣ m) :
    u2Term4 q b c d j ≤ u2Term4 m b c d j := by
  have himp (hm : m ∣ j) : q ∣ j := hqm.trans hm
  by_cases hq : q ∣ j
  · by_cases hm : m ∣ j
    · simp [u2Term4, u2Count4, hq, hm]
    · by_cases hb : b ∣ j <;> by_cases hc : c ∣ j <;>
        by_cases hd : d ∣ j <;>
        norm_num [u2Term4, u2Count4, hq, hm, hb, hc, hd]
  · have hm : ¬m ∣ j := by
      intro hm
      exact hq (himp hm)
    simp [u2Term4, u2Count4, hq, hm]

lemma u2Term4_dvd_mono_second (a q m c d j : ℕ) (hqm : q ∣ m) :
    u2Term4 a q c d j ≤ u2Term4 a m c d j := by
  simpa only [u2Term4, u2Count4, add_comm, add_left_comm, add_assoc] using
    u2Term4_dvd_mono_first q m a c d j hqm

lemma u2Term4_dvd_mono_third (a b q m d j : ℕ) (hqm : q ∣ m) :
    u2Term4 a b q d j ≤ u2Term4 a b m d j := by
  simpa only [u2Term4, u2Count4, add_comm, add_left_comm, add_assoc] using
    u2Term4_dvd_mono_first q m a b d j hqm

lemma u2Term4_dvd_mono_fourth (a b c q m j : ℕ) (hqm : q ∣ m) :
    u2Term4 a b c q j ≤ u2Term4 a b c m j := by
  simpa only [u2Term4, u2Count4, add_comm, add_left_comm, add_assoc] using
    u2Term4_dvd_mono_first q m a b c j hqm

lemma u2Drift4_dvd_mono_first (q m b c d J : ℕ) (hqm : q ∣ m) :
    u2Drift4 q b c d J ≤ u2Drift4 m b c d J := by
  apply Finset.sum_le_sum
  intro j _hj
  exact u2Term4_dvd_mono_first q m b c d j hqm

lemma u2Drift4_dvd_mono_second (a q m c d J : ℕ) (hqm : q ∣ m) :
    u2Drift4 a q c d J ≤ u2Drift4 a m c d J := by
  apply Finset.sum_le_sum
  intro j _hj
  exact u2Term4_dvd_mono_second a q m c d j hqm

lemma u2Drift4_dvd_mono_third (a b q m d J : ℕ) (hqm : q ∣ m) :
    u2Drift4 a b q d J ≤ u2Drift4 a b m d J := by
  apply Finset.sum_le_sum
  intro j _hj
  exact u2Term4_dvd_mono_third a b q m d j hqm

lemma u2Drift4_dvd_mono_fourth (a b c q m J : ℕ) (hqm : q ∣ m) :
    u2Drift4 a b c q J ≤ u2Drift4 a b c m J := by
  apply Finset.sum_le_sum
  intro j _hj
  exact u2Term4_dvd_mono_fourth a b c q m j hqm

/-- Coordinatewise divisor lowering can only decrease four-modulus drift. -/
theorem u2Drift4_dvd_mono (q1 q2 q3 q4 m1 m2 m3 m4 J : ℕ)
    (h1 : q1 ∣ m1) (h2 : q2 ∣ m2) (h3 : q3 ∣ m3) (h4 : q4 ∣ m4) :
    u2Drift4 q1 q2 q3 q4 J ≤ u2Drift4 m1 m2 m3 m4 J := by
  calc
    u2Drift4 q1 q2 q3 q4 J ≤ u2Drift4 m1 q2 q3 q4 J :=
      u2Drift4_dvd_mono_first q1 m1 q2 q3 q4 J h1
    _ ≤ u2Drift4 m1 m2 q3 q4 J :=
      u2Drift4_dvd_mono_second m1 q2 m2 q3 q4 J h2
    _ ≤ u2Drift4 m1 m2 m3 q4 J :=
      u2Drift4_dvd_mono_third m1 m2 q3 m3 q4 J h3
    _ ≤ u2Drift4 m1 m2 m3 m4 J :=
      u2Drift4_dvd_mono_fourth m1 m2 m3 q4 m4 J h4

/-- The only terminal U2 input after divisor lowering. There are 35
unordered four-multisets over the four listed primes. -/
def U2PrimeKernel : Prop :=
  ∀ q1 q2 q3 q4 J : ℕ,
    IsU2SmallPrime q1 → IsU2SmallPrime q2 →
    IsU2SmallPrime q3 → IsU2SmallPrime q4 →
      7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 q1 q2 q3 q4 J

/-- A prime-kernel certificate implies U2 throughout the complete terminal box. -/
theorem u2_terminal_box_of_primeKernel (hprime : U2PrimeKernel)
    (m1 m2 m3 m4 J : ℕ)
    (h1lo : 2 ≤ m1) (h2lo : 2 ≤ m2) (h3lo : 2 ≤ m3) (h4lo : 2 ≤ m4)
    (h1hi : m1 ≤ 10) (h2hi : m2 ≤ 10) (h3hi : m3 ≤ 10) (h4hi : m4 ≤ 10) :
    7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 J := by
  obtain ⟨q1, hq1, hd1⟩ := exists_smallPrime_dvd m1 h1lo h1hi
  obtain ⟨q2, hq2, hd2⟩ := exists_smallPrime_dvd m2 h2lo h2hi
  obtain ⟨q3, hq3, hd3⟩ := exists_smallPrime_dvd m3 h3lo h3hi
  obtain ⟨q4, hq4, hd4⟩ := exists_smallPrime_dvd m4 h4lo h4hi
  have hp := hprime q1 q2 q3 q4 J hq1 hq2 hq3 hq4
  have hm := u2Drift4_dvd_mono q1 q2 q3 q4 m1 m2 m3 m4 J hd1 hd2 hd3 hd4
  linarith

/-- Add one term to a positive initial-interval sum. -/
private lemma sum_Ioc_succ (F : ℕ → ℚ) (y : ℕ) :
    (∑ k ∈ Finset.Ioc 0 (y + 1), F k)
      = (∑ k ∈ Finset.Ioc 0 y, F k) + F (y + 1) := by
  have hins : Finset.Ioc 0 (y + 1) = insert (y + 1) (Finset.Ioc 0 y) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hnot : y + 1 ∉ Finset.Ioc 0 y := by simp
  rw [hins, Finset.sum_insert hnot]
  ring

/-- A periodic rational summand gains exactly one period sum when its endpoint
is translated by the period. -/
private lemma sum_Ioc_add_period (F : ℕ → ℚ) {L : ℕ}
    (hper : ∀ k, F (k + L) = F k) (x : ℕ) :
    (∑ k ∈ Finset.Ioc 0 (x + L), F k)
      = (∑ k ∈ Finset.Ioc 0 x, F k) + ∑ k ∈ Finset.Ioc 0 L, F k := by
  induction x with
  | zero => simp
  | succ x ih =>
      have e1 : x + 1 + L = (x + L) + 1 := by omega
      have e2 : F ((x + L) + 1) = F (x + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hper (x + 1)
      rw [e1, sum_Ioc_succ F (x + L), ih, sum_Ioc_succ F x, e2]
      ring

/-- The four-modulus drift summand is periodic under any common multiple. -/
lemma u2Term4_add_period (m1 m2 m3 m4 L j : ℕ)
    (h1 : m1 ∣ L) (h2 : m2 ∣ L) (h3 : m3 ∣ L) (h4 : m4 ∣ L) :
    u2Term4 m1 m2 m3 m4 (j + L) = u2Term4 m1 m2 m3 m4 j := by
  have e1 : m1 ∣ j + L ↔ m1 ∣ j := by
    rw [Nat.add_comm]
    exact Nat.dvd_add_right h1
  have e2 : m2 ∣ j + L ↔ m2 ∣ j := by
    rw [Nat.add_comm]
    exact Nat.dvd_add_right h2
  have e3 : m3 ∣ j + L ↔ m3 ∣ j := by
    rw [Nat.add_comm]
    exact Nat.dvd_add_right h3
  have e4 : m4 ∣ j + L ↔ m4 ∣ j := by
    rw [Nat.add_comm]
    exact Nat.dvd_add_right h4
  simp only [u2Term4, u2Count4, e1, e2, e3, e4]

theorem u2Drift4_add_period (m1 m2 m3 m4 L J : ℕ)
    (h1 : m1 ∣ L) (h2 : m2 ∣ L) (h3 : m3 ∣ L) (h4 : m4 ∣ L) :
    u2Drift4 m1 m2 m3 m4 (J + L)
      = u2Drift4 m1 m2 m3 m4 J + u2Drift4 m1 m2 m3 m4 L := by
  exact sum_Ioc_add_period (u2Term4 m1 m2 m3 m4)
    (fun j => u2Term4_add_period m1 m2 m3 m4 L j h1 h2 h3 h4) J

/-- Iterated period propagation for the U2 drift. -/
theorem u2Drift4_add_mul_period (m1 m2 m3 m4 L J q : ℕ)
    (h1 : m1 ∣ L) (h2 : m2 ∣ L) (h3 : m3 ∣ L) (h4 : m4 ∣ L) :
    u2Drift4 m1 m2 m3 m4 (J + q * L)
      = u2Drift4 m1 m2 m3 m4 J
        + (q : ℚ) * u2Drift4 m1 m2 m3 m4 L := by
  induction q with
  | zero => simp
  | succ q ih =>
      have heq : J + (q + 1) * L = (J + q * L) + L := by ring
      rw [heq, u2Drift4_add_period m1 m2 m3 m4 L (J + q * L) h1 h2 h3 h4, ih]
      push_cast
      ring

def u2Period4 (m1 m2 m3 m4 : ℕ) : ℕ :=
  Nat.lcm (Nat.lcm (Nat.lcm m1 m2) m3) m4

lemma dvd_u2Period4_first (m1 m2 m3 m4 : ℕ) :
    m1 ∣ u2Period4 m1 m2 m3 m4 := by
  exact ((Nat.dvd_lcm_left m1 m2).trans
    (Nat.dvd_lcm_left (Nat.lcm m1 m2) m3)).trans
      (Nat.dvd_lcm_left (Nat.lcm (Nat.lcm m1 m2) m3) m4)

lemma dvd_u2Period4_second (m1 m2 m3 m4 : ℕ) :
    m2 ∣ u2Period4 m1 m2 m3 m4 := by
  exact ((Nat.dvd_lcm_right m1 m2).trans
    (Nat.dvd_lcm_left (Nat.lcm m1 m2) m3)).trans
      (Nat.dvd_lcm_left (Nat.lcm (Nat.lcm m1 m2) m3) m4)

lemma dvd_u2Period4_third (m1 m2 m3 m4 : ℕ) :
    m3 ∣ u2Period4 m1 m2 m3 m4 := by
  exact (Nat.dvd_lcm_right (Nat.lcm m1 m2) m3).trans
    (Nat.dvd_lcm_left (Nat.lcm (Nat.lcm m1 m2) m3) m4)

lemma dvd_u2Period4_fourth (m1 m2 m3 m4 : ℕ) :
    m4 ∣ u2Period4 m1 m2 m3 m4 :=
  Nat.dvd_lcm_right (Nat.lcm (Nat.lcm m1 m2) m3) m4

lemma u2Period4_pos (m1 m2 m3 m4 : ℕ)
    (h1 : 0 < m1) (h2 : 0 < m2) (h3 : 0 < m3) (h4 : 0 < m4) :
    0 < u2Period4 m1 m2 m3 m4 := by
  exact Nat.lcm_pos (Nat.lcm_pos (Nat.lcm_pos h1 h2) h3) h4

/-- One-period prefix control plus a sufficient period slope implies the U2
line for every endpoint. -/
theorem u2_bound_of_period_certificate (m1 m2 m3 m4 L : ℕ)
    (hL : 0 < L)
    (h1 : m1 ∣ L) (h2 : m2 ∣ L) (h3 : m3 ∣ L) (h4 : m4 ∣ L)
    (hprefix : ∀ r : ℕ, r ≤ L →
      7 * (r : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 r)
    (hslope : 7 * (L : ℚ) ≤ 300 * u2Drift4 m1 m2 m3 m4 L)
    (J : ℕ) :
    7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 J := by
  let r := J % L
  let q := J / L
  have hr : r ≤ L := le_of_lt (by simpa [r] using Nat.mod_lt J hL)
  have hp := hprefix r hr
  have hq : (0 : ℚ) ≤ (q : ℚ) := by positivity
  have hs := mul_le_mul_of_nonneg_left hslope hq
  have hdecomp : J = r + q * L := by
    calc
      J = J % L + L * (J / L) := (Nat.mod_add_div J L).symm
      _ = r + q * L := by simp [r, q, Nat.mul_comm]
  rw [hdecomp, u2Drift4_add_mul_period m1 m2 m3 m4 L r q h1 h2 h3 h4]
  push_cast
  linarith

lemma smallPrime_pos {q : ℕ} (hq : IsU2SmallPrime q) : 0 < q := by
  rcases hq with rfl | rfl | rfl | rfl <;> norm_num

/-- Finite terminal certificate interface: for each of the 35 prime
multisets, check only prefixes through one LCM period and the period slope. -/
def U2PrimePeriodKernel : Prop :=
  ∀ q1 q2 q3 q4 : ℕ,
    IsU2SmallPrime q1 → IsU2SmallPrime q2 →
    IsU2SmallPrime q3 → IsU2SmallPrime q4 →
    let L := u2Period4 q1 q2 q3 q4
    (∀ r : ℕ, r ≤ L →
      7 * (r : ℚ) - 70 ≤ 300 * u2Drift4 q1 q2 q3 q4 r) ∧
    7 * (L : ℚ) ≤ 300 * u2Drift4 q1 q2 q3 q4 L

/-- The finite one-period prime certificate implies the all-endpoint prime kernel. -/
theorem u2PrimeKernel_of_periodKernel (hperiod : U2PrimePeriodKernel) :
    U2PrimeKernel := by
  intro q1 q2 q3 q4 J hq1 hq2 hq3 hq4
  rcases hperiod q1 q2 q3 q4 hq1 hq2 hq3 hq4 with ⟨hprefix, hslope⟩
  exact u2_bound_of_period_certificate q1 q2 q3 q4
    (u2Period4 q1 q2 q3 q4)
    (u2Period4_pos q1 q2 q3 q4 (smallPrime_pos hq1)
      (smallPrime_pos hq2) (smallPrime_pos hq3) (smallPrime_pos hq4))
    (dvd_u2Period4_first q1 q2 q3 q4)
    (dvd_u2Period4_second q1 q2 q3 q4)
    (dvd_u2Period4_third q1 q2 q3 q4)
    (dvd_u2Period4_fourth q1 q2 q3 q4)
    hprefix hslope J

/-- The finite one-period prime certificate closes the complete terminal box. -/
theorem u2_terminal_box_of_primePeriodKernel (hperiod : U2PrimePeriodKernel)
    (m1 m2 m3 m4 J : ℕ)
    (h1lo : 2 ≤ m1) (h2lo : 2 ≤ m2) (h3lo : 2 ≤ m3) (h4lo : 2 ≤ m4)
    (h1hi : m1 ≤ 10) (h2hi : m2 ≤ 10) (h3hi : m3 ≤ 10) (h4hi : m4 ≤ 10) :
    7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 J :=
  u2_terminal_box_of_primeKernel (u2PrimeKernel_of_periodKernel hperiod)
    m1 m2 m3 m4 J h1lo h2lo h3lo h4lo h1hi h2hi h3hi h4hi

end Erdos488
