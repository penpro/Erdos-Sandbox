import Mathlib

/-!
# Erdős Problem 488 for a primitive triple (uncovered zone) — arithmetic core

Elementary formalization of the self-contained number-theoretic steps of the
`|P| ≤ 3` proof: the floor bound (Lemma 1(ii)) and the parity dichotomy
(Lemma 4).  The counting (Bonferroni) and assembly are developed separately.

Conventions for a primitive triple `a < b < c` (`primitive`: no element divides
another).  The *uncovered zone* `1/b + 1/c > 1/a` is, cleared of denominators,
`b*c < a*(b+c)`.
-/

namespace Erdos488

/-- **Lemma 1(ii).**  For `t ≥ 1`, a divisor `q ≥ 2` and a divisor `q' ≥ 3`,
`t − ⌊t/q⌋ − ⌊t/q'⌋ ≥ 1`. -/
lemma floor_bound {t q q' : ℕ} (ht : 1 ≤ t) (hq : 2 ≤ q) (hq' : 3 ≤ q') :
    1 ≤ t - t / q - t / q' := by
  have h1 : t / q ≤ t / 2 := Nat.div_le_div_left hq (by norm_num)
  have h2 : t / q' ≤ t / 3 := Nat.div_le_div_left hq' (by norm_num)
  omega

/-- **Lemma 3.**  For `x < y` with `x ∤ y`, `lcm(x,y)/x = y/gcd(x,y) ≥ 3` and
`lcm(x,y)/y = x/gcd(x,y) ≥ 2`. -/
lemma ratio_bounds {x y : ℕ} (hx : 0 < x) (hxy : x < y) (hnd : ¬ x ∣ y) :
    3 ≤ y / Nat.gcd x y ∧ 2 ≤ x / Nat.gcd x y := by
  have hgpos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
  have hgx : Nat.gcd x y ∣ x := Nat.gcd_dvd_left x y
  have hgy : Nat.gcd x y ∣ y := Nat.gcd_dvd_right x y
  have hxe : Nat.gcd x y * (x / Nat.gcd x y) = x := Nat.mul_div_cancel' hgx
  have hye : Nat.gcd x y * (y / Nat.gcd x y) = y := Nat.mul_div_cancel' hgy
  set qx := x / Nat.gcd x y
  set qy := y / Nat.gcd x y
  have hqxpos : 0 < qx := Nat.div_pos (Nat.le_of_dvd hx hgx) hgpos
  have hqlt : qx < qy := by
    have h : Nat.gcd x y * qx < Nat.gcd x y * qy := by rw [hxe, hye]; exact hxy
    exact lt_of_mul_lt_mul_left h (Nat.zero_le _)
  have hndq : ¬ qx ∣ qy := by
    intro h
    apply hnd
    have hd : Nat.gcd x y * qx ∣ Nat.gcd x y * qy := mul_dvd_mul_left _ h
    rwa [hxe, hye] at hd
  clear_value qx qy
  refine ⟨?_, ?_⟩
  · by_contra h; push_neg at h
    interval_cases qy
    · omega
    · omega
    · exact hndq (by rw [show qx = 1 by omega]; exact one_dvd 2)
  · by_contra h; push_neg at h
    exact hndq (by rw [show qx = 1 by omega]; exact one_dvd qy)

/-- Helper: if `lcm(x,c) = 2*c` and `¬ x ∣ c`, then `k := 2*c/x` is odd and
`x*k = 2*c`, with `k > 0` (given `0 < c`). -/
lemma odd_cofactor {x c : ℕ} (hx : 0 < x) (hc : 0 < c) (hlc : Nat.lcm x c = 2 * c)
    (hnd : ¬ x ∣ c) : x * (2 * c / x) = 2 * c ∧ Odd (2 * c / x) ∧ 0 < 2 * c / x := by
  have hxdvd : x ∣ 2 * c := hlc ▸ Nat.dvd_lcm_left x c
  set k := 2 * c / x with hk
  have hxk : x * k = 2 * c := Nat.mul_div_cancel' hxdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hxk; omega
    · exact h
  refine ⟨hxk, ?_, hkpos⟩
  rw [Nat.odd_iff]
  by_contra hodd
  -- k even ⇒ x * (k/2) = c ⇒ x ∣ c
  have hke : k % 2 = 0 := by omega
  obtain ⟨m, hm⟩ : 2 ∣ k := Nat.dvd_of_mod_eq_zero hke
  have hxm : x * m = c := by
    have h2 : x * (2 * m) = 2 * c := by rw [← hm]; exact hxk
    have h4 : x * (2 * m) = 2 * (x * m) := by ring
    omega
  exact hnd ⟨m, hxm.symm⟩

/-- **Lemma 4 (parity dichotomy).**  In the uncovered zone, `lcm(a,c)` and
`lcm(b,c)` cannot both equal `2*c`. -/
lemma parity_dichotomy {a b c : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c)
    (hunc : b * c < a * (b + c)) :
    ¬ (Nat.lcm a c = 2 * c ∧ Nat.lcm b c = 2 * c) := by
  rintro ⟨hlca, hlcb⟩
  have hc : 0 < c := by omega
  have hb : 0 < b := by omega
  obtain ⟨hak, hkodd, hkpos⟩ := odd_cofactor ha hc hlca hnac
  obtain ⟨hbl, hlodd, hlpos⟩ := odd_cofactor hb hc hlcb hnbc
  set k := 2 * c / a with hkdef
  set l := 2 * c / b with hldef
  -- a*k = b*l = 2c
  have habkl : a * k = b * l := by rw [hak, hbl]
  -- a < b ⇒ k > l
  have hkl : l < k := by
    by_contra h
    push_neg at h    -- k ≤ l
    have : a * k < b * l := by
      calc a * k ≤ a * l := Nat.mul_le_mul_left a h
        _ < b * l := (Nat.mul_lt_mul_right hlpos).mpr hab
    omega
  -- both odd, l < k ⇒ l + 2 ≤ k
  have hkl2 : l + 2 ≤ k := by
    rcases hkodd with ⟨kk, hkk⟩
    rcases hlodd with ⟨ll, hll⟩
    omega
  -- key1 : a*b*k < 2*a*b + a*a*k   (uncovered × 2, using 2c = a*k)
  have e1 : a * b * k = 2 * (b * c) := by
    have : a * b * k = (a * k) * b := by ring
    rw [this, hak]; ring
  have e2 : a * a * k = 2 * (a * c) := by
    have : a * a * k = (a * k) * a := by ring
    rw [this, hak]; ring
  have key1 : a * b * k < 2 * (a * b) + a * a * k := by
    rw [e1, e2]; nlinarith [hunc]
  -- key2 : a*a*k + 2*(a*b) ≤ a*b*k
  have step : a * k + 2 * b ≤ b * k := by
    have h1 : b * (l + 2) ≤ b * k := Nat.mul_le_mul_left b hkl2
    have h2 : b * (l + 2) = b * l + 2 * b := by ring
    rw [h2, ← habkl] at h1
    omega
  have key2 : a * a * k + 2 * (a * b) ≤ a * b * k := by
    have := Nat.mul_le_mul_left a step
    nlinarith [this]
  omega

end Erdos488
