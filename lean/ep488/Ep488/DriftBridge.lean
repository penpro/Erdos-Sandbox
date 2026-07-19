import Ep488.Transport

/-!
# The U2 drift bridge: algebraic assembly

This module machine-checks the rational and floor-loss layer between the
per-element U2 certificate and the size-5 finite-n bridge. The finite U2 kernel
itself remains an explicit hypothesis.

For each generator, U2 gives f(J) >= (7/300) J - 7/30. Together with the exact
multiplicity identity and the five floor losses, this gives

150 (2B(n) - nS) >= 7nS - 1135 + 157S.

The two corollaries are the strict bridge and the tower-form handoff.
-/

namespace Erdos488

/-- The reciprocal sum of five positive generators, as a rational. -/
def reciprocalSum5 (a b c d e : ℕ) : ℚ :=
  1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) + 1 / (d : ℚ) + 1 / (e : ℚ)

/-- The sum of the five floor arguments floor(n/a_i), as a rational. -/
def floorSum5 (a b c d e n : ℕ) : ℚ :=
  (n / a : ℕ) + (n / b : ℕ) + (n / c : ℕ) + (n / d : ℕ) + (n / e : ℕ)

/-- Exact rational floor loss, sharpened by integrality:
floor(n/a) >= n/a - (1 - 1/a) for positive integers a. -/
lemma floor_cast_lower (n a : ℕ) (ha : 0 < a) :
    ((n / a : ℕ) : ℚ) ≥ (n : ℚ) / a - (1 - 1 / (a : ℚ)) := by
  have hmod : n % a + 1 ≤ a := Nat.succ_le_iff.mpr (Nat.mod_lt n ha)
  have hmodQ : ((n % a : ℕ) : ℚ) + 1 ≤ (a : ℚ) := by
    exact_mod_cast hmod
  have hdiv : (n : ℚ) = (a : ℚ) * (n / a : ℕ) + (n % a : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n a).symm
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  rw [hdiv]
  field_simp [ne_of_gt haQ]
  linarith

/-- Summed floor loss for five positive generators. -/
lemma floorSum5_lower (a b c d e n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    floorSum5 a b c d e n
      ≥ (n : ℚ) * reciprocalSum5 a b c d e
        - (5 - reciprocalSum5 a b c d e) := by
  have hfa := floor_cast_lower n a ha
  have hfb := floor_cast_lower n b hb
  have hfc := floor_cast_lower n c hc
  have hfd := floor_cast_lower n d hd
  have hfe := floor_cast_lower n e he
  simp only [floorSum5, reciprocalSum5]
  ring_nf at hfa hfb hfc hfd hfe ⊢
  linarith

/-- Number of the five generators dividing k, counted by position. -/
def coverCount5 (a b c d e k : ℕ) : ℕ :=
  (if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0)
    + (if c ∣ k then 1 else 0) + (if d ∣ k then 1 else 0)
    + (if e ∣ k then 1 else 0)

/-- The drift contribution owned by generator x at k. -/
def driftTerm5 (x a b c d e k : ℕ) : ℚ :=
  if x ∣ k then 1 / (coverCount5 a b c d e k : ℚ) - 1 / 2 else 0

/-- Per-generator drift, summed over (0,n]. Terms outside the multiples of x
are zero, so this is the same finite sum as the usual j <= floor(n/x) form. -/
def drift5 (x a b c d e n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Ioc 0 n, driftTerm5 x a b c d e k

/-- Pointwise multiplicity identity. If r generators cover k, the r reciprocal
shares sum to one; subtracting the five half-indicators gives the drift sum. -/
lemma drift_pointwise5 (a b c d e k : ℕ) :
    2 * (if a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k then (1 : ℚ) else 0)
        - ((if a ∣ k then (1 : ℚ) else 0) + (if b ∣ k then 1 else 0)
          + (if c ∣ k then 1 else 0) + (if d ∣ k then 1 else 0)
          + (if e ∣ k then 1 else 0))
      = 2 * (driftTerm5 a a b c d e k + driftTerm5 b a b c d e k
          + driftTerm5 c a b c d e k + driftTerm5 d a b c d e k
          + driftTerm5 e a b c d e k) := by
  by_cases ha : a ∣ k <;> by_cases hb : b ∣ k <;> by_cases hc : c ∣ k <;>
    by_cases hd : d ∣ k <;> by_cases he : e ∣ k <;>
    norm_num [coverCount5, driftTerm5, ha, hb, hc, hd, he]

/-- Rational version of the standard count of multiples in (0,n]. -/
lemma cast_div_eq_sum_indicator_q (L n : ℕ) :
    ((n / L : ℕ) : ℚ)
      = ∑ k ∈ Finset.Ioc 0 n, if L ∣ k then (1 : ℚ) else 0 := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div n L, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : L ∣ k <;> simp [h]

/-- Rational covered-set cardinality as a sum of union indicators. -/
lemma cast_Bgen5_eq_sum_indicator_q (a b c d e n : ℕ) :
    ((Bgen {a, b, c, d, e} n).card : ℚ)
      = ∑ k ∈ Finset.Ioc 0 n,
          if a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k then (1 : ℚ) else 0 := by
  rw [Bgen_eq_filter, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k <;> simp [h]

/-- Exact finite multiplicity identity:
2B(n)-sum floor(n/a_i) is twice the sum of the five drifts. -/
theorem drift_multiplicity_identity5 (a b c d e n : ℕ) :
    2 * ((Bgen {a, b, c, d, e} n).card : ℚ) - floorSum5 a b c d e n
      = 2 * (drift5 a a b c d e n + drift5 b a b c d e n
          + drift5 c a b c d e n + drift5 d a b c d e n
          + drift5 e a b c d e n) := by
  have hsum := Finset.sum_congr rfl
    (fun k (_hk : k ∈ Finset.Ioc 0 n) => drift_pointwise5 a b c d e k)
  rw [cast_Bgen5_eq_sum_indicator_q]
  simp only [floorSum5, drift5]
  rw [cast_div_eq_sum_indicator_q, cast_div_eq_sum_indicator_q,
    cast_div_eq_sum_indicator_q, cast_div_eq_sum_indicator_q,
    cast_div_eq_sum_indicator_q]
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib] using hsum

/-- The exact identity in the form consumed by the bridge assembly. -/
theorem drift_exact_identity5 (a b c d e n : ℕ) :
    2 * ((Bgen {a, b, c, d, e} n).card : ℚ)
        - (n : ℚ) * reciprocalSum5 a b c d e
      = 2 * (drift5 a a b c d e n + drift5 b a b c d e n
          + drift5 c a b c d e n + drift5 d a b c d e n
          + drift5 e a b c d e n)
        + (floorSum5 a b c d e n - (n : ℚ) * reciprocalSum5 a b c d e) := by
  have h := drift_multiplicity_identity5 a b c d e n
  linarith
/-- U2 bridge assembly. B is the rational cardinality of the covered set
and f1,...,f5 are the five per-generator drifts. The exact multiplicity
identity is supplied explicitly; each cleared U2 hypothesis is
300*f_i >= 7*floor(n/a_i)-70. -/
theorem drift_bridge_from_u2 (a b c d e n : ℕ) (B f1 f2 f3 f4 f5 : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hid :
      2 * B - (n : ℚ) * reciprocalSum5 a b c d e
        = 2 * (f1 + f2 + f3 + f4 + f5)
          + (floorSum5 a b c d e n - (n : ℚ) * reciprocalSum5 a b c d e))
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * f1)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * f2)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * f3)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * f4)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * f5) :
    7 * (n : ℚ) * reciprocalSum5 a b c d e - 1135
        + 157 * reciprocalSum5 a b c d e
      ≤ 150 * (2 * B - (n : ℚ) * reciprocalSum5 a b c d e) := by
  have hfloor := floorSum5_lower a b c d e n ha hb hc hd he
  have hsum :
      7 * floorSum5 a b c d e n - 350
        ≤ 300 * (f1 + f2 + f3 + f4 + f5) := by
    simp only [floorSum5]
    norm_num at h1 h2 h3 h4 h5 ⊢
    linarith
  rw [hid]
  linarith

/-- Strict positivity on the U2 bridge side:
7nS > 1135 - 157S implies 2B(n) > nS. -/
theorem drift_bridge_positive (a b c d e n : ℕ) (B f1 f2 f3 f4 f5 : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hid :
      2 * B - (n : ℚ) * reciprocalSum5 a b c d e
        = 2 * (f1 + f2 + f3 + f4 + f5)
          + (floorSum5 a b c d e n - (n : ℚ) * reciprocalSum5 a b c d e))
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * f1)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * f2)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * f3)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * f4)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * f5)
    (hbridge :
      1135 - 157 * reciprocalSum5 a b c d e
        < 7 * (n : ℚ) * reciprocalSum5 a b c d e) :
    (n : ℚ) * reciprocalSum5 a b c d e < 2 * B := by
  have h := drift_bridge_from_u2 a b c d e n B f1 f2 f3 f4 f5
    ha hb hc hd he hid h1 h2 h3 h4 h5
  linarith

/-- Tower handoff at the complementary endpoint:
if 7(n+1)S >= 1135, U2 gives 2B(n) >= (n+1)S. -/
theorem drift_bridge_tower (a b c d e n : ℕ) (B f1 f2 f3 f4 f5 : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hid :
      2 * B - (n : ℚ) * reciprocalSum5 a b c d e
        = 2 * (f1 + f2 + f3 + f4 + f5)
          + (floorSum5 a b c d e n - (n : ℚ) * reciprocalSum5 a b c d e))
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * f1)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * f2)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * f3)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * f4)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * f5)
    (htower : 1135 ≤ 7 * ((n : ℚ) + 1) * reciprocalSum5 a b c d e) :
    ((n : ℚ) + 1) * reciprocalSum5 a b c d e ≤ 2 * B := by
  have h := drift_bridge_from_u2 a b c d e n B f1 f2 f3 f4 f5
    ha hb hc hd he hid h1 h2 h3 h4 h5
  linarith

end Erdos488
