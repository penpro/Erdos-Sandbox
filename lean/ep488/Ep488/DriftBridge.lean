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

/-- The standard four-modulus U2 summand. -/
def u2Count4 (m1 m2 m3 m4 j : ℕ) : ℕ :=
  (if m1 ∣ j then 1 else 0) + (if m2 ∣ j then 1 else 0)
    + (if m3 ∣ j then 1 else 0) + (if m4 ∣ j then 1 else 0)

def u2Term4 (m1 m2 m3 m4 j : ℕ) : ℚ :=
  1 / (1 + u2Count4 m1 m2 m3 m4 j : ℕ) - 1 / 2

def u2Drift4 (m1 m2 m3 m4 J : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ioc 0 J, u2Term4 m1 m2 m3 m4 j

/-- Reduced-cofactor divisibility:
f divides a*j iff the reduced lcm cofactor (lcm a f)/a divides j. -/
lemma reduced_lcm_dvd_iff (a f j : ℕ) (ha : 0 < a) :
    Nat.lcm a f / a ∣ j ↔ f ∣ a * j := by
  have hal : a ∣ Nat.lcm a f := Nat.dvd_lcm_left a f
  have hfactor : a * (Nat.lcm a f / a) = Nat.lcm a f :=
    Nat.mul_div_cancel' hal
  constructor
  · rintro ⟨c, rfl⟩
    refine (Nat.dvd_lcm_right a f).trans ?_
    refine ⟨c, ?_⟩
    calc a * ((Nat.lcm a f / a) * c)
        = (a * (Nat.lcm a f / a)) * c := by ring
      _ = Nat.lcm a f * c := by rw [hfactor]
  · intro hf
    have hl : Nat.lcm a f ∣ a * j :=
      Nat.lcm_dvd (Nat.dvd_mul_right a j) hf
    obtain ⟨c, hc⟩ := hl
    refine ⟨c, ?_⟩
    have hmul : a * j = a * ((Nat.lcm a f / a) * c) := by
      calc a * j = Nat.lcm a f * c := hc
        _ = a * (Nat.lcm a f / a) * c := by rw [hfactor]
        _ = a * ((Nat.lcm a f / a) * c) := by ring
    exact Nat.eq_of_mul_eq_mul_left ha hmul

/-- In a positive antichain, every reduced lcm cofactor is at least two. -/
lemma two_le_reduced_lcm (a f : ℕ) (ha : 0 < a) (hf : 0 < f)
    (hnd : ¬ f ∣ a) : 2 ≤ Nat.lcm a f / a := by
  have hal : a ∣ Nat.lcm a f := Nat.dvd_lcm_left a f
  have hone : 1 ≤ Nat.lcm a f / a := by
    rw [Nat.one_le_div_iff ha]
    exact Nat.le_of_dvd (Nat.lcm_pos ha hf) hal
  have hne : Nat.lcm a f / a ≠ 1 := by
    intro hq
    apply hnd
    have hfl : f ∣ Nat.lcm a f := Nat.dvd_lcm_right a f
    have hfactor : a * (Nat.lcm a f / a) = Nat.lcm a f :=
      Nat.mul_div_cancel' hal
    rw [hq, Nat.mul_one] at hfactor
    rwa [← hfactor] at hfl
  omega
/-- Reindex a weighted sum over positive multiples of a by k=a*j. -/
lemma sum_multiples_reindex (a n : ℕ) (ha : 0 < a) (F : ℕ → ℚ) :
    (∑ k ∈ Finset.Ioc 0 n, if a ∣ k then F k else 0)
      = ∑ j ∈ Finset.Ioc 0 (n / a), F (a * j) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun j => a * j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨Nat.mul_pos ha hj.1, ?_⟩, Nat.dvd_mul_right a j⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hj.2
  · intro j1 hj1 j2 hj2 h
    exact Nat.eq_of_mul_eq_mul_left ha h
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkrange, hak⟩
    rcases Finset.mem_Ioc.mp hkrange with ⟨hk0, hkn⟩
    obtain ⟨j, rfl⟩ := hak
    refine ⟨j, Finset.mem_Ioc.mpr ?_, rfl⟩
    constructor
    · exact Nat.pos_of_mul_pos_left hk0
    · exact (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hkn)
  · intro j hj
    rfl

/-- A generator-owned drift is exactly the four-reduced-cofactor U2 drift. -/
theorem drift5_eq_u2Drift4 (a b c d e n : ℕ) (ha : 0 < a) :
    drift5 a a b c d e n
      = u2Drift4 (Nat.lcm a b / a) (Nat.lcm a c / a)
          (Nat.lcm a d / a) (Nat.lcm a e / a) (n / a) := by
  simp only [drift5, driftTerm5]
  rw [sum_multiples_reindex a n ha
    (fun k => 1 / (coverCount5 a b c d e k : ℚ) - 1 / 2)]
  simp only [u2Drift4]
  refine Finset.sum_congr rfl (fun j _hj => ?_)
  simp only [u2Term4, u2Count4, coverCount5]
  simp [reduced_lcm_dvd_iff, ha]
  ring
/-- The universal four-modulus U2 statement certified by census drift. -/
def U2Kernel : Prop :=
  ∀ m1 m2 m3 m4 J : ℕ,
    2 ≤ m1 → 2 ≤ m2 → 2 ≤ m3 → 2 ≤ m4 →
      7 * (J : ℚ) - 70 ≤ 300 * u2Drift4 m1 m2 m3 m4 J

/-- Transfer the universal U2 kernel to one generator-owned drift. -/
lemma drift5_u2_bound (a b c d e n : ℕ) (ha : 0 < a)
    (hm1 : 2 ≤ Nat.lcm a b / a) (hm2 : 2 ≤ Nat.lcm a c / a)
    (hm3 : 2 ≤ Nat.lcm a d / a) (hm4 : 2 ≤ Nat.lcm a e / a)
    (hU2 : U2Kernel) :
    7 * (n / a : ℕ) - 70 ≤ 300 * drift5 a a b c d e n := by
  rw [drift5_eq_u2Drift4 a b c d e n ha]
  exact hU2 _ _ _ _ _ hm1 hm2 hm3 hm4
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

/-- Concrete quintuple bridge: the exact multiplicity identity is discharged
internally, leaving only the five per-generator U2 inequalities. -/
theorem quintuple_drift_bridge (a b c d e n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * drift5 a a b c d e n)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * drift5 b a b c d e n)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * drift5 c a b c d e n)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * drift5 d a b c d e n)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * drift5 e a b c d e n) :
    7 * (n : ℚ) * reciprocalSum5 a b c d e - 1135
        + 157 * reciprocalSum5 a b c d e
      ≤ 150 * (2 * ((Bgen {a, b, c, d, e} n).card : ℚ)
          - (n : ℚ) * reciprocalSum5 a b c d e) := by
  exact drift_bridge_from_u2 a b c d e n
    ((Bgen {a, b, c, d, e} n).card : ℚ)
    (drift5 a a b c d e n) (drift5 b a b c d e n)
    (drift5 c a b c d e n) (drift5 d a b c d e n)
    (drift5 e a b c d e n) ha hb hc hd he
    (drift_exact_identity5 a b c d e n) h1 h2 h3 h4 h5

/-- Concrete strict bridge after the five U2 inputs. -/
theorem quintuple_drift_bridge_positive (a b c d e n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * drift5 a a b c d e n)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * drift5 b a b c d e n)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * drift5 c a b c d e n)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * drift5 d a b c d e n)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * drift5 e a b c d e n)
    (hbridge :
      1135 - 157 * reciprocalSum5 a b c d e
        < 7 * (n : ℚ) * reciprocalSum5 a b c d e) :
    (n : ℚ) * reciprocalSum5 a b c d e
      < 2 * ((Bgen {a, b, c, d, e} n).card : ℚ) := by
  exact drift_bridge_positive a b c d e n
    ((Bgen {a, b, c, d, e} n).card : ℚ)
    (drift5 a a b c d e n) (drift5 b a b c d e n)
    (drift5 c a b c d e n) (drift5 d a b c d e n)
    (drift5 e a b c d e n) ha hb hc hd he
    (drift_exact_identity5 a b c d e n) h1 h2 h3 h4 h5 hbridge

/-- Concrete tower handoff after the five U2 inputs. -/
theorem quintuple_drift_bridge_tower (a b c d e n : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (h1 : 7 * (n / a : ℕ) - 70 ≤ 300 * drift5 a a b c d e n)
    (h2 : 7 * (n / b : ℕ) - 70 ≤ 300 * drift5 b a b c d e n)
    (h3 : 7 * (n / c : ℕ) - 70 ≤ 300 * drift5 c a b c d e n)
    (h4 : 7 * (n / d : ℕ) - 70 ≤ 300 * drift5 d a b c d e n)
    (h5 : 7 * (n / e : ℕ) - 70 ≤ 300 * drift5 e a b c d e n)
    (htower : 1135 ≤ 7 * ((n : ℚ) + 1) * reciprocalSum5 a b c d e) :
    ((n : ℚ) + 1) * reciprocalSum5 a b c d e
      ≤ 2 * ((Bgen {a, b, c, d, e} n).card : ℚ) := by
  exact drift_bridge_tower a b c d e n
    ((Bgen {a, b, c, d, e} n).card : ℚ)
    (drift5 a a b c d e n) (drift5 b a b c d e n)
    (drift5 c a b c d e n) (drift5 d a b c d e n)
    (drift5 e a b c d e n) ha hb hc hd he
    (drift_exact_identity5 a b c d e n) h1 h2 h3 h4 h5 htower
end Erdos488
