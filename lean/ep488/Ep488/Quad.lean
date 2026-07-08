import Ep488.Certificate

/-!
# Toward `|primitive core| ≤ 4`

Formalization of the quadruple charge method (Codex's `quadruple_charge_notes.md`,
Claude-audited). This file is built incrementally; it starts with the arithmetic
foundation — the 3-term charge floor bound, the quadruple analogue of
`Erdos488.floor_bound`.
-/

namespace Erdos488

/-- **3-term charge floor bound** (Prop 8″ arithmetic core, quadruple case).
If the integer charge condition `k₂k₃ + k₁k₃ + k₁k₂ < k₁k₂k₃` holds (i.e.
`1/k₁+1/k₂+1/k₃ < 1`), then for `t ≥ 1` the per-generator charge is `≥ 1`:
`1 ≤ t − t/k₁ − t/k₂ − t/k₃`. -/
lemma floor_bound3 {t k1 k2 k3 : ℕ} (ht : 1 ≤ t)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hk3 : 1 ≤ k3)
    (hcharge : k2 * k3 + k1 * k3 + k1 * k2 < k1 * k2 * k3) :
    1 ≤ t - t / k1 - t / k2 - t / k3 := by
  have hK : 0 < k1 * k2 * k3 := by positivity
  -- K * (t/kᵢ) ≤ t * (product of the other two)
  have e1 : k1 * k2 * k3 * (t / k1) ≤ t * (k2 * k3) := by
    have h := Nat.div_mul_le_self t k1
    nlinarith [h, Nat.zero_le (k2 * k3)]
  have e2 : k1 * k2 * k3 * (t / k2) ≤ t * (k1 * k3) := by
    have h := Nat.div_mul_le_self t k2
    nlinarith [h, Nat.zero_le (k1 * k3)]
  have e3 : k1 * k2 * k3 * (t / k3) ≤ t * (k1 * k2) := by
    have h := Nat.div_mul_le_self t k3
    nlinarith [h, Nat.zero_le (k1 * k2)]
  -- sum, then use the charge condition scaled by t
  have hsum : k1 * k2 * k3 * (t / k1 + t / k2 + t / k3)
      ≤ t * (k2 * k3 + k1 * k3 + k1 * k2) := by nlinarith [e1, e2, e3]
  have hlt : t * (k2 * k3 + k1 * k3 + k1 * k2) < t * (k1 * k2 * k3) :=
    by nlinarith [hcharge, ht]
  have hcancel : t / k1 + t / k2 + t / k3 < t := by
    have hchain : k1 * k2 * k3 * (t / k1 + t / k2 + t / k3) < k1 * k2 * k3 * t := by
      calc k1 * k2 * k3 * (t / k1 + t / k2 + t / k3)
          ≤ t * (k2 * k3 + k1 * k3 + k1 * k2) := hsum
        _ < t * (k1 * k2 * k3) := hlt
        _ = k1 * k2 * k3 * t := by ring
    exact Nat.lt_of_mul_lt_mul_left hchain
  omega

/-- Helper: `1 ≤ lcm(e,f)/e` when `e, f ≥ 1`. -/
private lemma one_le_lcm_div {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    1 ≤ Nat.lcm e f / e := by
  rw [Nat.one_le_div_iff (by omega)]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega)) (Nat.dvd_lcm_left e f)

/-- **Prop 8″ (quadruple charge, `good ⟹ X_e ≥ 1`).** For an element `e` with the
three other generators `f₁,f₂,f₃`, if `e` is good — the integer charge condition
on the cofactors `kᵢ = lcm(e,fᵢ)/e` (i.e. `1/k₁+1/k₂+1/k₃ < 1`) — then the charge
`X_e(n) = ⌊n/e⌋ − Σ⌊n/lcm(e,fᵢ)⌋ ≥ 1` for every `n ≥ e`. -/
lemma charge_ge_one {e f1 f2 f3 n : ℕ}
    (he : 1 ≤ e) (hf1 : 1 ≤ f1) (hf2 : 1 ≤ f2) (hf3 : 1 ≤ f3) (hn : e ≤ n)
    (hcharge : (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f3 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e)
             < (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)) :
    1 ≤ n / e - n / Nat.lcm e f1 - n / Nat.lcm e f2 - n / Nat.lcm e f3 := by
  rw [div_lcm_eq n e f1, div_lcm_eq n e f2, div_lcm_eq n e f3]
  have ht : 1 ≤ n / e := (Nat.one_le_div_iff (by omega)).2 hn
  exact floor_bound3 ht (one_le_lcm_div he hf1) (one_le_lcm_div he hf2)
    (one_le_lcm_div he hf3) hcharge

/-! ### Pointwise arithmetic core of the two-good-charge proposition

For a 4-element set, a point `k` is divided by `d ≤ 4` of the elements. These two
facts are the per-point content of the inclusion–exclusion identity `2B = s + H`
and of the `Y_H ≥ 2` weight bound; both are pure `ℕ` arithmetic (`interval_cases`
+ `decide`), independent of the Finset bookkeeping that sums them over `(0,n]`. -/

/-- **4-set inclusion–exclusion, per point.** For a point with `d ≤ 4` divisors,
`2·[d ≥ 1] = 2d − 2·C(d,2) + 2·C(d,3) − 2·C(d,4)` (additive form, no ℕ subtraction).
Summed over `k ∈ (0,n]` this is `2·B(n) = s − 2P₂ + 2T₃ − 2T₄ + s = s + H`. -/
lemma ie4_pointwise {d : ℕ} (hd : d ≤ 4) :
    2 * min d 1 + 2 * d.choose 2 + 2 * d.choose 4 = 2 * d + 2 * d.choose 3 := by
  interval_cases d <;> decide

/-- **`Y_H` weight nonnegativity, per point.** With `p` = #(H-elements dividing k)
and `q` = #(G-elements dividing k), both `≤ 2`, the `Y_H` weight
`p(2−p−q) + 2·C(p+q,3) − 2·C(p+q,4) ≥ 0` (additive form). -/
lemma yh_weight_nonneg {p q : ℕ} (hp : p ≤ 2) (hq : q ≤ 2) :
    p * (p + q) + 2 * (p + q).choose 4 ≤ 2 * p + 2 * (p + q).choose 3 := by
  interval_cases p <;> interval_cases q <;> decide

/-! ### The card→sum bridge (workhorse for the summation layer)

Every count `n/L` in the inclusion–exclusion identity is turned into a sum over
`k ∈ (0,n]` of the indicator `[L ∣ k]`, in `ℤ` (signs need subtraction). -/

open Finset in
/-- `⌊n/L⌋ = Σ_{k ∈ (0,n]} [L ∣ k]`, cast to `ℤ`. -/
lemma cast_div_eq_sum_indicator (L n : ℕ) :
    ((n / L : ℕ) : ℤ) = ∑ k ∈ Ioc 0 n, if L ∣ k then (1 : ℤ) else 0 := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div n L, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : L ∣ k <;> simp [h]

/-- **Pointwise 4-event inclusion–exclusion.** For four decidable props (at a
fixed `k`: the events `a∣k, …, d∣k`), the union indicator equals the alternating
sum of the single/pair/triple/quad indicators. Proved by `decide` over the 16
boolean cases. -/
lemma ie4_bool (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d] :
    (if a ∨ b ∨ c ∨ d then (1 : ℤ) else 0)
      = ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + (if d then (1:ℤ) else 0))
        - ((if a ∧ b then 1 else 0) + (if a ∧ c then 1 else 0) + (if a ∧ d then 1 else 0)
          + (if b ∧ c then 1 else 0) + (if b ∧ d then 1 else 0) + (if c ∧ d then (1:ℤ) else 0))
        + ((if a ∧ b ∧ c then 1 else 0) + (if a ∧ b ∧ d then 1 else 0)
          + (if a ∧ c ∧ d then 1 else 0) + (if b ∧ c ∧ d then (1:ℤ) else 0))
        - (if a ∧ b ∧ c ∧ d then (1:ℤ) else 0) := by
  by_cases a <;> by_cases b <;> by_cases c <;> by_cases d <;> simp_all

/-- `s(n) = ⌊n/a⌋+⌊n/b⌋+⌊n/c⌋+⌊n/d⌋`. -/
def sfun4 (a b c d n : ℕ) : ℕ := n / a + n / b + n / c + n / d

/-- `P₂(n)` = sum of `⌊n/lcm⌋` over the 6 pairs. -/
def p2fun4 (a b c d n : ℕ) : ℕ :=
  n / Nat.lcm a b + n / Nat.lcm a c + n / Nat.lcm a d
    + n / Nat.lcm b c + n / Nat.lcm b d + n / Nat.lcm c d

/-- `T₃(n)` = sum of `⌊n/lcm⌋` over the 4 triples (fixed nested-lcm order). -/
def t3fun4 (a b c d n : ℕ) : ℕ :=
  n / Nat.lcm (Nat.lcm a b) c + n / Nat.lcm (Nat.lcm a b) d
    + n / Nat.lcm (Nat.lcm a c) d + n / Nat.lcm (Nat.lcm b c) d

/-- `T₄(n) = ⌊n/lcm(a,b,c,d)⌋`. -/
def t4fun4 (a b c d n : ℕ) : ℕ := n / Nat.lcm (Nat.lcm (Nat.lcm a b) c) d

/-- `lcm(x,y) ∣ k ↔ x∣k ∧ y∣k`, as an indicator equality. -/
lemma lcm2_ind (x y k : ℕ) :
    (if Nat.lcm x y ∣ k then (1 : ℤ) else 0) = if x ∣ k ∧ y ∣ k then 1 else 0 := by
  have h : (Nat.lcm x y ∣ k) ↔ (x ∣ k ∧ y ∣ k) :=
    ⟨fun h => ⟨(Nat.dvd_lcm_left x y).trans h, (Nat.dvd_lcm_right x y).trans h⟩,
     fun h => Nat.lcm_dvd h.1 h.2⟩
  simp only [h]

/-- `lcm(lcm(x,y),z) ∣ k ↔ x∣k ∧ y∣k ∧ z∣k`, as an indicator equality. -/
lemma lcm3_ind (x y z k : ℕ) :
    (if Nat.lcm (Nat.lcm x y) z ∣ k then (1 : ℤ) else 0)
      = if x ∣ k ∧ y ∣ k ∧ z ∣ k then 1 else 0 := by
  have h : (Nat.lcm (Nat.lcm x y) z ∣ k) ↔ (x ∣ k ∧ y ∣ k ∧ z ∣ k) := by
    constructor
    · intro hd
      have h1 : Nat.lcm x y ∣ k := (Nat.dvd_lcm_left _ _).trans hd
      exact ⟨(Nat.dvd_lcm_left x y).trans h1, (Nat.dvd_lcm_right x y).trans h1,
        (Nat.dvd_lcm_right _ _).trans hd⟩
    · rintro ⟨hx, hy, hz⟩
      exact Nat.lcm_dvd (Nat.lcm_dvd hx hy) hz
  simp only [h]

/-- `lcm(lcm(lcm(x,y),z),w) ∣ k ↔ x∣k ∧ y∣k ∧ z∣k ∧ w∣k`, as an indicator equality. -/
lemma lcm4_ind (x y z w k : ℕ) :
    (if Nat.lcm (Nat.lcm (Nat.lcm x y) z) w ∣ k then (1 : ℤ) else 0)
      = if x ∣ k ∧ y ∣ k ∧ z ∣ k ∧ w ∣ k then 1 else 0 := by
  have h : (Nat.lcm (Nat.lcm (Nat.lcm x y) z) w ∣ k)
      ↔ (x ∣ k ∧ y ∣ k ∧ z ∣ k ∧ w ∣ k) := by
    constructor
    · intro hd
      have h2 : Nat.lcm (Nat.lcm x y) z ∣ k := (Nat.dvd_lcm_left _ _).trans hd
      have h1 : Nat.lcm x y ∣ k := (Nat.dvd_lcm_left _ _).trans h2
      exact ⟨(Nat.dvd_lcm_left x y).trans h1, (Nat.dvd_lcm_right x y).trans h1,
        (Nat.dvd_lcm_right _ _).trans h2, (Nat.dvd_lcm_right _ _).trans hd⟩
    · rintro ⟨hx, hy, hz, hw⟩
      exact Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd hx hy) hz) hw
  simp only [h]

/-- **Exact 4-set inclusion–exclusion** (in `ℤ`): `B = s − P₂ + T₃ − T₄`. -/
lemma card_ie4 (a b c d n : ℕ) :
    ((Bgen {a, b, c, d} n).card : ℤ)
      = (sfun4 a b c d n : ℤ) - (p2fun4 a b c d n : ℤ)
        + (t3fun4 a b c d n : ℤ) - (t4fun4 a b c d n : ℤ) := by
  have hL : ((Bgen {a, b, c, d} n).card : ℤ)
      = ∑ k ∈ Finset.Ioc 0 n, if a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k then (1 : ℤ) else 0 := by
    rw [Bgen_eq_filter, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hiff : (∃ e ∈ ({a, b, c, d} : Finset ℕ), e ∣ k) ↔ (a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨e, (rfl | rfl | rfl | rfl), h⟩ <;> tauto
      · rintro (h | h | h | h)
        exacts [⟨a, Or.inl rfl, h⟩, ⟨b, Or.inr (Or.inl rfl), h⟩,
          ⟨c, Or.inr (Or.inr (Or.inl rfl)), h⟩, ⟨d, Or.inr (Or.inr (Or.inr rfl)), h⟩]
    by_cases hk : a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k <;> simp [hiff, hk]
  rw [hL]
  simp only [sfun4, p2fun4, t3fun4, t4fun4, Nat.cast_add, cast_div_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lcm4_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind,
    lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind]
  have hb := ie4_bool (a ∣ k) (b ∣ k) (c ∣ k) (d ∣ k)
  linarith [hb]

/-- `2B = 2s − 2P₂ + 2T₃ − 2T₄` (in ℤ), immediate from `card_ie4`. -/
lemma two_B_eq (a b c d n : ℕ) :
    2 * ((Bgen {a, b, c, d} n).card : ℤ)
      = 2 * (sfun4 a b c d n : ℤ) - 2 * (p2fun4 a b c d n : ℤ)
        + 2 * (t3fun4 a b c d n : ℤ) - 2 * (t4fun4 a b c d n : ℤ) := by
  have h := card_ie4 a b c d n
  linarith

/-- **Charge in ℤ (Prop 8″ recast).** For a good element `e` (charge condition on
the cofactors `kᵢ = lcm(e,fᵢ)/e`), the ℤ charge `X_e = ⌊n/e⌋ − Σ⌊n/lcm(e,fᵢ)⌋ ≥ 1`
for `n ≥ e`. -/
lemma charge_ge_one_int {e f1 f2 f3 n : ℕ}
    (he : 1 ≤ e) (hf1 : 1 ≤ f1) (hf2 : 1 ≤ f2) (hf3 : 1 ≤ f3) (hn : e ≤ n)
    (hcharge : (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f3 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e)
             < (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)) :
    1 ≤ ((n / e : ℕ) : ℤ) - ((n / Nat.lcm e f1 : ℕ) : ℤ) - ((n / Nat.lcm e f2 : ℕ) : ℤ)
        - ((n / Nat.lcm e f3 : ℕ) : ℤ) := by
  have h := charge_ge_one he hf1 hf2 hf3 hn hcharge
  omega

/-- **Charge-sum identity.** The four charges sum to `s − 2P₂` (each pairwise
`lcm` term is subtracted by both of its endpoints). -/
lemma charge_sum4 (a b c d n : ℕ) :
    (((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ))
      + (((n / c : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm c d : ℕ) : ℤ))
      + (((n / d : ℕ) : ℤ) - ((n / Nat.lcm a d : ℕ) : ℤ) - ((n / Nat.lcm b d : ℕ) : ℤ)
        - ((n / Nat.lcm c d : ℕ) : ℤ))
      = (sfun4 a b c d n : ℤ) - 2 * (p2fun4 a b c d n : ℤ) := by
  simp only [sfun4, p2fun4, Nat.cast_add]
  ring

end Erdos488
