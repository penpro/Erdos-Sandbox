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

/-- **`Y_H` pointwise nonnegativity, indicator form.** At a point `k`, with `h₁,h₂`
the two H-elements and `g₁,g₂` the two G-elements, the raw `Y_H` contribution
`[h₁]+[h₂] − 2[h₁h₂] − ([h₁g₁]+[h₁g₂]+[h₂g₁]+[h₂g₂]) + 2([h₁h₂g₁]+[h₁h₂g₂]+
[h₁g₁g₂]+[h₂g₁g₂]) − 2[h₁h₂g₁g₂] ≥ 0`. `decide` over the 16 boolean cases. -/
lemma yh_raw_nonneg (h1 h2 g1 g2 : Prop)
    [Decidable h1] [Decidable h2] [Decidable g1] [Decidable g2] :
    0 ≤ ((if h1 then (1:ℤ) else 0) + (if h2 then 1 else 0)
        - 2 * (if h1 ∧ h2 then 1 else 0)
        - ((if h1 ∧ g1 then 1 else 0) + (if h1 ∧ g2 then 1 else 0)
          + (if h2 ∧ g1 then 1 else 0) + (if h2 ∧ g2 then 1 else 0))
        + 2 * ((if h1 ∧ h2 ∧ g1 then 1 else 0) + (if h1 ∧ h2 ∧ g2 then 1 else 0)
          + (if h1 ∧ g1 ∧ g2 then 1 else 0) + (if h2 ∧ g1 ∧ g2 then 1 else 0))
        - 2 * (if h1 ∧ h2 ∧ g1 ∧ g2 then (1:ℤ) else 0)) := by
  by_cases h1 <;> by_cases h2 <;> by_cases g1 <;> by_cases g2 <;> simp_all

/-- The raw pointwise `Y_H` contribution at `k` (H-elements `a,b`, G-elements `c,d`). -/
def yhRaw (a b c d k : ℕ) : ℤ :=
  (if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0)
    - 2 * (if a ∣ k ∧ b ∣ k then 1 else 0)
    - ((if a ∣ k ∧ c ∣ k then 1 else 0) + (if a ∣ k ∧ d ∣ k then 1 else 0)
      + (if b ∣ k ∧ c ∣ k then 1 else 0) + (if b ∣ k ∧ d ∣ k then 1 else 0))
    + 2 * ((if a ∣ k ∧ b ∣ k ∧ c ∣ k then 1 else 0) + (if a ∣ k ∧ b ∣ k ∧ d ∣ k then 1 else 0)
      + (if a ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0) + (if b ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0))
    - 2 * (if a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0)

/-- **`Y_H = Σ_k yhRaw`.** The pointwise expansion of `X_a + X_b + 2T₃ − 2T₄`. -/
lemma yh_eq_sum (a b c d n : ℕ) :
    ((((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ))
      + 2 * (t3fun4 a b c d n : ℤ) - 2 * (t4fun4 a b c d n : ℤ))
      = ∑ k ∈ Finset.Ioc 0 n, yhRaw a b c d k := by
  simp only [yhRaw, t3fun4, t4fun4, Nat.cast_add, cast_div_eq_sum_indicator, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind,
    lcm4_ind]
  ring

/-- **`Y_H ≥ 2`.** For H-elements `a,b` (`≤ n`, positive) with `b∤a, c∤a, d∤a` and
`a∤b, c∤b, d∤b` (antichain), the raw sum is `≥ 2` — the two points `k=a,b` each
contribute `1` and the rest are `≥ 0`. -/
lemma yh_ge_two {a b c d n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (han : a ≤ n) (hbn : b ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b) :
    2 ≤ (((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ))
      + 2 * (t3fun4 a b c d n : ℤ) - 2 * (t4fun4 a b c d n : ℤ) := by
  rw [yh_eq_sum]
  have hnn : ∀ k ∈ Finset.Ioc 0 n, k ∉ ({a, b} : Finset ℕ) → 0 ≤ yhRaw a b c d k :=
    fun k _ _ => yh_raw_nonneg (a ∣ k) (b ∣ k) (c ∣ k) (d ∣ k)
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ioc 0 n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_Ioc] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hRa : yhRaw a b c d a = 1 := by simp [yhRaw, hba, hca, hda]
  have hRb : yhRaw a b c d b = 1 := by simp [yhRaw, hab2, hcb, hdb]
  have hpair : ∑ k ∈ ({a, b} : Finset ℕ), yhRaw a b c d k = 2 := by
    rw [Finset.sum_pair hab, hRa, hRb]; norm_num
  linarith [hle, hpair]

/-- **Two-good-charge, step 1: `2B ≥ s + 4`.** For a primitive quadruple with `c,d`
good (charge conditions) and `a,b` as the H-pair, combining `2B = 2s−2P₂+2T₃−2T₄`,
`ΣX = s−2P₂`, `Y_H(a,b) ≥ 2`, and `X_c, X_d ≥ 1`. -/
lemma two_B_ge_s4 {a b c d n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) + (Nat.lcm d a / d) * (Nat.lcm d c / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)) :
    (sfun4 a b c d n : ℤ) + 4 ≤ 2 * ((Bgen {a, b, c, d} n).card : ℤ) := by
  have h2B := two_B_eq a b c d n
  have hcs := charge_sum4 a b c d n
  have hYH := yh_ge_two ha hb han hbn hab hba hca hda hab2 hcb hdb
  have hXc := charge_ge_one_int hc ha hb hd hcn hc_good
  have hXd := charge_ge_one_int hd ha hb hc hdn hd_good
  rw [Nat.lcm_comm c a, Nat.lcm_comm c b] at hXc
  rw [Nat.lcm_comm d a, Nat.lcm_comm d b, Nat.lcm_comm d c] at hXd
  simp only [sfun4, p2fun4, Nat.cast_add] at h2B hcs ⊢
  linarith [h2B, hcs, hYH, hXc, hXd]

/-- **Floor/mod bound.** `n·(bcd+acd+abd+abc) < (s+4)·abcd`, because
`s·abcd = n·(triples) − Σ(n%e)·(others)` and each `(n%e)·(others) < abcd`. -/
lemma s4_gt (a b c d n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (n : ℤ) * ((b : ℤ) * c * d + (a : ℤ) * c * d + (a : ℤ) * b * d + (a : ℤ) * b * c)
      < ((sfun4 a b c d n : ℤ) + 4) * ((a : ℤ) * b * c * d) := by
  have da : (a : ℤ) * ((n / a : ℕ) : ℤ) = (n : ℤ) - ((n % a : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n a; omega
  have db : (b : ℤ) * ((n / b : ℕ) : ℤ) = (n : ℤ) - ((n % b : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n b; omega
  have dc : (c : ℤ) * ((n / c : ℕ) : ℤ) = (n : ℤ) - ((n % c : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n c; omega
  have dd : (d : ℤ) * ((n / d : ℕ) : ℤ) = (n : ℤ) - ((n % d : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n d; omega
  have ma : ((n % a : ℕ) : ℤ) < a := by exact_mod_cast Nat.mod_lt n ha
  have mb : ((n % b : ℕ) : ℤ) < b := by exact_mod_cast Nat.mod_lt n hb
  have mc : ((n % c : ℕ) : ℤ) < c := by exact_mod_cast Nat.mod_lt n hc
  have md : ((n % d : ℕ) : ℤ) < d := by exact_mod_cast Nat.mod_lt n hd
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have key : (sfun4 a b c d n : ℤ) * ((a : ℤ) * b * c * d)
      = (n : ℤ) * ((b : ℤ) * c * d + (a : ℤ) * c * d + (a : ℤ) * b * d + (a : ℤ) * b * c)
        - (((n % a : ℕ) : ℤ) * ((b : ℤ) * c * d) + ((n % b : ℕ) : ℤ) * ((a : ℤ) * c * d)
          + ((n % c : ℕ) : ℤ) * ((a : ℤ) * b * d) + ((n % d : ℕ) : ℤ) * ((a : ℤ) * b * c)) := by
    simp only [sfun4, Nat.cast_add]
    linear_combination ((b : ℤ) * c * d) * da + ((a : ℤ) * c * d) * db
      + ((a : ℤ) * b * d) * dc + ((a : ℤ) * b * c) * dd
  have hpa : ((n % a : ℕ) : ℤ) * ((b : ℤ) * c * d) < (a : ℤ) * b * c * d := by
    nlinarith [ma, mul_pos (mul_pos hb' hc') hd']
  have hpb : ((n % b : ℕ) : ℤ) * ((a : ℤ) * c * d) < (a : ℤ) * b * c * d := by
    nlinarith [mb, mul_pos (mul_pos ha' hc') hd']
  have hpc : ((n % c : ℕ) : ℤ) * ((a : ℤ) * b * d) < (a : ℤ) * b * c * d := by
    nlinarith [mc, mul_pos (mul_pos ha' hb') hd']
  have hpd : ((n % d : ℕ) : ℤ) * ((a : ℤ) * b * c) < (a : ℤ) * b * c * d := by
    nlinarith [md, mul_pos (mul_pos ha' hb') hc']
  have hexp : ((sfun4 a b c d n : ℤ) + 4) * ((a : ℤ) * b * c * d)
      = (sfun4 a b c d n : ℤ) * ((a : ℤ) * b * c * d) + 4 * ((a : ℤ) * b * c * d) := by ring
  rw [hexp, key]
  linarith [hpa, hpb, hpc, hpd]

/-- **Two-good-charge proposition: `2B(n) > nS`** (integer form) for a primitive
quadruple with two good charges (here `c,d`; `a,b` the H-pair). -/
lemma two_good_charge_2BnS {a b c d n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) + (Nat.lcm d a / d) * (Nat.lcm d c / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)) :
    (n : ℤ) * ((b : ℤ) * c * d + (a : ℤ) * c * d + (a : ℤ) * b * d + (a : ℤ) * b * c)
      < 2 * ((Bgen {a, b, c, d} n).card : ℤ) * ((a : ℤ) * b * c * d) := by
  have hs4 := two_B_ge_s4 ha hb hc hd han hbn hcn hdn hab hba hca hda hab2 hcb hdb hc_good hd_good
  have hgt := s4_gt a b c d n ha hb hc hd
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have habcd : (0 : ℤ) ≤ (a : ℤ) * b * c * d := le_of_lt (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hs4 habcd
  linarith [hgt, hmul]

/-- Union bound for the quadruple: `B(m) ≤ s(m)`. -/
lemma Bgen_card_le_sfun4 {a b c d m : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Bgen {a, b, c, d} m).card ≤ sfun4 a b c d m := by
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
  simp only [mult_card, sfun4]
  omega

/-- **EP488 for a primitive quadruple with two good charges.** `n·B(m) < 2·m·B(n)`
for all `m > n ≥ max`. -/
theorem ep488_quad_two_good {a b c d n m : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hm : n < m)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) + (Nat.lcm d a / d) * (Nat.lcm d c / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)) :
    n * (Bgen {a, b, c, d} m).card < 2 * m * (Bgen {a, b, c, d} n).card := by
  -- two-good-charge lower bound at n:  n·(triples) < 2·B(n)·abcd
  have hlow := two_good_charge_2BnS ha hb hc hd han hbn hcn hdn hab hba hca hda hab2 hcb hdb
    hc_good hd_good
  -- union bound at m:  B(m) ≤ s(m), and s(m)·abcd ≤ m·(triples)
  have hBm := Bgen_card_le_sfun4 (a := a) (b := b) (c := c) (d := d) (m := m) hab hac had hbc hbd hcd
  have habcd : 0 < a * b * c * d := by positivity
  -- s(m)·abcd ≤ m·(triples), in ℕ
  have hsm : sfun4 a b c d m * (a * b * c * d) ≤ m * (b * c * d + a * c * d + a * b * d + a * b * c) := by
    have p1 : m / a * (a * b * c * d) ≤ m * (b * c * d) := by
      calc m / a * (a * b * c * d) = m / a * a * (b * c * d) := by ring
        _ ≤ m * (b * c * d) := mul_le_mul_right' (Nat.div_mul_le_self m a) (b * c * d)
    have p2 : m / b * (a * b * c * d) ≤ m * (a * c * d) := by
      calc m / b * (a * b * c * d) = m / b * b * (a * c * d) := by ring
        _ ≤ m * (a * c * d) := mul_le_mul_right' (Nat.div_mul_le_self m b) (a * c * d)
    have p3 : m / c * (a * b * c * d) ≤ m * (a * b * d) := by
      calc m / c * (a * b * c * d) = m / c * c * (a * b * d) := by ring
        _ ≤ m * (a * b * d) := mul_le_mul_right' (Nat.div_mul_le_self m c) (a * b * d)
    have p4 : m / d * (a * b * c * d) ≤ m * (a * b * c) := by
      calc m / d * (a * b * c * d) = m / d * d * (a * b * c) := by ring
        _ ≤ m * (a * b * c) := mul_le_mul_right' (Nat.div_mul_le_self m d) (a * b * c)
    simp only [sfun4]
    calc (m / a + m / b + m / c + m / d) * (a * b * c * d)
        = m / a * (a * b * c * d) + m / b * (a * b * c * d) + m / c * (a * b * c * d)
          + m / d * (a * b * c * d) := by ring
      _ ≤ m * (b * c * d) + m * (a * c * d) + m * (a * b * d) + m * (a * b * c) := by
          linarith [p1, p2, p3, p4]
      _ = m * (b * c * d + a * c * d + a * b * d + a * b * c) := by ring
  -- ℕ combination (mirror Counting.lean): B(m)·abcd ≤ m·triples, cancel abcd
  have hub : (Bgen {a, b, c, d} m).card * (a * b * c * d)
      ≤ m * (b * c * d + a * c * d + a * b * d + a * b * c) :=
    le_trans (mul_le_mul_right' hBm (a * b * c * d)) hsm
  have hlow_nat : n * (b * c * d + a * c * d + a * b * d + a * b * c)
      < 2 * (Bgen {a, b, c, d} n).card * (a * b * c * d) := by exact_mod_cast hlow
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
  have s1 : n * ((Bgen {a, b, c, d} m).card * (a * b * c * d))
      ≤ n * (m * (b * c * d + a * c * d + a * b * d + a * b * c)) := Nat.mul_le_mul_left n hub
  have s2 : m * (n * (b * c * d + a * c * d + a * b * d + a * b * c))
      < m * (2 * (Bgen {a, b, c, d} n).card * (a * b * c * d)) := mul_lt_mul_of_pos_left hlow_nat hm0
  have keyN : n * (Bgen {a, b, c, d} m).card * (a * b * c * d)
      < 2 * m * (Bgen {a, b, c, d} n).card * (a * b * c * d) := by
    calc n * (Bgen {a, b, c, d} m).card * (a * b * c * d)
        = n * ((Bgen {a, b, c, d} m).card * (a * b * c * d)) := by ring
      _ ≤ n * (m * (b * c * d + a * c * d + a * b * d + a * b * c)) := s1
      _ = m * (n * (b * c * d + a * c * d + a * b * d + a * b * c)) := by ring
      _ < m * (2 * (Bgen {a, b, c, d} n).card * (a * b * c * d)) := s2
      _ = 2 * m * (Bgen {a, b, c, d} n).card * (a * b * c * d) := by ring
  exact lt_of_mul_lt_mul_right keyN (Nat.zero_le _)

/-! ## Closing lemmas: every primitive quadruple has ≥ 2 good elements -/

/-- If the cofactor `lcm(a,y)/a = 3` (for `a < y`, `¬a∣y`), then `y = 3a/2`
(i.e. `2y = 3a`). Hence at most one `y` among the larger elements can give `3`. -/
lemma cofactor_three_eq {a y : ℕ} (ha : 0 < a) (hay : a < y) (hnay : ¬ a ∣ y)
    (h3 : Nat.lcm a y / a = 3) : 2 * y = 3 * a := by
  have hg : 0 < Nat.gcd a y := Nat.gcd_pos_of_pos_left y ha
  have hgy : Nat.gcd a y ∣ y := Nat.gcd_dvd_right a y
  have hga : Nat.gcd a y ∣ a := Nat.gcd_dvd_left a y
  have ex : Nat.lcm a y / a = y / Nat.gcd a y := by
    have h : Nat.lcm a y = a * (y / Nat.gcd a y) := by
      rw [Nat.lcm, Nat.mul_div_assoc a hgy]
    rw [h, Nat.mul_div_cancel_left _ ha]
  rw [ex] at h3
  have hy3g : y = 3 * Nat.gcd a y := by
    have h := Nat.div_mul_cancel hgy; rw [h3] at h; omega
  have h2 : 2 ≤ a / Nat.gcd a y := (ratio_bounds ha hay hnay).2
  have hlt : a / Nat.gcd a y < 3 := by
    rw [Nat.div_lt_iff_lt_mul hg]; omega
  have ha2g : a = 2 * Nat.gcd a y := by
    have hq : a / Nat.gcd a y = 2 := by omega
    have h := Nat.div_mul_cancel hga; rw [hq] at h; omega
  omega

/-- Arithmetic: for `x,y,z ≥ 3` with `x+y+z ≥ 10` (i.e. not all `= 3`),
`yz + xz + xy < xyz` (equivalently `1/x + 1/y + 1/z < 1`). -/
lemma three_prod_ineq {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) (hs : 10 ≤ x + y + z) :
    y * z + x * z + x * y < x * y * z := by
  have hx' : (3 : ℤ) ≤ x := by exact_mod_cast hx
  have hy' : (3 : ℤ) ≤ y := by exact_mod_cast hy
  have hz' : (3 : ℤ) ≤ z := by exact_mod_cast hz
  have hs' : (10 : ℤ) ≤ (x : ℤ) + y + z := by exact_mod_cast hs
  have goalZ : ((y : ℤ) * z + x * z + x * y) < (x : ℤ) * y * z := by
    nlinarith [hs', mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 3)
        (by linarith : (0:ℤ) ≤ (y:ℤ) - 3)) (by linarith : (0:ℤ) ≤ (z:ℤ) - 3),
      mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 3) (by linarith : (0:ℤ) ≤ (y:ℤ) - 3),
      mul_nonneg (by linarith : (0:ℤ) ≤ (y:ℤ) - 3) (by linarith : (0:ℤ) ≤ (z:ℤ) - 3),
      mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 3) (by linarith : (0:ℤ) ≤ (z:ℤ) - 3)]
  exact_mod_cast goalZ

/-- **Lemma A: the least element is good.** For `a < b,c,d` with `a ∤ b,c,d`
(so `a` is the smallest of a primitive quadruple), the charge of `a` is `< 1`. -/
lemma least_good {a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hac : a < c) (had : a < d)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnad : ¬ a ∣ d) (hbc : b ≠ c) :
    (Nat.lcm a c / a) * (Nat.lcm a d / a) + (Nat.lcm a b / a) * (Nat.lcm a d / a)
        + (Nat.lcm a b / a) * (Nat.lcm a c / a)
      < (Nat.lcm a b / a) * (Nat.lcm a c / a) * (Nat.lcm a d / a) := by
  have hkb : 3 ≤ Nat.lcm a b / a := (lcm_ratio ha (ha.trans hab) hab hnab).1
  have hkc : 3 ≤ Nat.lcm a c / a := (lcm_ratio ha (ha.trans hac) hac hnac).1
  have hkd : 3 ≤ Nat.lcm a d / a := (lcm_ratio ha (ha.trans had) had hnad).1
  have hbc3 : ¬ (Nat.lcm a b / a = 3 ∧ Nat.lcm a c / a = 3) := by
    rintro ⟨h1, h2⟩
    have e1 := cofactor_three_eq ha hab hnab h1
    have e2 := cofactor_three_eq ha hac hnac h2
    omega
  have hsum : 10 ≤ Nat.lcm a b / a + Nat.lcm a c / a + Nat.lcm a d / a := by
    by_contra h
    push_neg at h
    exact hbc3 ⟨by omega, by omega⟩
  exact three_prod_ineq hkb hkc hkd hsum

/-- If three cofactors `q,u,v ≥ 3` satisfy the bad inequality `quv ≤ uv+qv+qu`
(i.e. `1/q+1/u+1/v ≥ 1`), then all three equal `3`. -/
lemma three_all_three {q u v : ℕ} (hq : 3 ≤ q) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (h : q * u * v ≤ u * v + q * v + q * u) : q = 3 ∧ u = 3 ∧ v = 3 := by
  have hq3 : q ≤ 3 := by
    by_contra hq4
    have h10 : 10 ≤ q + u + v := by omega
    have := three_prod_ineq hq hu hv h10
    omega
  have hu3 : u ≤ 3 := by
    by_contra hu4
    have h10 : 10 ≤ q + u + v := by omega
    have := three_prod_ineq hq hu hv h10
    omega
  have hv3 : v ≤ 3 := by
    by_contra hv4
    have h10 : 10 ≤ q + u + v := by omega
    have := three_prod_ineq hq hu hv h10
    omega
  exact ⟨by omega, by omega, by omega⟩

/-- **`b` bad forces `q = 2`.** If `b` (2nd smallest) is bad, its `a`-cofactor
`lcm(a,b)/b = 2`: else `q ≥ 3` forces `u=v=3`, giving `2c=3b=2d`, so `c=d`. -/
lemma b_bad_forces_q_two {a b c d : ℕ} (hb : 0 < b) (hab : a < b) (hbc : b < c) (hbd : b < d)
    (hcd : c ≠ d) (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d)
    (hq : 2 ≤ Nat.lcm a b / b) (hu : 3 ≤ Nat.lcm b c / b) (hv : 3 ≤ Nat.lcm b d / b)
    (hbad : (Nat.lcm a b / b) * (Nat.lcm b c / b) * (Nat.lcm b d / b)
      ≤ (Nat.lcm b c / b) * (Nat.lcm b d / b) + (Nat.lcm a b / b) * (Nat.lcm b d / b)
        + (Nat.lcm a b / b) * (Nat.lcm b c / b)) :
    Nat.lcm a b / b = 2 := by
  by_contra hq2
  have hq3 : 3 ≤ Nat.lcm a b / b := by omega
  obtain ⟨_, hu3, hv3⟩ := three_all_three hq3 hu hv hbad
  have e1 := cofactor_three_eq hb hbc hnbc hu3
  have e2 := cofactor_three_eq hb hbd hnbd hv3
  omega

/-- a-term for the `c/b = 3/2` case: with `q=2` (`a = 2·gcd(a,b)`) and `2c=3b`,
the a-cofactor `p = a/gcd(a,c) = 4` (parity chain: `m` odd ⟹ `g` even ⟹ `p=4`). -/
lemma aterm_case32 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hnab : ¬ a ∣ b)
    (hq : a = 2 * Nat.gcd a b) (h32 : 2 * c = 3 * b) :
    a / Nat.gcd a c = 4 := by
  set g := Nat.gcd a b with hgdef
  obtain ⟨m, hm⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha
  -- m is odd: else a = 2·gcd ∣ gcd·m = b
  have hmodd : m % 2 = 1 := by
    by_contra h
    obtain ⟨m', rfl⟩ : 2 ∣ m := by omega
    exact hnab ⟨m', by rw [hq, hm]; ring⟩
  -- 2 | g: 2c = 3·(gcd·m); 3 and m coprime to 2 ⟹ gcd even
  have h2g : 2 ∣ g := by
    have h2bc : (2 : ℕ) ∣ 3 * (g * m) := by
      have heq : 3 * (g * m) = 2 * c := by rw [← hm]; omega
      rw [heq]; exact dvd_mul_right 2 c
    have hc3 : Nat.Coprime 2 3 := by decide
    have hcm : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    exact Nat.Coprime.dvd_of_dvd_mul_right hcm (Nat.Coprime.dvd_of_dvd_mul_left hc3 h2bc)
  obtain ⟨g1, hg1⟩ := h2g
  have hg1pos : 0 < g1 := by rw [hg1] at hg0; omega
  have ha4 : a = g1 * 4 := by rw [hq, hg1]; ring
  -- gcd(a,c) = g1·gcd(4,3m) = g1
  have hac : Nat.gcd a c = g1 := by
    have hc3 : c = g1 * (3 * m) := by
      have h2 : 2 * c = 2 * (g1 * (3 * m)) := by rw [h32, hm, hg1]; ring
      omega
    rw [ha4, hc3, Nat.gcd_mul_left]
    have hco : Nat.gcd 4 (3 * m) = 1 := by
      have c4 : Nat.Coprime 4 (3 * m) := by
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4]
        exact Nat.Coprime.pow_left 2 ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))
      exact c4
    rw [hco, Nat.mul_one]
  rw [hac, ha4, Nat.mul_div_cancel_left 4 hg1pos]

/-- From `k*x = l*y` with `k,l` coprime and `0 < l`, extract the common scale
`t` with `x = l*t`, `y = k*t`. (`t = gcd x y`.) -/
lemma coprime_ratio {k l x y : ℕ} (hl : 0 < l) (hco : Nat.Coprime k l)
    (h : k * x = l * y) : ∃ t, x = l * t ∧ y = k * t := by
  have hlx : l ∣ x := Nat.Coprime.dvd_of_dvd_mul_left hco.symm ⟨y, h⟩
  obtain ⟨t, rfl⟩ := hlx
  have hy : k * t = y := Nat.eq_of_mul_eq_mul_left hl (by rw [← h]; ring)
  exact ⟨t, rfl, hy.symm⟩

/-- Reduced-ratio cofactors: if `k*x = l*y` with `k,l` coprime, `0 < l`, `0 < x`,
then `x/gcd(x,y) = l` and `y/gcd(x,y) = k`. -/
lemma cof_of_ratio {k l x y : ℕ} (hl : 0 < l) (hxpos : 0 < x)
    (hco : Nat.Coprime k l) (h : k * x = l * y) :
    x / Nat.gcd x y = l ∧ y / Nat.gcd x y = k := by
  obtain ⟨t, hx, hy⟩ := coprime_ratio hl hco h
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, Nat.mul_zero] at hx; omega
    · exact h0
  have hlk : Nat.gcd l k = 1 := hco.symm
  have hg : Nat.gcd x y = t := by
    rw [hx, hy, Nat.gcd_mul_right, hlk, Nat.one_mul]
  refine ⟨?_, ?_⟩
  · rw [hg, hx, Nat.mul_comm l t]; exact Nat.mul_div_cancel_left l ht
  · rw [hg, hy, Nat.mul_comm k t]; exact Nat.mul_div_cancel_left k ht

/-- `lcm(x,y)/x = y/gcd(x,y)` (equality form, for `0 < x`). -/
lemma lcm_div_self {x y : ℕ} (hx : 0 < x) : Nat.lcm x y / x = y / Nat.gcd x y := by
  have hgy : Nat.gcd x y ∣ y := Nat.gcd_dvd_right x y
  have h : Nat.lcm x y = x * (y / Nat.gcd x y) := by
    rw [Nat.lcm, Nat.mul_div_assoc x hgy]
  rw [h, Nat.mul_div_cancel_left _ hx]

/-- The `c`-cofactor against another element `z`, read off a reduced ratio
`k*z = l*c` with `k,l` coprime: `lcm(c,z)/c = l`. -/
lemma cof_c {c z k l : ℕ} (hc : 0 < c) (hz : 0 < z) (hl : 0 < l)
    (hco : Nat.Coprime k l) (h : k * z = l * c) : Nat.lcm c z / c = l := by
  rw [lcm_div_self hc, Nat.gcd_comm c z]
  exact (cof_of_ratio hl hz hco h).1

/-- **Case 1** (`c/b = 3/2`, `d/b = 5/3`): `charge(c) ≤ 1/4 + 1/2 + 1/10 < 1`. -/
lemma c_good_case1 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnab : ¬ a ∣ b) (hq : a = 2 * Nat.gcd a b)
    (h32 : 2 * c = 3 * b) (h53 : 3 * d = 5 * b) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  have e1 : 3 * b = 2 * c := by omega
  have hcb : Nat.lcm c b / c = 2 := cof_c hc hb (by norm_num) (by decide) e1
  have e2 : 9 * d = 10 * c := by omega
  have hcd : Nat.lcm c d / c = 10 := cof_c hc hd (by norm_num) (by decide) e2
  have hca : Nat.lcm c a / c = 4 := by
    rw [lcm_div_self hc, Nat.gcd_comm c a]; exact aterm_case32 ha hb hnab hq h32
  rw [hcb, hcd, hca]; omega

/-- **Case 2** (`c/b = 3/2`, `d/b = 5/2`): `charge(c) ≤ 1/4 + 1/2 + 1/5 < 1`. -/
lemma c_good_case2 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnab : ¬ a ∣ b) (hq : a = 2 * Nat.gcd a b)
    (h32 : 2 * c = 3 * b) (h52 : 2 * d = 5 * b) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  have e1 : 3 * b = 2 * c := by omega
  have hcb : Nat.lcm c b / c = 2 := cof_c hc hb (by norm_num) (by decide) e1
  have e2 : 3 * d = 5 * c := by omega
  have hcd : Nat.lcm c d / c = 5 := cof_c hc hd (by norm_num) (by decide) e2
  have hca : Nat.lcm c a / c = 4 := by
    rw [lcm_div_self hc, Nat.gcd_comm c a]; exact aterm_case32 ha hb hnab hq h32
  rw [hcb, hcd, hca]; omega

/-- **Case 3** (`c/b = 4/3`, `d/b = 3/2`): `charge(c) ≤ 1/2 + 1/3 + 1/9 < 1`
(free `a`-term `p ≥ 2`). -/
lemma c_good_case3 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : a < c) (hnac : ¬ a ∣ c)
    (h43 : 3 * c = 4 * b) (h32 : 2 * d = 3 * b) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  have e1 : 4 * b = 3 * c := by omega
  have hcb : Nat.lcm c b / c = 3 := cof_c hc hb (by norm_num) (by decide) e1
  have e2 : 8 * d = 9 * c := by omega
  have hcd : Nat.lcm c d / c = 9 := cof_c hc hd (by norm_num) (by decide) e2
  have hP : 2 ≤ Nat.lcm c a / c := by rw [Nat.lcm_comm c a]; exact (lcm_ratio ha hc hac hnac).2
  rw [hcb, hcd]; omega

/-- **Case 4** (`c/b = 5/4`, `d/b = 3/2`): `charge(c) ≤ 1/2 + 1/4 + 1/6 < 1`. -/
lemma c_good_case4 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : a < c) (hnac : ¬ a ∣ c)
    (h54 : 4 * c = 5 * b) (h32 : 2 * d = 3 * b) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  have e1 : 5 * b = 4 * c := by omega
  have hcb : Nat.lcm c b / c = 4 := cof_c hc hb (by norm_num) (by decide) e1
  have e2 : 5 * d = 6 * c := by omega
  have hcd : Nat.lcm c d / c = 6 := cof_c hc hd (by norm_num) (by decide) e2
  have hP : 2 ≤ Nat.lcm c a / c := by rw [Nat.lcm_comm c a]; exact (lcm_ratio ha hc hac hnac).2
  rw [hcb, hcd]; omega

/-- **Case 5** (`c/b = 6/5`, `d/b = 3/2`): `charge(c) ≤ 1/2 + 1/5 + 1/5 < 1`. -/
lemma c_good_case5 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : a < c) (hnac : ¬ a ∣ c)
    (h65 : 5 * c = 6 * b) (h32 : 2 * d = 3 * b) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  have e1 : 6 * b = 5 * c := by omega
  have hcb : Nat.lcm c b / c = 5 := cof_c hc hb (by norm_num) (by decide) e1
  have e2 : 4 * d = 5 * c := by omega
  have hcd : Nat.lcm c d / c = 5 := cof_c hc hd (by norm_num) (by decide) e2
  have hP : 2 ≤ Nat.lcm c a / c := by rw [Nat.lcm_comm c a]; exact (lcm_ratio ha hc hac hnac).2
  rw [hcb, hcd]; omega

/-- **Five-shape enumeration under `b` bad** (with `q = 2` already used, so the
charge condition is `uv ≤ 2u + 2v`, `u = c/gcd(b,c)`, `v = d/gcd(b,d)`). The
reduced ratios `c/b`, `d/b` must be one of the five listed pairs. -/
lemma b_bad_five_shapes {b c d : ℕ} (hb : 0 < b) (hbc : b < c) (hbd : b < d) (hcd : c < d)
    (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d)
    (hbad : (Nat.lcm b c / b) * (Nat.lcm b d / b)
        ≤ 2 * (Nat.lcm b c / b) + 2 * (Nat.lcm b d / b)) :
    (2 * c = 3 * b ∧ 3 * d = 5 * b) ∨ (2 * c = 3 * b ∧ 2 * d = 5 * b)
      ∨ (3 * c = 4 * b ∧ 2 * d = 3 * b) ∨ (4 * c = 5 * b ∧ 2 * d = 3 * b)
      ∨ (5 * c = 6 * b ∧ 2 * d = 3 * b) := by
  have hc0 : 0 < c := hb.trans hbc
  have hd0 : 0 < d := hb.trans hbd
  have hg1 : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left c hb
  have hg2 : 0 < Nat.gcd b d := Nat.gcd_pos_of_pos_left d hb
  obtain ⟨r, hbr⟩ : Nat.gcd b c ∣ b := Nat.gcd_dvd_left b c
  obtain ⟨u, hcu⟩ : Nat.gcd b c ∣ c := Nat.gcd_dvd_right b c
  obtain ⟨s, hbs⟩ : Nat.gcd b d ∣ b := Nat.gcd_dvd_left b d
  obtain ⟨v, hdv⟩ : Nat.gcd b d ∣ d := Nat.gcd_dvd_right b d
  have hbgr : b / Nat.gcd b c = r := Nat.div_eq_of_eq_mul_right hg1 hbr
  have hcgu : c / Nat.gcd b c = u := Nat.div_eq_of_eq_mul_right hg1 hcu
  have hbgs : b / Nat.gcd b d = s := Nat.div_eq_of_eq_mul_right hg2 hbs
  have hdgv : d / Nat.gcd b d = v := Nat.div_eq_of_eq_mul_right hg2 hdv
  have hUu : Nat.lcm b c / b = u := (lcm_div_self hb).trans hcgu
  have hVv : Nat.lcm b d / b = v := (lcm_div_self hb).trans hdgv
  have hlcmbc_c : Nat.lcm b c / c = r := by
    have h1 : Nat.lcm b c / c = b / Nat.gcd b c := by
      rw [Nat.lcm_comm b c, lcm_div_self hc0, Nat.gcd_comm c b]
    rw [h1, hbgr]
  have hlcmbd_d : Nat.lcm b d / d = s := by
    have h1 : Nat.lcm b d / d = b / Nat.gcd b d := by
      rw [Nat.lcm_comm b d, lcm_div_self hd0, Nat.gcd_comm d b]
    rw [h1, hbgs]
  have hu3 : 3 ≤ u := by have := (lcm_ratio hb hc0 hbc hnbc).1; rwa [hUu] at this
  have hv3 : 3 ≤ v := by have := (lcm_ratio hb hd0 hbd hnbd).1; rwa [hVv] at this
  have hr2 : 2 ≤ r := by have := (lcm_ratio hb hc0 hbc hnbc).2; rwa [hlcmbc_c] at this
  have hs2 : 2 ≤ s := by have := (lcm_ratio hb hd0 hbd hnbd).2; rwa [hlcmbd_d] at this
  rw [hUu, hVv] at hbad
  have hu6 : u ≤ 6 := by nlinarith [hbad, hu3, hv3]
  have hv6 : v ≤ 6 := by nlinarith [hbad, hu3, hv3]
  have hru_lt : r < u := by
    have h : Nat.gcd b c * r < Nat.gcd b c * u := by rw [← hbr, ← hcu]; exact hbc
    exact Nat.lt_of_mul_lt_mul_left h
  have hsv_lt : s < v := by
    have h : Nat.gcd b d * s < Nat.gcd b d * v := by rw [← hbs, ← hdv]; exact hbd
    exact Nat.lt_of_mul_lt_mul_left h
  have hru : Nat.Coprime r u := by
    have h := Nat.coprime_div_gcd_div_gcd hg1
    rwa [hbgr, hcgu] at h
  have hsv : Nat.Coprime s v := by
    have h := Nat.coprime_div_gcd_div_gcd hg2
    rwa [hbgs, hdgv] at h
  have hord : u * s < v * r := by
    have hcb_eq : c * b = u * s * (Nat.gcd b c * Nat.gcd b d) := by
      rw [show u * s * (Nat.gcd b c * Nat.gcd b d)
            = (Nat.gcd b c * u) * (Nat.gcd b d * s) from by ring, ← hcu, ← hbs]
    have hdb_eq : d * b = v * r * (Nat.gcd b c * Nat.gcd b d) := by
      rw [show v * r * (Nat.gcd b c * Nat.gcd b d)
            = (Nat.gcd b d * v) * (Nat.gcd b c * r) from by ring, ← hdv, ← hbr]
    have hlt : c * b < d * b := Nat.mul_lt_mul_of_pos_right hcd hb
    rw [hcb_eq, hdb_eq] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  interval_cases u <;> interval_cases v <;> interval_cases r <;> interval_cases s <;>
    first
      | omega
      | exact absurd hru (by decide)
      | exact absurd hsv (by decide)

/-- **`b` bad ⟹ `c` good.** In a primitive quadruple `a<b<c<d`, if `b` is bad
(and `q = 2`, which `b_bad_forces_q_two` guarantees), then `c` has good charge. -/
lemma c_good_of_b_bad {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a < b) (hbc : b < c) (hbd : b < d) (hcd : c < d)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d)
    (hq : a = 2 * Nat.gcd a b)
    (hbad : (Nat.lcm b c / b) * (Nat.lcm b d / b)
        ≤ 2 * (Nat.lcm b c / b) + 2 * (Nat.lcm b d / b)) :
    (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
      + (Nat.lcm c a / c) * (Nat.lcm c b / c)
      < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) := by
  rcases b_bad_five_shapes hb hbc hbd hcd hnbc hnbd hbad with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact c_good_case1 ha hb hc hd hnab hq h1 h2
  · exact c_good_case2 ha hb hc hd hnab hq h1 h2
  · exact c_good_case3 ha hb hc hd (hab.trans hbc) hnac h1 h2
  · exact c_good_case4 ha hb hc hd (hab.trans hbc) hnac h1 h2
  · exact c_good_case5 ha hb hc hd (hab.trans hbc) hnac h1 h2

/-- Bridge: `lcm(a,b)/b = 2` gives `a = 2·gcd(a,b)`. -/
lemma q_eq_two_of_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Nat.lcm a b / b = 2) : a = 2 * Nat.gcd a b := by
  have hid : Nat.lcm a b / b = a / Nat.gcd a b := by
    rw [Nat.lcm_comm, lcm_div_self hb, Nat.gcd_comm b a]
  rw [hid] at h
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨k, hk⟩ : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  have hk2 : k = 2 := by
    have hkc : Nat.gcd a b * k / Nat.gcd a b = 2 := by rw [← hk]; exact h
    rwa [Nat.mul_div_cancel_left k hg] at hkc
  rw [hk2] at hk; omega

/-- **`a` and `b` good ⟹ EP488 for the quadruple** (good pair relabelled into the
`(c,d)` slots of `ep488_quad_two_good`). -/
lemma ep488_quad_ab_good {a b c d n m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnad : ¬ a ∣ d)
    (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d) (hncd : ¬ c ∣ d)
    (hn : d ≤ n) (hm : n < m)
    (haG : (Nat.lcm a c / a) * (Nat.lcm a d / a) + (Nat.lcm a b / a) * (Nat.lcm a d / a)
             + (Nat.lcm a b / a) * (Nat.lcm a c / a)
           < (Nat.lcm a b / a) * (Nat.lcm a c / a) * (Nat.lcm a d / a))
    (hbG : (Nat.lcm b c / b) * (Nat.lcm b d / b) + (Nat.lcm b a / b) * (Nat.lcm b d / b)
             + (Nat.lcm b a / b) * (Nat.lcm b c / b)
           < (Nat.lcm b a / b) * (Nat.lcm b c / b) * (Nat.lcm b d / b)) :
    n * (Bgen {a, b, c, d} m).card < 2 * m * (Bgen {a, b, c, d} n).card := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hd : 0 < d := hc.trans hcd
  have hbd : b < d := hbc.trans hcd
  have hac : a < c := hab.trans hbc
  have had : a < d := hac.trans hcd
  have hset : ({a, b, c, d} : Finset ℕ) = {c, d, a, b} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset]
  have ndc : ¬ d ∣ c := fun h => absurd (Nat.le_of_dvd hc h) (not_le.mpr hcd)
  exact ep488_quad_two_good (a := c) (b := d) (c := a) (d := b)
    hc hd ha hb
    (by omega) hn (by omega) (by omega) hm
    (ne_of_lt hcd) (ne_of_lt hac).symm (ne_of_lt hbc).symm (ne_of_lt had).symm
    (ne_of_lt hbd).symm (ne_of_lt hab)
    ndc hnac hnbc hncd hnad hnbd
    (by have h := haG; ring_nf at h ⊢; exact h)
    (by have h := hbG; ring_nf at h ⊢; exact h)

/-- **`a` and `c` good ⟹ EP488 for the quadruple** (good pair relabelled into the
`(c,d)` slots of `ep488_quad_two_good`; here the H-pair is `b,d`). -/
lemma ep488_quad_ac_good {a b c d n m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnad : ¬ a ∣ d)
    (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d) (hncd : ¬ c ∣ d)
    (hn : d ≤ n) (hm : n < m)
    (haG : (Nat.lcm a c / a) * (Nat.lcm a d / a) + (Nat.lcm a b / a) * (Nat.lcm a d / a)
             + (Nat.lcm a b / a) * (Nat.lcm a c / a)
           < (Nat.lcm a b / a) * (Nat.lcm a c / a) * (Nat.lcm a d / a))
    (hcG : (Nat.lcm c b / c) * (Nat.lcm c d / c) + (Nat.lcm c a / c) * (Nat.lcm c d / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c)
           < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c)) :
    n * (Bgen {a, b, c, d} m).card < 2 * m * (Bgen {a, b, c, d} n).card := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hd : 0 < d := hc.trans hcd
  have hbd : b < d := hbc.trans hcd
  have hac : a < c := hab.trans hbc
  have had : a < d := hac.trans hcd
  have hset : ({a, b, c, d} : Finset ℕ) = {b, d, a, c} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset]
  have ndb : ¬ d ∣ b := fun h => absurd (Nat.le_of_dvd hb h) (not_le.mpr hbd)
  have ncb : ¬ c ∣ b := fun h => absurd (Nat.le_of_dvd hb h) (not_le.mpr hbc)
  exact ep488_quad_two_good (a := b) (b := d) (c := a) (d := c)
    hb hd ha hc
    (by omega) hn (by omega) (by omega) hm
    (ne_of_lt hbd) (ne_of_lt hab).symm (ne_of_lt hbc) (ne_of_lt had).symm
    (ne_of_lt hcd).symm (ne_of_lt hac)
    ndb hnab ncb hnbd hnad hncd
    (by have h := haG; ring_nf at h ⊢; exact h)
    (by have h := hcG; ring_nf at h ⊢; exact h)

/-- **EP488 for an explicitly sorted primitive quadruple** (`Bgen` form). Every
primitive quadruple has at least two good charges (`a` always, plus `b` or `c`),
which the two-good-charge proposition converts into `n·B(m) < 2·m·B(n)`. -/
lemma ep488_quad_prim {a b c d n m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnad : ¬ a ∣ d)
    (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d) (hncd : ¬ c ∣ d)
    (hn : d ≤ n) (hm : n < m) :
    n * (Bgen {a, b, c, d} m).card < 2 * m * (Bgen {a, b, c, d} n).card := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hd : 0 < d := hc.trans hcd
  have hbd : b < d := hbc.trans hcd
  have hac : a < c := hab.trans hbc
  have had : a < d := hac.trans hcd
  have haG := least_good ha hab hac had hnab hnac hnad (ne_of_lt hbc)
  by_cases hGb : (Nat.lcm b c / b) * (Nat.lcm b d / b) + (Nat.lcm b a / b) * (Nat.lcm b d / b)
             + (Nat.lcm b a / b) * (Nat.lcm b c / b)
           < (Nat.lcm b a / b) * (Nat.lcm b c / b) * (Nat.lcm b d / b)
  · exact ep488_quad_ab_good ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd hn hm haG hGb
  · push_neg at hGb
    rw [Nat.lcm_comm b a] at hGb
    have hQ2 := (lcm_ratio ha hb hab hnab).2
    have hU3 := (lcm_ratio hb hc hbc hnbc).1
    have hV3 := (lcm_ratio hb hd hbd hnbd).1
    have hqeq := b_bad_forces_q_two hb hab hbc hbd (ne_of_lt hcd) hnbc hnbd hQ2 hU3 hV3 hGb
    have hq_eq := q_eq_two_of_lcm ha hb hqeq
    rw [hqeq] at hGb
    have hbad2 : (Nat.lcm b c / b) * (Nat.lcm b d / b)
        ≤ 2 * (Nat.lcm b c / b) + 2 * (Nat.lcm b d / b) := by nlinarith [hGb]
    have hcG := c_good_of_b_bad ha hb hc hd hab hbc hbd hcd hnab hnac hnbc hnbd hq_eq hbad2
    exact ep488_quad_ac_good ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd hn hm haG hcG

/-- **EP488 for any positive `∣`-antichain `P` of size ≤ 4.** Extends
`ep488_primitive` (which covers `≤ 3`) with the quadruple case. -/
theorem ep488_primitive_le_four {P : Finset ℕ} (hpos : ∀ a ∈ P, 0 < a)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ x ∣ y)
    (hcard : P.card ≤ 4) (hne : P.Nonempty)
    {n m : ℕ} (hn : ∀ a ∈ P, a ≤ n) (hm : n < m) :
    n * (Bgen P m).card < 2 * m * (Bgen P n).card := by
  rcases (by omega : P.card ≤ 3 ∨ P.card = 4) with h3 | h4
  · exact ep488_primitive hpos hanti h3 hne hn hm
  · -- card = 4: extract a < b < c < d with {a,b,c,d} = P
    set a := P.min' hne with ha_def
    set d := P.max' hne with hd_def
    have hamem : a ∈ P := P.min'_mem hne
    have hdmem : d ∈ P := P.max'_mem hne
    have had : a < d := Finset.min'_lt_max'_of_card P (by omega)
    have hd_in1 : d ∈ P.erase a := Finset.mem_erase.mpr ⟨(ne_of_lt had).symm, hdmem⟩
    have hcard2 : ((P.erase a).erase d).card = 2 := by
      have e1 := Finset.card_erase_of_mem hd_in1
      have e2 := Finset.card_erase_of_mem hamem
      omega
    have hP2ne : ((P.erase a).erase d).Nonempty := by rw [← Finset.card_pos]; omega
    set b := ((P.erase a).erase d).min' hP2ne with hb_def
    set c := ((P.erase a).erase d).max' hP2ne with hc_def
    have hbmem2 : b ∈ (P.erase a).erase d := Finset.min'_mem _ hP2ne
    have hcmem2 : c ∈ (P.erase a).erase d := Finset.max'_mem _ hP2ne
    have hbc : b < c := Finset.min'_lt_max'_of_card _ (by omega)
    have hb_in1 : b ∈ P.erase a := (Finset.mem_erase.mp hbmem2).2
    have hbmem : b ∈ P := (Finset.mem_erase.mp hb_in1).2
    have hba_ne : b ≠ a := (Finset.mem_erase.mp hb_in1).1
    have hbd_ne : b ≠ d := (Finset.mem_erase.mp hbmem2).1
    have hc_in1 : c ∈ P.erase a := (Finset.mem_erase.mp hcmem2).2
    have hcmem : c ∈ P := (Finset.mem_erase.mp hc_in1).2
    have hcd_ne : c ≠ d := (Finset.mem_erase.mp hcmem2).1
    have hab : a < b := lt_of_le_of_ne (Finset.min'_le _ b hbmem) (fun h => hba_ne h.symm)
    have hcd : c < d := lt_of_le_of_ne (Finset.le_max' _ c hcmem) hcd_ne
    have hac : a < c := hab.trans hbc
    have hbd : b < d := hbc.trans hcd
    have hcard4' : ({a, b, c, d} : Finset ℕ).card = 4 :=
      Finset.card_eq_four.2 ⟨a, b, c, d, ne_of_lt hab, ne_of_lt hac, ne_of_lt had,
        ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hcd, rfl⟩
    have hsub : ({a, b, c, d} : Finset ℕ) ⊆ P := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hamem
      · exact hbmem
      · exact hcmem
      · exact hdmem
    have hset : ({a, b, c, d} : Finset ℕ) = P :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard4']; omega)
    rw [← hset]
    exact ep488_quad_prim (hpos a hamem) hab hbc hcd
      (hanti a hamem b hbmem (ne_of_lt hab))
      (hanti a hamem c hcmem (ne_of_lt hac))
      (hanti a hamem d hdmem (ne_of_lt had))
      (hanti b hbmem c hcmem (ne_of_lt hbc))
      (hanti b hbmem d hdmem (ne_of_lt hbd))
      (hanti c hcmem d hdmem (ne_of_lt hcd))
      (hn d hdmem) hm

/-- **EP488 for every finite `A` of positive integers whose primitive core has
size ≤ 4.** The `|core| = 4` case is not established in Chojecki's paper: his route
to size 4 runs through the pair-vs-two-tail case of his *open* Conjecture 4.8
(pair-tail split doubling), which §7 lists as the "first unresolved" problem. This
proves the assembled #488 inequality for `|core| ≤ 4` *directly* via the flat charge
method — a weaker, different statement than Conjecture 4.8's per-block split
doubling. So it closes a case the public record leaves open, but is NOT a proof of
Conjecture 4.8. Method classical (Heilbronn–Rohrbach); novelty pending referee. -/
theorem ep488_core_le_four {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a)
    (hAne : A.Nonempty) (hcore : (core A).card ≤ 4)
    {n m : ℕ} (hn : ∀ a ∈ A, a ≤ n) (hm : n < m) :
    n * (Bgen A m).card < 2 * m * (Bgen A n).card := by
  rw [Bgen_core_eq hpos m, Bgen_core_eq hpos n]
  have hcne : (core A).Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb, _⟩ := exists_core_dvd hpos ha
    exact ⟨b, hb⟩
  exact ep488_primitive_le_four (fun a ha => core_pos hpos ha)
    (fun x hx y hy hxy => core_antichain hx hy hxy)
    hcore hcne (fun a ha => hn a (core_subset A ha)) hm

end Erdos488
