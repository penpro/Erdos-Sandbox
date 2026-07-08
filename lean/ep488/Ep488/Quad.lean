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

end Erdos488
