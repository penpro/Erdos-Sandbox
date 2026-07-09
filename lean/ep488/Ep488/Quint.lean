import Ep488.Quad

/-!
# Toward `|primitive core| = 5` — the three-good-charge proposition (PARTIAL)

Mechanical 4→5 lift of `Ep488.Quad`. Proves the analytic engine for quintuples:
a primitive quintuple with **at least three good charges** satisfies #488.

**This is a coverage result, not a closure.** Codex's `sweep-quint-cert` shows the
three-good regime covers `43,290,285 / 43,291,981` primitive quintuples (entries
≤ 100); it leaves the `≤ 2`-good residual (canonically `{4,6,10,14,15}`, which has
only one good charge) entirely untouched. That residual is an unbounded family and
its uniform handling — equivalently, whether `2B(n) > nS` holds for *every*
primitive quintuple — needs a genuinely new idea (the naive 2-good rescue is dead:
the pointwise weight is `−1` at `p=3, q=0`). See `../../quintuple_charge_notes.md`.

This file starts with the arithmetic foundation: the 5-set inclusion–exclusion
`B = s − P₂ + T₃ − T₄ + T₅`, the single genuinely-new brick.
-/

namespace Erdos488

open Finset

/-- **Pointwise 5-event inclusion–exclusion** (in `ℤ`): the union indicator equals
the alternating sum singles − pairs + triples − quads + quint. `decide`-style over
the `2⁵ = 32` boolean cases. -/
lemma ie5_bool (a b c d e : Prop)
    [Decidable a] [Decidable b] [Decidable c] [Decidable d] [Decidable e] :
    (if a ∨ b ∨ c ∨ d ∨ e then (1 : ℤ) else 0)
      = ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + (if d then 1 else 0) + (if e then (1:ℤ) else 0))
        - ((if a ∧ b then 1 else 0) + (if a ∧ c then 1 else 0) + (if a ∧ d then 1 else 0)
          + (if a ∧ e then 1 else 0) + (if b ∧ c then 1 else 0) + (if b ∧ d then 1 else 0)
          + (if b ∧ e then 1 else 0) + (if c ∧ d then 1 else 0) + (if c ∧ e then 1 else 0)
          + (if d ∧ e then (1:ℤ) else 0))
        + ((if a ∧ b ∧ c then 1 else 0) + (if a ∧ b ∧ d then 1 else 0)
          + (if a ∧ b ∧ e then 1 else 0) + (if a ∧ c ∧ d then 1 else 0)
          + (if a ∧ c ∧ e then 1 else 0) + (if a ∧ d ∧ e then 1 else 0)
          + (if b ∧ c ∧ d then 1 else 0) + (if b ∧ c ∧ e then 1 else 0)
          + (if b ∧ d ∧ e then 1 else 0) + (if c ∧ d ∧ e then (1:ℤ) else 0))
        - ((if a ∧ b ∧ c ∧ d then 1 else 0) + (if a ∧ b ∧ c ∧ e then 1 else 0)
          + (if a ∧ b ∧ d ∧ e then 1 else 0) + (if a ∧ c ∧ d ∧ e then 1 else 0)
          + (if b ∧ c ∧ d ∧ e then (1:ℤ) else 0))
        + (if a ∧ b ∧ c ∧ d ∧ e then (1:ℤ) else 0) := by
  by_cases a <;> by_cases b <;> by_cases c <;> by_cases d <;> by_cases e <;> simp_all

/-- `lcm(x,y,z,w,v) ∣ k ↔ x∣k ∧ … ∧ v∣k`, as an indicator equality. -/
lemma lcm5_ind (x y z w v k : ℕ) :
    (if Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm x y) z) w) v ∣ k then (1 : ℤ) else 0)
      = if x ∣ k ∧ y ∣ k ∧ z ∣ k ∧ w ∣ k ∧ v ∣ k then 1 else 0 := by
  have h : (Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm x y) z) w) v ∣ k)
      ↔ (x ∣ k ∧ y ∣ k ∧ z ∣ k ∧ w ∣ k ∧ v ∣ k) := by
    constructor
    · intro hd
      have h3 : Nat.lcm (Nat.lcm (Nat.lcm x y) z) w ∣ k := (Nat.dvd_lcm_left _ _).trans hd
      have h2 : Nat.lcm (Nat.lcm x y) z ∣ k := (Nat.dvd_lcm_left _ _).trans h3
      have h1 : Nat.lcm x y ∣ k := (Nat.dvd_lcm_left _ _).trans h2
      exact ⟨(Nat.dvd_lcm_left x y).trans h1, (Nat.dvd_lcm_right x y).trans h1,
        (Nat.dvd_lcm_right _ _).trans h2, (Nat.dvd_lcm_right _ _).trans h3,
        (Nat.dvd_lcm_right _ _).trans hd⟩
    · rintro ⟨hx, hy, hz, hw, hv⟩
      exact Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd hx hy) hz) hw) hv
  simp only [h]

/-- `s(n) = Σ ⌊n/·⌋` over the 5 singletons. -/
def sfun5 (a b c d e n : ℕ) : ℕ := n / a + n / b + n / c + n / d + n / e

/-- `P₂(n)` = sum of `⌊n/lcm⌋` over the 10 pairs. -/
def p2fun5 (a b c d e n : ℕ) : ℕ :=
  n / Nat.lcm a b + n / Nat.lcm a c + n / Nat.lcm a d + n / Nat.lcm a e
    + n / Nat.lcm b c + n / Nat.lcm b d + n / Nat.lcm b e
    + n / Nat.lcm c d + n / Nat.lcm c e + n / Nat.lcm d e

/-- `T₃(n)` = sum of `⌊n/lcm⌋` over the 10 triples (fixed nested-lcm order). -/
def t3fun5 (a b c d e n : ℕ) : ℕ :=
  n / Nat.lcm (Nat.lcm a b) c + n / Nat.lcm (Nat.lcm a b) d + n / Nat.lcm (Nat.lcm a b) e
    + n / Nat.lcm (Nat.lcm a c) d + n / Nat.lcm (Nat.lcm a c) e + n / Nat.lcm (Nat.lcm a d) e
    + n / Nat.lcm (Nat.lcm b c) d + n / Nat.lcm (Nat.lcm b c) e + n / Nat.lcm (Nat.lcm b d) e
    + n / Nat.lcm (Nat.lcm c d) e

/-- `T₄(n)` = sum of `⌊n/lcm⌋` over the 5 quadruples. -/
def t4fun5 (a b c d e n : ℕ) : ℕ :=
  n / Nat.lcm (Nat.lcm (Nat.lcm a b) c) d + n / Nat.lcm (Nat.lcm (Nat.lcm a b) c) e
    + n / Nat.lcm (Nat.lcm (Nat.lcm a b) d) e + n / Nat.lcm (Nat.lcm (Nat.lcm a c) d) e
    + n / Nat.lcm (Nat.lcm (Nat.lcm b c) d) e

/-- `T₅(n) = ⌊n/lcm(a,b,c,d,e)⌋`. -/
def t5fun5 (a b c d e n : ℕ) : ℕ := n / Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm a b) c) d) e

/-- **Exact 5-set inclusion–exclusion** (in `ℤ`): `B = s − P₂ + T₃ − T₄ + T₅`. -/
lemma card_ie5 (a b c d e n : ℕ) :
    ((Bgen {a, b, c, d, e} n).card : ℤ)
      = (sfun5 a b c d e n : ℤ) - (p2fun5 a b c d e n : ℤ)
        + (t3fun5 a b c d e n : ℤ) - (t4fun5 a b c d e n : ℤ) + (t5fun5 a b c d e n : ℤ) := by
  have hL : ((Bgen {a, b, c, d, e} n).card : ℤ)
      = ∑ k ∈ Finset.Ioc 0 n,
          if a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k then (1 : ℤ) else 0 := by
    rw [Bgen_eq_filter, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hiff : (∃ f ∈ ({a, b, c, d, e} : Finset ℕ), f ∣ k)
        ↔ (a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨f, (rfl | rfl | rfl | rfl | rfl), h⟩ <;> tauto
      · rintro (h | h | h | h | h)
        exacts [⟨a, Or.inl rfl, h⟩, ⟨b, Or.inr (Or.inl rfl), h⟩,
          ⟨c, Or.inr (Or.inr (Or.inl rfl)), h⟩, ⟨d, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩,
          ⟨e, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h⟩]
    by_cases hk : a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k ∨ e ∣ k <;> simp [hiff, hk]
  rw [hL]
  simp only [sfun5, p2fun5, t3fun5, t4fun5, t5fun5, Nat.cast_add, cast_div_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lcm5_ind,
    lcm4_ind, lcm4_ind, lcm4_ind, lcm4_ind, lcm4_ind,
    lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind,
    lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind,
    lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind,
    lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind]
  have hb := ie5_bool (a ∣ k) (b ∣ k) (c ∣ k) (d ∣ k) (e ∣ k)
  linarith [hb]

/-- `2B = 2s − 2P₂ + 2T₃ − 2T₄ + 2T₅` (in ℤ), immediate from `card_ie5`. -/
lemma two_B_eq5 (a b c d e n : ℕ) :
    2 * ((Bgen {a, b, c, d, e} n).card : ℤ)
      = 2 * (sfun5 a b c d e n : ℤ) - 2 * (p2fun5 a b c d e n : ℤ)
        + 2 * (t3fun5 a b c d e n : ℤ) - 2 * (t4fun5 a b c d e n : ℤ)
        + 2 * (t5fun5 a b c d e n : ℤ) := by
  have h := card_ie5 a b c d e n
  linarith [h]

/-- Helper: `1 ≤ lcm(e,f)/e` when `e, f ≥ 1`. -/
private lemma one_le_lcm_div {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f) :
    1 ≤ Nat.lcm e f / e := by
  rw [Nat.one_le_div_iff (by omega)]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    simp only [ne_eq, Nat.lcm_eq_zero_iff]; omega)) (Nat.dvd_lcm_left e f)

/-- **4-term charge floor bound** (quintuple case). If `1/k₁+1/k₂+1/k₃+1/k₄ < 1`
(cleared form), then for `t ≥ 1` the per-generator charge is `≥ 1`. -/
lemma floor_bound4 {t k1 k2 k3 k4 : ℕ} (ht : 1 ≤ t)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hk3 : 1 ≤ k3) (hk4 : 1 ≤ k4)
    (hcharge : k2 * k3 * k4 + k1 * k3 * k4 + k1 * k2 * k4 + k1 * k2 * k3
      < k1 * k2 * k3 * k4) :
    1 ≤ t - t / k1 - t / k2 - t / k3 - t / k4 := by
  have e1 : k1 * k2 * k3 * k4 * (t / k1) ≤ t * (k2 * k3 * k4) := by
    have h := Nat.div_mul_le_self t k1; nlinarith [h, Nat.zero_le (k2 * k3 * k4)]
  have e2 : k1 * k2 * k3 * k4 * (t / k2) ≤ t * (k1 * k3 * k4) := by
    have h := Nat.div_mul_le_self t k2; nlinarith [h, Nat.zero_le (k1 * k3 * k4)]
  have e3 : k1 * k2 * k3 * k4 * (t / k3) ≤ t * (k1 * k2 * k4) := by
    have h := Nat.div_mul_le_self t k3; nlinarith [h, Nat.zero_le (k1 * k2 * k4)]
  have e4 : k1 * k2 * k3 * k4 * (t / k4) ≤ t * (k1 * k2 * k3) := by
    have h := Nat.div_mul_le_self t k4; nlinarith [h, Nat.zero_le (k1 * k2 * k3)]
  have hsum : k1 * k2 * k3 * k4 * (t / k1 + t / k2 + t / k3 + t / k4)
      ≤ t * (k2 * k3 * k4 + k1 * k3 * k4 + k1 * k2 * k4 + k1 * k2 * k3) := by
    nlinarith [e1, e2, e3, e4]
  have hlt : t * (k2 * k3 * k4 + k1 * k3 * k4 + k1 * k2 * k4 + k1 * k2 * k3)
      < t * (k1 * k2 * k3 * k4) := by nlinarith [hcharge, ht]
  have hcancel : t / k1 + t / k2 + t / k3 + t / k4 < t := by
    have hchain : k1 * k2 * k3 * k4 * (t / k1 + t / k2 + t / k3 + t / k4)
        < k1 * k2 * k3 * k4 * t := by
      calc k1 * k2 * k3 * k4 * (t / k1 + t / k2 + t / k3 + t / k4)
          ≤ t * (k2 * k3 * k4 + k1 * k3 * k4 + k1 * k2 * k4 + k1 * k2 * k3) := hsum
        _ < t * (k1 * k2 * k3 * k4) := hlt
        _ = k1 * k2 * k3 * k4 * t := by ring
    exact Nat.lt_of_mul_lt_mul_left hchain
  omega

/-- **Prop 8″ (quintuple charge, `good ⟹ X_e ≥ 1`).** For an element `e` with four
other generators `f₁..f₄`, good charge (on the cofactors `kᵢ = lcm(e,fᵢ)/e`) gives
`X_e(n) = ⌊n/e⌋ − Σ⌊n/lcm(e,fᵢ)⌋ ≥ 1` for `n ≥ e`. -/
lemma charge_ge_one4 {e f1 f2 f3 f4 n : ℕ}
    (he : 1 ≤ e) (hf1 : 1 ≤ f1) (hf2 : 1 ≤ f2) (hf3 : 1 ≤ f3) (hf4 : 1 ≤ f4) (hn : e ≤ n)
    (hcharge : (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f3 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
             < (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
               * (Nat.lcm e f4 / e)) :
    1 ≤ n / e - n / Nat.lcm e f1 - n / Nat.lcm e f2 - n / Nat.lcm e f3 - n / Nat.lcm e f4 := by
  rw [div_lcm_eq n e f1, div_lcm_eq n e f2, div_lcm_eq n e f3, div_lcm_eq n e f4]
  have ht : 1 ≤ n / e := (Nat.one_le_div_iff (by omega)).2 hn
  exact floor_bound4 ht (one_le_lcm_div he hf1) (one_le_lcm_div he hf2)
    (one_le_lcm_div he hf3) (one_le_lcm_div he hf4) hcharge

/-- **5-set inclusion–exclusion, per point.** For `d ≤ 5` divisors,
`2·[d≥1] = 2d − 2C(d,2) + 2C(d,3) − 2C(d,4) + 2C(d,5)` (additive form). -/
lemma ie5_pointwise {d : ℕ} (hd : d ≤ 5) :
    2 * min d 1 + 2 * d.choose 2 + 2 * d.choose 4
      = 2 * d + 2 * d.choose 3 + 2 * d.choose 5 := by
  interval_cases d <;> decide

/-- **`Y_H` weight nonnegativity for the three-good case** (H-pair `p ≤ 2`, three
good partners `q ≤ 3`): the size-5 `Y_H` weight `p(2−p−q) + 2C(d,3) − 2C(d,4) +
2C(d,5) ≥ 0`, `d = p+q` (additive form). -/
lemma yh_weight_nonneg5 {p q : ℕ} (hp : p ≤ 2) (hq : q ≤ 3) :
    p * (p + q) + 2 * (p + q).choose 4
      ≤ 2 * p + 2 * (p + q).choose 3 + 2 * (p + q).choose 5 := by
  interval_cases p <;> interval_cases q <;> decide

/-- **Charge in ℤ (quintuple).** For a good element `e` with four partners, the ℤ
charge `X_e = ⌊n/e⌋ − Σ⌊n/lcm(e,fᵢ)⌋ ≥ 1` for `n ≥ e`. -/
lemma charge_ge_one_int4 {e f1 f2 f3 f4 n : ℕ}
    (he : 1 ≤ e) (hf1 : 1 ≤ f1) (hf2 : 1 ≤ f2) (hf3 : 1 ≤ f3) (hf4 : 1 ≤ f4) (hn : e ≤ n)
    (hcharge : (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f3 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f4 / e)
             + (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
             < (Nat.lcm e f1 / e) * (Nat.lcm e f2 / e) * (Nat.lcm e f3 / e)
               * (Nat.lcm e f4 / e)) :
    1 ≤ ((n / e : ℕ) : ℤ) - ((n / Nat.lcm e f1 : ℕ) : ℤ) - ((n / Nat.lcm e f2 : ℕ) : ℤ)
        - ((n / Nat.lcm e f3 : ℕ) : ℤ) - ((n / Nat.lcm e f4 : ℕ) : ℤ) := by
  have h := charge_ge_one4 he hf1 hf2 hf3 hf4 hn hcharge
  omega

/-- **Charge-sum identity (quintuple).** The five charges sum to `s − 2P₂`. -/
lemma charge_sum5 (a b c d e n : ℕ) :
    (((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ) - ((n / Nat.lcm a e : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ) - ((n / Nat.lcm b e : ℕ) : ℤ))
      + (((n / c : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm c d : ℕ) : ℤ) - ((n / Nat.lcm c e : ℕ) : ℤ))
      + (((n / d : ℕ) : ℤ) - ((n / Nat.lcm a d : ℕ) : ℤ) - ((n / Nat.lcm b d : ℕ) : ℤ)
        - ((n / Nat.lcm c d : ℕ) : ℤ) - ((n / Nat.lcm d e : ℕ) : ℤ))
      + (((n / e : ℕ) : ℤ) - ((n / Nat.lcm a e : ℕ) : ℤ) - ((n / Nat.lcm b e : ℕ) : ℤ)
        - ((n / Nat.lcm c e : ℕ) : ℤ) - ((n / Nat.lcm d e : ℕ) : ℤ))
      = (sfun5 a b c d e n : ℤ) - 2 * (p2fun5 a b c d e n : ℤ) := by
  simp only [sfun5, p2fun5, Nat.cast_add]
  ring

/-- **`Y_H` pointwise nonnegativity (three-good case), indicator form.** H-events
`h₁,h₂`, G-events `g₁,g₂,g₃`. The raw `Y_H` weight is `≥ 0`; `decide` over `2⁵ = 32`
boolean cases. -/
lemma yh_raw_nonneg5 (h1 h2 g1 g2 g3 : Prop)
    [Decidable h1] [Decidable h2] [Decidable g1] [Decidable g2] [Decidable g3] :
    0 ≤ ((if h1 then (1:ℤ) else 0) + (if h2 then 1 else 0)
        - 2 * (if h1 ∧ h2 then 1 else 0)
        - ((if h1 ∧ g1 then 1 else 0) + (if h1 ∧ g2 then 1 else 0) + (if h1 ∧ g3 then 1 else 0)
          + (if h2 ∧ g1 then 1 else 0) + (if h2 ∧ g2 then 1 else 0) + (if h2 ∧ g3 then 1 else 0))
        + 2 * ((if h1 ∧ h2 ∧ g1 then 1 else 0) + (if h1 ∧ h2 ∧ g2 then 1 else 0)
          + (if h1 ∧ h2 ∧ g3 then 1 else 0) + (if h1 ∧ g1 ∧ g2 then 1 else 0)
          + (if h1 ∧ g1 ∧ g3 then 1 else 0) + (if h1 ∧ g2 ∧ g3 then 1 else 0)
          + (if h2 ∧ g1 ∧ g2 then 1 else 0) + (if h2 ∧ g1 ∧ g3 then 1 else 0)
          + (if h2 ∧ g2 ∧ g3 then 1 else 0) + (if g1 ∧ g2 ∧ g3 then 1 else 0))
        - 2 * ((if h1 ∧ h2 ∧ g1 ∧ g2 then 1 else 0) + (if h1 ∧ h2 ∧ g1 ∧ g3 then 1 else 0)
          + (if h1 ∧ h2 ∧ g2 ∧ g3 then 1 else 0) + (if h1 ∧ g1 ∧ g2 ∧ g3 then 1 else 0)
          + (if h2 ∧ g1 ∧ g2 ∧ g3 then 1 else 0))
        + 2 * (if h1 ∧ h2 ∧ g1 ∧ g2 ∧ g3 then (1:ℤ) else 0)) := by
  by_cases h1 <;> by_cases h2 <;> by_cases g1 <;> by_cases g2 <;> by_cases g3 <;> simp_all

/-- The raw pointwise `Y_H` contribution at `k` (H-elements `a,b`; G-elements `c,d,e`). -/
def yhRaw5 (a b c d e k : ℕ) : ℤ :=
  (if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0)
    - 2 * (if a ∣ k ∧ b ∣ k then 1 else 0)
    - ((if a ∣ k ∧ c ∣ k then 1 else 0) + (if a ∣ k ∧ d ∣ k then 1 else 0)
      + (if a ∣ k ∧ e ∣ k then 1 else 0) + (if b ∣ k ∧ c ∣ k then 1 else 0)
      + (if b ∣ k ∧ d ∣ k then 1 else 0) + (if b ∣ k ∧ e ∣ k then 1 else 0))
    + 2 * ((if a ∣ k ∧ b ∣ k ∧ c ∣ k then 1 else 0) + (if a ∣ k ∧ b ∣ k ∧ d ∣ k then 1 else 0)
      + (if a ∣ k ∧ b ∣ k ∧ e ∣ k then 1 else 0) + (if a ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0)
      + (if a ∣ k ∧ c ∣ k ∧ e ∣ k then 1 else 0) + (if a ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0)
      + (if b ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0) + (if b ∣ k ∧ c ∣ k ∧ e ∣ k then 1 else 0)
      + (if b ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0) + (if c ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0))
    - 2 * ((if a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ d ∣ k then 1 else 0)
      + (if a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ e ∣ k then 1 else 0)
      + (if a ∣ k ∧ b ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0)
      + (if a ∣ k ∧ c ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0)
      + (if b ∣ k ∧ c ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0))
    + 2 * (if a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ d ∣ k ∧ e ∣ k then 1 else 0)

/-- **`Y_H = Σ_k yhRaw5`.** Pointwise expansion of `X_a + X_b + 2T₃ − 2T₄ + 2T₅`. -/
lemma yh_eq_sum5 (a b c d e n : ℕ) :
    ((((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ) - ((n / Nat.lcm a e : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ) - ((n / Nat.lcm b e : ℕ) : ℤ))
      + 2 * (t3fun5 a b c d e n : ℤ) - 2 * (t4fun5 a b c d e n : ℤ)
        + 2 * (t5fun5 a b c d e n : ℤ))
      = ∑ k ∈ Finset.Ioc 0 n, yhRaw5 a b c d e k := by
  simp only [yhRaw5, t3fun5, t4fun5, t5fun5, Nat.cast_add, cast_div_eq_sum_indicator,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind,
    lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind, lcm3_ind,
    lcm3_ind, lcm4_ind, lcm4_ind, lcm4_ind, lcm4_ind, lcm4_ind, lcm5_ind]
  ring

/-- **`Y_H ≥ 2`** (three-good case): H-pair `a,b` (positive, `≤ n`, antichain with the
other three) contributes `1` at `k = a` and `k = b`; the rest is `≥ 0`. -/
lemma yh_ge_two5 {a b c d e n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (han : a ≤ n) (hbn : b ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a) (hea : ¬ e ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b) (heb : ¬ e ∣ b) :
    2 ≤ (((n / a : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm a c : ℕ) : ℤ)
        - ((n / Nat.lcm a d : ℕ) : ℤ) - ((n / Nat.lcm a e : ℕ) : ℤ))
      + (((n / b : ℕ) : ℤ) - ((n / Nat.lcm a b : ℕ) : ℤ) - ((n / Nat.lcm b c : ℕ) : ℤ)
        - ((n / Nat.lcm b d : ℕ) : ℤ) - ((n / Nat.lcm b e : ℕ) : ℤ))
      + 2 * (t3fun5 a b c d e n : ℤ) - 2 * (t4fun5 a b c d e n : ℤ)
        + 2 * (t5fun5 a b c d e n : ℤ) := by
  rw [yh_eq_sum5]
  have hnn : ∀ k ∈ Finset.Ioc 0 n, k ∉ ({a, b} : Finset ℕ) → 0 ≤ yhRaw5 a b c d e k :=
    fun k _ _ => yh_raw_nonneg5 (a ∣ k) (b ∣ k) (c ∣ k) (d ∣ k) (e ∣ k)
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ioc 0 n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_Ioc] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hRa : yhRaw5 a b c d e a = 1 := by simp [yhRaw5, hba, hca, hda, hea]
  have hRb : yhRaw5 a b c d e b = 1 := by simp [yhRaw5, hab2, hcb, hdb, heb]
  have hpair : ∑ k ∈ ({a, b} : Finset ℕ), yhRaw5 a b c d e k = 2 := by
    rw [Finset.sum_pair hab, hRa, hRb]; norm_num
  linarith [hle, hpair]

/-- **Three-good-charge, step 1: `2B ≥ s + 5`.** Primitive quintuple with `c,d,e`
good and `a,b` the H-pair. -/
lemma two_B_ge_s5 {a b c d e n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hen : e ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a) (hea : ¬ e ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b) (heb : ¬ e ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d))
    (he_good : (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e)
             < (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)) :
    (sfun5 a b c d e n : ℤ) + 5 ≤ 2 * ((Bgen {a, b, c, d, e} n).card : ℤ) := by
  have h2B := two_B_eq5 a b c d e n
  have hcs := charge_sum5 a b c d e n
  have hYH := yh_ge_two5 ha hb han hbn hab hba hca hda hea hab2 hcb hdb heb
  have hXc := charge_ge_one_int4 hc ha hb hd he hcn hc_good
  have hXd := charge_ge_one_int4 hd ha hb hc he hdn hd_good
  have hXe := charge_ge_one_int4 he ha hb hc hd hen he_good
  rw [Nat.lcm_comm c a, Nat.lcm_comm c b] at hXc
  rw [Nat.lcm_comm d a, Nat.lcm_comm d b, Nat.lcm_comm d c] at hXd
  rw [Nat.lcm_comm e a, Nat.lcm_comm e b, Nat.lcm_comm e c, Nat.lcm_comm e d] at hXe
  simp only [sfun5, p2fun5, Nat.cast_add] at h2B hcs ⊢
  linarith [h2B, hcs, hYH, hXc, hXd, hXe]

/-- **Floor/mod bound (quintuple).** `n·(quads) < (s+5)·abcde`. -/
lemma s5_gt (a b c d e n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    (n : ℤ) * ((b : ℤ) * c * d * e + (a : ℤ) * c * d * e + (a : ℤ) * b * d * e
        + (a : ℤ) * b * c * e + (a : ℤ) * b * c * d)
      < ((sfun5 a b c d e n : ℤ) + 5) * ((a : ℤ) * b * c * d * e) := by
  have da : (a : ℤ) * ((n / a : ℕ) : ℤ) = (n : ℤ) - ((n % a : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n a; omega
  have db : (b : ℤ) * ((n / b : ℕ) : ℤ) = (n : ℤ) - ((n % b : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n b; omega
  have dc : (c : ℤ) * ((n / c : ℕ) : ℤ) = (n : ℤ) - ((n % c : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n c; omega
  have dd : (d : ℤ) * ((n / d : ℕ) : ℤ) = (n : ℤ) - ((n % d : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n d; omega
  have de : (e : ℤ) * ((n / e : ℕ) : ℤ) = (n : ℤ) - ((n % e : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n e; omega
  have ma : ((n % a : ℕ) : ℤ) < a := by exact_mod_cast Nat.mod_lt n ha
  have mb : ((n % b : ℕ) : ℤ) < b := by exact_mod_cast Nat.mod_lt n hb
  have mc : ((n % c : ℕ) : ℤ) < c := by exact_mod_cast Nat.mod_lt n hc
  have md : ((n % d : ℕ) : ℤ) < d := by exact_mod_cast Nat.mod_lt n hd
  have me : ((n % e : ℕ) : ℤ) < e := by exact_mod_cast Nat.mod_lt n he
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have key : (sfun5 a b c d e n : ℤ) * ((a : ℤ) * b * c * d * e)
      = (n : ℤ) * ((b : ℤ) * c * d * e + (a : ℤ) * c * d * e + (a : ℤ) * b * d * e
          + (a : ℤ) * b * c * e + (a : ℤ) * b * c * d)
        - (((n % a : ℕ) : ℤ) * ((b : ℤ) * c * d * e) + ((n % b : ℕ) : ℤ) * ((a : ℤ) * c * d * e)
          + ((n % c : ℕ) : ℤ) * ((a : ℤ) * b * d * e) + ((n % d : ℕ) : ℤ) * ((a : ℤ) * b * c * e)
          + ((n % e : ℕ) : ℤ) * ((a : ℤ) * b * c * d)) := by
    simp only [sfun5, Nat.cast_add]
    linear_combination ((b : ℤ) * c * d * e) * da + ((a : ℤ) * c * d * e) * db
      + ((a : ℤ) * b * d * e) * dc + ((a : ℤ) * b * c * e) * dd + ((a : ℤ) * b * c * d) * de
  have hpa : ((n % a : ℕ) : ℤ) * ((b : ℤ) * c * d * e) < (a : ℤ) * b * c * d * e := by
    have h := mul_lt_mul_of_pos_right ma (show (0:ℤ) < (b:ℤ) * c * d * e by positivity)
    have hE : (a : ℤ) * ((b:ℤ) * c * d * e) = (a : ℤ) * b * c * d * e := by ring
    linarith [h, hE]
  have hpb : ((n % b : ℕ) : ℤ) * ((a : ℤ) * c * d * e) < (a : ℤ) * b * c * d * e := by
    have h := mul_lt_mul_of_pos_right mb (show (0:ℤ) < (a:ℤ) * c * d * e by positivity)
    have hE : (b : ℤ) * ((a:ℤ) * c * d * e) = (a : ℤ) * b * c * d * e := by ring
    linarith [h, hE]
  have hpc : ((n % c : ℕ) : ℤ) * ((a : ℤ) * b * d * e) < (a : ℤ) * b * c * d * e := by
    have h := mul_lt_mul_of_pos_right mc (show (0:ℤ) < (a:ℤ) * b * d * e by positivity)
    have hE : (c : ℤ) * ((a:ℤ) * b * d * e) = (a : ℤ) * b * c * d * e := by ring
    linarith [h, hE]
  have hpd : ((n % d : ℕ) : ℤ) * ((a : ℤ) * b * c * e) < (a : ℤ) * b * c * d * e := by
    have h := mul_lt_mul_of_pos_right md (show (0:ℤ) < (a:ℤ) * b * c * e by positivity)
    have hE : (d : ℤ) * ((a:ℤ) * b * c * e) = (a : ℤ) * b * c * d * e := by ring
    linarith [h, hE]
  have hpe : ((n % e : ℕ) : ℤ) * ((a : ℤ) * b * c * d) < (a : ℤ) * b * c * d * e := by
    have h := mul_lt_mul_of_pos_right me (show (0:ℤ) < (a:ℤ) * b * c * d by positivity)
    have hE : (e : ℤ) * ((a:ℤ) * b * c * d) = (a : ℤ) * b * c * d * e := by ring
    linarith [h, hE]
  have hexp : ((sfun5 a b c d e n : ℤ) + 5) * ((a : ℤ) * b * c * d * e)
      = (sfun5 a b c d e n : ℤ) * ((a : ℤ) * b * c * d * e) + 5 * ((a : ℤ) * b * c * d * e) := by
    ring
  rw [hexp, key]
  linarith [hpa, hpb, hpc, hpd, hpe]

/-- **Three-good-charge proposition: `2B(n) > nS`** (integer form) for a primitive
quintuple with three good charges (`c,d,e`; `a,b` the H-pair). -/
lemma three_good_charge_2BnS5 {a b c d e n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hen : e ≤ n) (hab : a ≠ b)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a) (hea : ¬ e ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b) (heb : ¬ e ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d))
    (he_good : (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e)
             < (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)) :
    (n : ℤ) * ((b : ℤ) * c * d * e + (a : ℤ) * c * d * e + (a : ℤ) * b * d * e
        + (a : ℤ) * b * c * e + (a : ℤ) * b * c * d)
      < 2 * ((Bgen {a, b, c, d, e} n).card : ℤ) * ((a : ℤ) * b * c * d * e) := by
  have hs5 := two_B_ge_s5 ha hb hc hd he han hbn hcn hdn hen hab hba hca hda hea hab2 hcb hdb heb
    hc_good hd_good he_good
  have hgt := s5_gt a b c d e n ha hb hc hd he
  have habcde : (0 : ℤ) ≤ (a : ℤ) * b * c * d * e := le_of_lt (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hs5 habcde
  linarith [hgt, hmul]

/-- Union bound for the quintuple: `B(m) ≤ s(m)`. -/
lemma Bgen_card_le_sfun5 {a b c d e m : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (Bgen {a, b, c, d, e} m).card ≤ sfun5 a b c d e m := by
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [Finset.sum_insert (by simp [hab, hac, had, hae]),
    Finset.sum_insert (by simp [hbc, hbd, hbe]), Finset.sum_insert (by simp [hcd, hce]),
    Finset.sum_insert (by simp [hde]), Finset.sum_singleton]
  simp only [mult_card, sfun5]
  omega

/-- **EP488 for a primitive quintuple with three good charges.** `n·B(m) < 2·m·B(n)`
for all `m > n ≥ max` when three of the five (here `c,d,e`) are good and `a,b` are
the H-pair. This is the analytic engine for `|core| = 5`; it is **partial** — it does
NOT establish `|core| = 5`, which requires handling the `≤ 2`-good residual. -/
theorem ep488_quint_three_good {a b c d e n m : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) (hdn : d ≤ n) (hen : e ≤ n) (hm : n < m)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hba : ¬ b ∣ a) (hca : ¬ c ∣ a) (hda : ¬ d ∣ a) (hea : ¬ e ∣ a)
    (hab2 : ¬ a ∣ b) (hcb : ¬ c ∣ b) (hdb : ¬ d ∣ b) (heb : ¬ e ∣ b)
    (hc_good : (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c e / c)
             + (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c)
             < (Nat.lcm c a / c) * (Nat.lcm c b / c) * (Nat.lcm c d / c) * (Nat.lcm c e / c))
    (hd_good : (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d e / d)
             + (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d)
             < (Nat.lcm d a / d) * (Nat.lcm d b / d) * (Nat.lcm d c / d) * (Nat.lcm d e / d))
    (he_good : (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e d / e)
             + (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e)
             < (Nat.lcm e a / e) * (Nat.lcm e b / e) * (Nat.lcm e c / e) * (Nat.lcm e d / e)) :
    n * (Bgen {a, b, c, d, e} m).card < 2 * m * (Bgen {a, b, c, d, e} n).card := by
  have hlow := three_good_charge_2BnS5 ha hb hc hd he han hbn hcn hdn hen hab hba hca hda hea
    hab2 hcb hdb heb hc_good hd_good he_good
  have hBm := Bgen_card_le_sfun5 (a := a) (b := b) (c := c) (d := d) (e := e) (m := m)
    hab hac had hae hbc hbd hbe hcd hce hde
  have habcde : 0 < a * b * c * d * e := by positivity
  have hsm : sfun5 a b c d e m * (a * b * c * d * e)
      ≤ m * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d) := by
    have p1 : m / a * (a * b * c * d * e) ≤ m * (b * c * d * e) := by
      calc m / a * (a * b * c * d * e) = m / a * a * (b * c * d * e) := by ring
        _ ≤ m * (b * c * d * e) := mul_le_mul_right' (Nat.div_mul_le_self m a) (b * c * d * e)
    have p2 : m / b * (a * b * c * d * e) ≤ m * (a * c * d * e) := by
      calc m / b * (a * b * c * d * e) = m / b * b * (a * c * d * e) := by ring
        _ ≤ m * (a * c * d * e) := mul_le_mul_right' (Nat.div_mul_le_self m b) (a * c * d * e)
    have p3 : m / c * (a * b * c * d * e) ≤ m * (a * b * d * e) := by
      calc m / c * (a * b * c * d * e) = m / c * c * (a * b * d * e) := by ring
        _ ≤ m * (a * b * d * e) := mul_le_mul_right' (Nat.div_mul_le_self m c) (a * b * d * e)
    have p4 : m / d * (a * b * c * d * e) ≤ m * (a * b * c * e) := by
      calc m / d * (a * b * c * d * e) = m / d * d * (a * b * c * e) := by ring
        _ ≤ m * (a * b * c * e) := mul_le_mul_right' (Nat.div_mul_le_self m d) (a * b * c * e)
    have p5 : m / e * (a * b * c * d * e) ≤ m * (a * b * c * d) := by
      calc m / e * (a * b * c * d * e) = m / e * e * (a * b * c * d) := by ring
        _ ≤ m * (a * b * c * d) := mul_le_mul_right' (Nat.div_mul_le_self m e) (a * b * c * d)
    simp only [sfun5]
    calc (m / a + m / b + m / c + m / d + m / e) * (a * b * c * d * e)
        = m / a * (a * b * c * d * e) + m / b * (a * b * c * d * e) + m / c * (a * b * c * d * e)
          + m / d * (a * b * c * d * e) + m / e * (a * b * c * d * e) := by ring
      _ ≤ m * (b * c * d * e) + m * (a * c * d * e) + m * (a * b * d * e) + m * (a * b * c * e)
          + m * (a * b * c * d) := by linarith [p1, p2, p3, p4, p5]
      _ = m * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d) := by
          ring
  have hub : (Bgen {a, b, c, d, e} m).card * (a * b * c * d * e)
      ≤ m * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d) :=
    le_trans (mul_le_mul_right' hBm (a * b * c * d * e)) hsm
  have hlow_nat : n * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d)
      < 2 * (Bgen {a, b, c, d, e} n).card * (a * b * c * d * e) := by exact_mod_cast hlow
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
  have s1 : n * ((Bgen {a, b, c, d, e} m).card * (a * b * c * d * e))
      ≤ n * (m * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d)) :=
    Nat.mul_le_mul_left n hub
  have s2 : m * (n * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d))
      < m * (2 * (Bgen {a, b, c, d, e} n).card * (a * b * c * d * e)) :=
    mul_lt_mul_of_pos_left hlow_nat hm0
  have keyN : n * (Bgen {a, b, c, d, e} m).card * (a * b * c * d * e)
      < 2 * m * (Bgen {a, b, c, d, e} n).card * (a * b * c * d * e) := by
    calc n * (Bgen {a, b, c, d, e} m).card * (a * b * c * d * e)
        = n * ((Bgen {a, b, c, d, e} m).card * (a * b * c * d * e)) := by ring
      _ ≤ n * (m * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d)) := s1
      _ = m * (n * (b * c * d * e + a * c * d * e + a * b * d * e + a * b * c * e + a * b * c * d)) := by
          ring
      _ < m * (2 * (Bgen {a, b, c, d, e} n).card * (a * b * c * d * e)) := s2
      _ = 2 * m * (Bgen {a, b, c, d, e} n).card * (a * b * c * d * e) := by ring
  exact lt_of_mul_lt_mul_right keyN (Nat.zero_le _)

end Erdos488
