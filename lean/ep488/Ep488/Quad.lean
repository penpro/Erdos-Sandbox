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

end Erdos488
