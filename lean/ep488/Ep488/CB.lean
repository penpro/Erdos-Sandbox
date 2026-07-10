import Ep488.Quint

/-!
# The C-B (finite-`n` Bonferroni) covering theorem for quintuples

Machine-checks the load-bearing new result of the size-5 program: the two-term
Bonferroni bound at the counting level, and the covering criterion it yields.

* `bonf_bool` — pointwise 2-term Bonferroni for five divisibility events.
* `cb_bonferroni5` — `B(n) ≥ s(n) − P₂(n)` (unconditional).
* `cb_cover5` — if `s(n) ≥ 2·P₂(n) + 5` then `2B(n) > nS` (division-free) — the
  finite-`n` covering criterion. On the window this closes regime C for the set.

See `../../quintuple_density_notes.md` ("The C-B reorganization").
-/

namespace Erdos488

open Finset

/-- **Pointwise 2-term Bonferroni** for five events: `singles − pairs ≤ [union]`.
Values by `d = #true`: `d − C(d,2) ∈ {0,1,1,0,−2,−5}`, all `≤ [d≥1]`. -/
lemma bonf_bool (a b c d e : Prop)
    [Decidable a] [Decidable b] [Decidable c] [Decidable d] [Decidable e] :
    (((if a then (1:ℤ) else 0) + (if b then 1 else 0) + (if c then 1 else 0)
        + (if d then 1 else 0) + (if e then 1 else 0))
      - ((if a ∧ b then (1:ℤ) else 0) + (if a ∧ c then 1 else 0) + (if a ∧ d then 1 else 0)
        + (if a ∧ e then 1 else 0) + (if b ∧ c then 1 else 0) + (if b ∧ d then 1 else 0)
        + (if b ∧ e then 1 else 0) + (if c ∧ d then 1 else 0) + (if c ∧ e then 1 else 0)
        + (if d ∧ e then 1 else 0)))
      ≤ (if a ∨ b ∨ c ∨ d ∨ e then (1:ℤ) else 0) := by
  by_cases a <;> by_cases b <;> by_cases c <;> by_cases d <;> by_cases e <;> simp_all

/-- **Two-term Bonferroni at the counting level** (unconditional): `B(n) ≥ s(n) − P₂(n)`. -/
lemma cb_bonferroni5 (a b c d e n : ℕ) :
    (sfun5 a b c d e n : ℤ) - (p2fun5 a b c d e n : ℤ)
      ≤ ((Bgen {a, b, c, d, e} n).card : ℤ) := by
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
  simp only [sfun5, p2fun5, Nat.cast_add, cast_div_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind,
      lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind, lcm2_ind]
  exact bonf_bool (a ∣ k) (b ∣ k) (c ∣ k) (d ∣ k) (e ∣ k)

/-- Floor bound: `n·Σ(∏others) < (s(n)+5)·abcde`, i.e. `nS < s(n)+5` cleared of
denominators. Each summand is `n < aᵢ·⌊n/aᵢ⌋ + aᵢ` scaled by `∏others`. -/
lemma floor_bound5 {a b c d e n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    n * (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d)
      < (sfun5 a b c d e n + 5) * (a*b*c*d*e) := by
  have key : ∀ x : ℕ, 0 < x → n < x * (n / x) + x := fun x hx => by
    have := Nat.div_add_mod n x
    have hmod := Nat.mod_lt n hx
    omega
  have Pa : n * (b*c*d*e) < (a*(n/a)+a) * (b*c*d*e) :=
    Nat.mul_lt_mul_of_lt_of_le (key a ha) (le_refl _) (by positivity)
  have Pb : n * (a*c*d*e) < (b*(n/b)+b) * (a*c*d*e) :=
    Nat.mul_lt_mul_of_lt_of_le (key b hb) (le_refl _) (by positivity)
  have Pc : n * (a*b*d*e) < (c*(n/c)+c) * (a*b*d*e) :=
    Nat.mul_lt_mul_of_lt_of_le (key c hc) (le_refl _) (by positivity)
  have Pd : n * (a*b*c*e) < (d*(n/d)+d) * (a*b*c*e) :=
    Nat.mul_lt_mul_of_lt_of_le (key d hd) (le_refl _) (by positivity)
  have Pe : n * (a*b*c*d) < (e*(n/e)+e) * (a*b*c*d) :=
    Nat.mul_lt_mul_of_lt_of_le (key e he) (le_refl _) (by positivity)
  unfold sfun5
  nlinarith [Pa, Pb, Pc, Pd, Pe]

/-- **C-B covering criterion** (division-free). If `s(n) ≥ 2·P₂(n) + 5` then
`n·Σ(∏others) < 2·B(n)·abcde`, i.e. `2B(n) > nS`. On the window this closes regime C. -/
theorem cb_cover5 {a b c d e n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e)
    (hcov : 2 * p2fun5 a b c d e n + 5 ≤ sfun5 a b c d e n) :
    n * (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d)
      < 2 * ((Bgen {a, b, c, d, e} n).card) * (a*b*c*d*e) := by
  -- 2B ≥ 2(s − P₂) = s + (s − 2P₂) ≥ s + 5.
  have hbonf := cb_bonferroni5 a b c d e n
  have h2B : (sfun5 a b c d e n : ℤ) + 5 ≤ 2 * ((Bgen {a, b, c, d, e} n).card : ℤ) := by
    have hc2 : (2 * p2fun5 a b c d e n + 5 : ℤ) ≤ (sfun5 a b c d e n : ℤ) := by exact_mod_cast hcov
    linarith [hbonf]
  -- floor bound, cast to ℤ
  have hfl := floor_bound5 (a := a) (b := b) (c := c) (d := d) (e := e) (n := n) ha hb hc hd he
  have hflZ : (n : ℤ) * (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d)
      < (sfun5 a b c d e n + 5) * (a*b*c*d*e) := by exact_mod_cast hfl
  have habcde : (0 : ℤ) < a*b*c*d*e := by positivity
  -- (s+5)·abcde ≤ 2B·abcde
  have hmul : ((sfun5 a b c d e n : ℤ) + 5) * (a*b*c*d*e)
      ≤ 2 * ((Bgen {a, b, c, d, e} n).card : ℤ) * (a*b*c*d*e) := by
    have := mul_le_mul_of_nonneg_right h2B (le_of_lt habcde)
    linarith [this]
  have : (n : ℤ) * (b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d)
      < 2 * ((Bgen {a, b, c, d, e} n).card : ℤ) * (a*b*c*d*e) := lt_of_lt_of_le hflZ hmul
  exact_mod_cast this

end Erdos488
