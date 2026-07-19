import Ep488.Quint

/-!
# The k = 5 self-bad ceiling (the minimum-good lemma, dual form)

Machine-checks Section 23.6 of `../../cbfin_reduction_notes.md`: in any
5-element divisibility antichain of positive integers, the MAXIMUM element is
never self-bad — the sum of its four gcds is `< e` (indeed `≤ 59e/60`).
Consequently no antichain quintuple has five self-bad elements, which is the
"5-bad impossible" row of the compact-residual partition
(`REFEREE_SIZE5_CANDIDATE.md`, section 2).

The proof is the distinct-reduced-fraction slot argument: each smaller element
`x` is `k·(e/m)` in lowest terms with `k ≥ 2` (antichain), `k < m` (maximality),
`gcd(k,m) = 1`; hence `m ≥ 3`, the slot `m = 3` forces `k = 2` and `m = 4`
forces `k = 3`, so each of those two slots is occupied by AT MOST ONE element,
and the four contributions `e/m` total at most `e/3 + e/4 + e/5 + e/5 = 59e/60`.

* `slot_trichotomy` — per element: `60·gcd ≤ 12e`, or `(m,k) = (3,2)`, or `(4,3)`.
* `ceiling_max` — `Σ_{x ∈ s} gcd e x < e` for any 4 distinct smaller
  non-divisors of `e`.
* `no_five_self_bad` — an antichain 5-set has at most 4 self-bad elements.
-/

namespace Erdos488

open Finset

/-- The reduced denominator of `x/e`: `m = e / gcd e x`. -/
private def mval (e x : ℕ) : ℕ := e / Nat.gcd e x

/-- **Slot trichotomy.** For `0 < x < e` with `x ∤ e`: either the gcd is small
(`60·gcd e x ≤ 12·e`, the `m ≥ 5` slots), or `x = 2e/3` (slot `m = 3`), or
`x = 3e/4` (slot `m = 4`). -/
lemma slot_trichotomy (e x : ℕ) (he : 0 < e) (hx : 0 < x) (hlt : x < e)
    (hnd : ¬ x ∣ e) :
    60 * Nat.gcd e x ≤ 12 * e
    ∨ (mval e x = 3 ∧ 3 * x = 2 * e)
    ∨ (mval e x = 4 ∧ 4 * x = 3 * e) := by
  set g := Nat.gcd e x with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left x he
  have hge : g ∣ e := Nat.gcd_dvd_left e x
  have hgx : g ∣ x := Nat.gcd_dvd_right e x
  set m := e / g with hm
  set k := x / g with hk
  have hem : g * m = e := Nat.mul_div_cancel' hge
  have hxk : g * k = x := Nat.mul_div_cancel' hgx
  have hcop : Nat.Coprime m k := Nat.coprime_div_gcd_div_gcd hgpos
  -- k ≥ 2
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · exfalso; apply hnd; rw [← hxk]; simpa using hge
    · exact h
  -- k < m
  have hkm : k < m := by
    have : g * k < g * m := by rw [hxk, hem]; exact hlt
    exact Nat.lt_of_mul_lt_mul_left this
  have hm3 : 3 ≤ m := by omega
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · -- m ∈ {3, 4}
    interval_cases m
    · -- m = 3: k = 2 forced
      right; left
      have hk2' : k = 2 := by omega
      constructor
      · simp [mval, ← hg, ← hm]
      · have : 3 * (g * k) = 2 * (g * 3) := by rw [hk2']; ring
        calc 3 * x = 3 * (g * k) := by rw [hxk]
        _ = 2 * (g * 3) := this
        _ = 2 * e := by rw [hem]
    · -- m = 4: k coprime to 4, 2 ≤ k < 4 ⟹ k = 3
      right; right
      have hk3 : k = 3 := by
        interval_cases k
        · exfalso
          have : Nat.Coprime 4 2 := hcop
          norm_num [Nat.Coprime] at this
        · rfl
      constructor
      · simp [mval, ← hg, ← hm]
      · have : 4 * (g * k) = 3 * (g * 4) := by rw [hk3]; ring
        calc 4 * x = 4 * (g * k) := by rw [hxk]
        _ = 3 * (g * 4) := this
        _ = 3 * e := by rw [hem]
  · -- m ≥ 5: 5g ≤ gm = e
    left
    have : 5 * g ≤ e := by
      calc 5 * g ≤ m * g := by exact Nat.mul_le_mul_right g h5
      _ = g * m := by ring
      _ = e := hem
    omega

/-- Slot `m = 3` pins the element: `3x = 2e` determines `x`. -/
lemma slot3_unique (e x y : ℕ) (hx : 3 * x = 2 * e) (hy : 3 * y = 2 * e) :
    x = y := by omega

/-- Slot `m = 4` pins the element: `4x = 3e` determines `x`. -/
lemma slot4_unique (e x y : ℕ) (hx : 4 * x = 3 * e) (hy : 4 * y = 3 * e) :
    x = y := by omega

/-- **The k = 5 ceiling, sum form.** If `s` consists of 4 positive integers,
each `< e` and none dividing `e`, then `Σ_{x ∈ s} gcd e x < e`. -/
theorem ceiling_max (e : ℕ) (he : 0 < e) (s : Finset ℕ) (hcard : s.card = 4)
    (hlt : ∀ x ∈ s, x < e) (hnd : ∀ x ∈ s, ¬ x ∣ e) (hpos : ∀ x ∈ s, 0 < x) :
    ∑ x ∈ s, Nat.gcd e x < e := by
  -- weight bound: 60·gcd ≤ 12e + (8e if slot3) + (3e if slot4), slots unique
  set T3 := s.filter (fun x => 3 * x = 2 * e) with hT3
  set T4 := s.filter (fun x => 4 * x = 3 * e) with hT4
  have hT3card : T3.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact slot3_unique e x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hT4card : T4.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact slot4_unique e x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  -- pointwise: 60·gcd e x ≤ 12e + ite(x ∈ slot3) 8e + ite(x ∈ slot4) 3e
  have hpt : ∀ x ∈ s, 60 * Nat.gcd e x
      ≤ 12 * e + (if 3 * x = 2 * e then 8 * e else 0)
        + (if 4 * x = 3 * e then 3 * e else 0) := by
    intro x hxs
    rcases slot_trichotomy e x he (hpos x hxs) (hlt x hxs) (hnd x hxs) with h | ⟨_, h3⟩ | ⟨_, h4⟩
    · have h8 : (0:ℕ) ≤ (if 3 * x = 2 * e then 8 * e else 0) := Nat.zero_le _
      have h3' : (0:ℕ) ≤ (if 4 * x = 3 * e then 3 * e else 0) := Nat.zero_le _
      omega
    · -- slot 3: 60·gcd = 20e exactly; g = e/3 since 3(gk)=2(gm), k=2, m=3
      have h34 : ¬ (4 * x = 3 * e) := by omega
      simp only [h3, h34, if_neg, not_false_iff, if_true]
      -- 60·gcd e x = 20e: from 3x = 2e: gcd e x = gcd e (2e/3) — derive via 3·gcd = e·gcd(3·..)/..
      -- direct: g := gcd e x divides e and x; e = g·m with m = 3 known from trichotomy…
      -- easier: 3x = 2e ⟹ x = 2(e/3), 3 ∣ e; gcd(e, x) = (e/3)·gcd(3, 2) = e/3.
      have h3e : 3 ∣ e := by omega
      obtain ⟨t, ht⟩ := h3e
      have hxt : x = 2 * t := by omega
      have hg32 : Nat.gcd 3 2 = 1 := by decide
      have : Nat.gcd e x = t := by
        rw [ht, hxt, Nat.mul_comm 3 t, Nat.mul_comm 2 t, Nat.gcd_mul_left, hg32,
          Nat.mul_one]
      omega
    · -- slot 4: 60·gcd = 15e exactly
      have h43 : ¬ (3 * x = 2 * e) := by omega
      simp only [h4, h43, if_neg, not_false_iff, if_true]
      have h4e : 4 ∣ e := by omega
      obtain ⟨t, ht⟩ := h4e
      have hxt : x = 3 * t := by omega
      have hg43 : Nat.gcd 4 3 = 1 := by decide
      have : Nat.gcd e x = t := by
        rw [ht, hxt, Nat.mul_comm 4 t, Nat.mul_comm 3 t, Nat.gcd_mul_left, hg43,
          Nat.mul_one]
      omega
  -- sum the pointwise bound
  have hsum : ∑ x ∈ s, 60 * Nat.gcd e x
      ≤ ∑ x ∈ s, (12 * e + (if 3 * x = 2 * e then 8 * e else 0)
        + (if 4 * x = 3 * e then 3 * e else 0)) :=
    Finset.sum_le_sum hpt
  have e3 : ∑ x ∈ s, (if 3 * x = 2 * e then 8 * e else 0) = T3.card * (8 * e) := by
    rw [hT3, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have e4 : ∑ x ∈ s, (if 4 * x = 3 * e then 3 * e else 0) = T4.card * (3 * e) := by
    rw [hT4, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have ec : ∑ _x ∈ s, (12 * e) = 4 * (12 * e) := by
    rw [Finset.sum_const, hcard, smul_eq_mul]
  have hsplit : ∑ x ∈ s, (12 * e + (if 3 * x = 2 * e then 8 * e else 0)
      + (if 4 * x = 3 * e then 3 * e else 0))
      = 4 * (12 * e) + T3.card * (8 * e) + T4.card * (3 * e) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ec, e3, e4]
  have htot : ∑ x ∈ s, 60 * Nat.gcd e x ≤ 59 * e := by
    have hb3 : T3.card * (8 * e) ≤ 8 * e := by
      have := Nat.mul_le_mul_right (8 * e) hT3card
      omega
    have hb4 : T4.card * (3 * e) ≤ 3 * e := by
      have := Nat.mul_le_mul_right (3 * e) hT4card
      omega
    omega
  -- 60·Σ ≤ 59e ⟹ Σ < e
  have h60 : 60 * ∑ x ∈ s, Nat.gcd e x = ∑ x ∈ s, 60 * Nat.gcd e x :=
    (Finset.mul_sum _ _ _)
  omega

/-- **No five self-bad.** In a 5-element antichain of positive integers, the
maximum element `e` satisfies `Σ_{x ≠ e} gcd e x < e`: it is never self-bad.
Hence at most 4 elements of any antichain quintuple are self-bad. -/
theorem no_five_self_bad (D : Finset ℕ) (hcard : D.card = 5)
    (hpos : ∀ x ∈ D, 0 < x)
    (hanti : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ x ∣ y)
    (e : ℕ) (he : e ∈ D) (hmax : ∀ x ∈ D, x ≤ e) :
    ∑ x ∈ D.erase e, Nat.gcd e x < e := by
  have hepos : 0 < e := hpos e he
  apply ceiling_max e hepos (D.erase e)
  · rw [Finset.card_erase_of_mem he, hcard]
  · intro x hx
    have hxD := Finset.mem_of_mem_erase hx
    have hne := Finset.ne_of_mem_erase hx
    exact lt_of_le_of_ne (hmax x hxD) hne
  · intro x hx
    exact hanti x (Finset.mem_of_mem_erase hx) e he (Finset.ne_of_mem_erase hx)
  · intro x hx
    exact hpos x (Finset.mem_of_mem_erase hx)

end Erdos488
