import Ep488.Reduction

/-!
# Certificate criterion and periodicity of `B`

Two ingredients that turn the per-set "compute the exact ratio bounds and check
`β < 2α`" strategy into a rigorous, finite argument:

* `ep488_of_certificate` — the clean interface: if `B_A(x)/x` lies in `[c/d, e/d]`
  for every `x ≥ N` and `e < 2c` (i.e. `β < 2α`), then EP488 holds for `A`.
* `Bgen_add_period` — `B_A(x + L) = B_A(x) + B_A(L)` whenever every element of `A`
  divides `L`.  This is why the infinite check collapses to one period: `B` is
  arithmetic-progression-like with common difference `D = B_A(L)`.
-/

namespace Erdos488

open Finset

/-- **Certificate criterion.** If `c/d ≤ B_A(x)/x ≤ e/d` for all `x ≥ N ≥ 1`, and
`e < 2c` (that is `β < 2α`), then EP488 holds for `A`. -/
theorem ep488_of_certificate {A : Finset ℕ} {N c e d : ℕ} (hN : 1 ≤ N)
    (hlow : ∀ x, N ≤ x → c * x ≤ d * (Bgen A x).card)
    (hupp : ∀ x, N ≤ x → d * (Bgen A x).card ≤ e * x)
    (hcert : e < 2 * c)
    {n m : ℕ} (hn : N ≤ n) (hm : n < m) :
    n * (Bgen A m).card < 2 * m * (Bgen A n).card := by
  have hnpos : 0 < n := lt_of_lt_of_le hN hn
  have hmpos : 0 < m := lt_trans hnpos hm
  have hUm := hupp m (le_trans hn (le_of_lt hm))
  have hLn := hlow n hn
  have t1 : d * (n * (Bgen A m).card) ≤ e * (n * m) := by
    calc d * (n * (Bgen A m).card) = n * (d * (Bgen A m).card) := by ring
      _ ≤ n * (e * m) := Nat.mul_le_mul_left n hUm
      _ = e * (n * m) := by ring
  have t2 : 2 * c * (n * m) ≤ d * (2 * m * (Bgen A n).card) := by
    calc 2 * c * (n * m) = 2 * m * (c * n) := by ring
      _ ≤ 2 * m * (d * (Bgen A n).card) := Nat.mul_le_mul_left (2 * m) hLn
      _ = d * (2 * m * (Bgen A n).card) := by ring
  have t3 : e * (n * m) < 2 * c * (n * m) := by
    have hp : 0 < n * m := Nat.mul_pos hnpos hmpos
    nlinarith [hcert, hp]
  have key : d * (n * (Bgen A m).card) < d * (2 * m * (Bgen A n).card) := by omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- `B_A(n)` as a `filter` on the interval, convenient for counting. -/
lemma Bgen_eq_filter (A : Finset ℕ) (n : ℕ) :
    Bgen A n = (Ioc 0 n).filter (fun k => ∃ a ∈ A, a ∣ k) := by
  ext k
  simp only [mem_Bgen, mem_filter, mem_Ioc]

/-- One-step increment of the count. -/
private lemma count_step (χ : ℕ → Prop) [DecidablePred χ] (y : ℕ) :
    ((Ioc 0 (y + 1)).filter χ).card
      = ((Ioc 0 y).filter χ).card + (if χ (y + 1) then 1 else 0) := by
  have hins : Ioc 0 (y + 1) = insert (y + 1) (Ioc 0 y) := by
    ext k; simp only [mem_Ioc, mem_insert]; omega
  have hnot : (y + 1) ∉ (Ioc 0 y).filter χ := by simp [mem_filter, mem_Ioc]
  rw [hins, filter_insert]
  by_cases h : χ (y + 1)
  · rw [if_pos h, if_pos h, card_insert_of_notMem hnot]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- **Periodicity of the count.** If `χ` is `L`-periodic then counting it on
`(0, x+L]` exceeds the count on `(0, x]` by exactly the count on one period. -/
private lemma count_period (χ : ℕ → Prop) [DecidablePred χ] {L : ℕ}
    (hper : ∀ k, χ (k + L) ↔ χ k) (x : ℕ) :
    ((Ioc 0 (x + L)).filter χ).card
      = ((Ioc 0 x).filter χ).card + ((Ioc 0 L).filter χ).card := by
  induction x with
  | zero => simp
  | succ x ih =>
    have e1 : x + 1 + L = (x + L) + 1 := by ring
    have e2 : χ ((x + L) + 1) ↔ χ (x + 1) := by
      have := hper (x + 1); rwa [show x + 1 + L = (x + L) + 1 from by ring] at this
    rw [e1, count_step χ (x + L), ih, count_step χ x]
    by_cases h : χ (x + 1)
    · rw [if_pos h, if_pos (e2.mpr h)]; omega
    · rw [if_neg h, if_neg (fun hc => h (e2.mp hc))]; omega

/-- **`B` is periodic.** If every element of `A` divides `L`, then
`B_A(x + L) = B_A(x) + B_A(L)`. -/
theorem Bgen_add_period {A : Finset ℕ} {L : ℕ} (hL : ∀ a ∈ A, a ∣ L) (x : ℕ) :
    (Bgen A (x + L)).card = (Bgen A x).card + (Bgen A L).card := by
  classical
  have hper : ∀ k, (∃ a ∈ A, a ∣ k + L) ↔ (∃ a ∈ A, a ∣ k) := by
    intro k
    have key : ∀ a ∈ A, (a ∣ k + L ↔ a ∣ k) := by
      intro a ha
      rw [Nat.add_comm k L]
      exact Nat.dvd_add_right (hL a ha)
    constructor
    · rintro ⟨a, ha, hd⟩; exact ⟨a, ha, (key a ha).mp hd⟩
    · rintro ⟨a, ha, hd⟩; exact ⟨a, ha, (key a ha).mpr hd⟩
  rw [Bgen_eq_filter, Bgen_eq_filter, Bgen_eq_filter]
  exact count_period (fun k => ∃ a ∈ A, a ∣ k) hper x

/-- Iterated periodicity: `B_A(x + q·L) = B_A(x) + q·B_A(L)`. -/
theorem Bgen_add_mul_period {A : Finset ℕ} {L : ℕ} (hL : ∀ a ∈ A, a ∣ L) (x q : ℕ) :
    (Bgen A (x + q * L)).card = (Bgen A x).card + q * (Bgen A L).card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : x + (q + 1) * L = (x + q * L) + L := by ring
    rw [this, Bgen_add_period hL, ih]
    ring

/-- Decompose `x ≥ N` as `x = x₀ + q·L` with `x₀` in the window `[N, N+L)`. -/
private lemma window_decomp {N L : ℕ} (hL0 : 0 < L) {x : ℕ} (hx : N ≤ x) :
    ∃ q x0, N ≤ x0 ∧ x0 < N + L ∧ x = x0 + q * L := by
  refine ⟨(x - N) / L, N + (x - N) % L, by omega, ?_, ?_⟩
  · have := Nat.mod_lt (x - N) hL0; omega
  · have hdm : (x - N) % L + (x - N) / L * L = x - N := Nat.mod_add_div' (x - N) L
    omega

/-- Global lower bound from a window check + a density-slope condition. -/
private lemma le_window {A : Finset ℕ} {N L c d : ℕ} (hL0 : 0 < L)
    (hLdvd : ∀ a ∈ A, a ∣ L)
    (hslope : c * L ≤ d * (Bgen A L).card)
    (hwin : ∀ x, N ≤ x → x < N + L → c * x ≤ d * (Bgen A x).card)
    {x : ℕ} (hx : N ≤ x) : c * x ≤ d * (Bgen A x).card := by
  obtain ⟨q, x0, hx0N, hx0L, hxeq⟩ := window_decomp hL0 hx
  have hB : (Bgen A x).card = (Bgen A x0).card + q * (Bgen A L).card := by
    rw [hxeq, Bgen_add_mul_period hLdvd]
  have hw := hwin x0 hx0N hx0L
  have hqsl : q * (c * L) ≤ q * (d * (Bgen A L).card) := Nat.mul_le_mul_left q hslope
  calc c * x = c * x0 + q * (c * L) := by rw [hxeq]; ring
    _ ≤ d * (Bgen A x0).card + q * (d * (Bgen A L).card) := by omega
    _ = d * ((Bgen A x0).card + q * (Bgen A L).card) := by ring
    _ = d * (Bgen A x).card := by rw [hB]

/-- Global upper bound from a window check + a density-slope condition. -/
private lemma ge_window {A : Finset ℕ} {N L e d : ℕ} (hL0 : 0 < L)
    (hLdvd : ∀ a ∈ A, a ∣ L)
    (hslope : d * (Bgen A L).card ≤ e * L)
    (hwin : ∀ x, N ≤ x → x < N + L → d * (Bgen A x).card ≤ e * x)
    {x : ℕ} (hx : N ≤ x) : d * (Bgen A x).card ≤ e * x := by
  obtain ⟨q, x0, hx0N, hx0L, hxeq⟩ := window_decomp hL0 hx
  have hB : (Bgen A x).card = (Bgen A x0).card + q * (Bgen A L).card := by
    rw [hxeq, Bgen_add_mul_period hLdvd]
  have hw := hwin x0 hx0N hx0L
  have hqsl : q * (d * (Bgen A L).card) ≤ q * (e * L) := Nat.mul_le_mul_left q hslope
  calc d * (Bgen A x).card = d * (Bgen A x0).card + q * (d * (Bgen A L).card) := by rw [hB]; ring
    _ ≤ e * x0 + q * (e * L) := by omega
    _ = e * x := by rw [hxeq]; ring

/-- **Finite-window certificate.** To prove EP488 for a fixed `A`, it suffices to
check, over ONE period `L` (any common multiple of `A`): the two density slopes
`c·L ≤ d·B(L) ≤ e·L`, the ratio bounds `c·x ≤ d·B(x) ≤ e·x` on the single window
`[N, N+L)`, and `e < 2c`.  All finitely checkable. -/
theorem ep488_of_window {A : Finset ℕ} {N L c e d : ℕ} (hN : 1 ≤ N) (hL0 : 0 < L)
    (hLdvd : ∀ a ∈ A, a ∣ L)
    (hslopeL : c * L ≤ d * (Bgen A L).card)
    (hslopeU : d * (Bgen A L).card ≤ e * L)
    (hwinLow : ∀ x, N ≤ x → x < N + L → c * x ≤ d * (Bgen A x).card)
    (hwinUpp : ∀ x, N ≤ x → x < N + L → d * (Bgen A x).card ≤ e * x)
    (hcert : e < 2 * c)
    {n m : ℕ} (hn : N ≤ n) (hm : n < m) :
    n * (Bgen A m).card < 2 * m * (Bgen A n).card :=
  ep488_of_certificate hN
    (fun x hx => le_window hL0 hLdvd hslopeL hwinLow hx)
    (fun x hx => ge_window hL0 hLdvd hslopeU hwinUpp hx)
    hcert hn hm

end Erdos488
