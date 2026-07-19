import Ep488.Ceiling

/-!
# The Duality Transport identity

Machine-checks the campaign's Duality Transport lemma (DT), quoted throughout
the compact-residual partition: dualizing an antichain by `d = L/p` (any common
multiple `L`) turns primal charge into dual self-charge EXACTLY, term by term:

```text
gcd(L/a, L/b) · a·b = gcd(a,b) · L        (a ∣ L, b ∣ L)
```

so `gcd(d_a, d_b)/d_a = gcd(a,b)/b`, and summing, `d_a` is self-bad in the dual
iff `charge(a) ≥ 1` in the primal. This is what makes the dual-side bad counts
(`nselfbad` in `census`, the k = 5 ceiling, the five-sector partition) speak
about primal charges.

* `gcd_div_div` — `gcd (L/a) (L/b) = L / lcm a b`.
* `transport_identity` — the displayed identity.
* `transport_term` — `gcd (L/a) (L/b) · a = gcd a b · (L/b)` (the charge term).
* `dual_selfbad_iff` — `Σ gcd(d_a, d_x) ≥ d_a ↔ Σ gcd(a,x)·(L/x) ≥ L`.
-/

namespace Erdos488

open Finset

/-- `gcd (L/a) (L/b) = L / lcm a b` for divisors `a, b` of `L > 0`. -/
lemma gcd_div_div (L a b : ℕ) (hL : 0 < L) (ha : a ∣ L) (hb : b ∣ L)
    (ha0 : 0 < a) (hb0 : 0 < b) :
    Nat.gcd (L / a) (L / b) = L / Nat.lcm a b := by
  have hl : Nat.lcm a b ∣ L := Nat.lcm_dvd ha hb
  set G := Nat.gcd (L / a) (L / b) with hG
  apply Nat.dvd_antisymm
  · -- G ∣ L / lcm a b
    have hga : G ∣ L / a := Nat.gcd_dvd_left _ _
    have hgb : G ∣ L / b := Nat.gcd_dvd_right _ _
    have hag : a * G ∣ L := by
      obtain ⟨c, hc⟩ := hga
      refine ⟨c, ?_⟩
      calc L = a * (L / a) := (Nat.mul_div_cancel' ha).symm
        _ = a * (G * c) := by rw [hc]
        _ = a * G * c := by ring
    have hbg : b * G ∣ L := by
      obtain ⟨c, hc⟩ := hgb
      refine ⟨c, ?_⟩
      calc L = b * (L / b) := (Nat.mul_div_cancel' hb).symm
        _ = b * (G * c) := by rw [hc]
        _ = b * G * c := by ring
    have hlg : Nat.lcm a b * G ∣ L := by
      have hd := Nat.lcm_dvd hag hbg
      rwa [Nat.lcm_mul_right a G b] at hd
    obtain ⟨c, hc⟩ := hlg
    refine ⟨c, ?_⟩
    have hlpos : 0 < Nat.lcm a b := Nat.pos_of_ne_zero (by
      intro h0
      rw [h0] at hl
      have := Nat.eq_zero_of_zero_dvd hl
      omega)
    apply Nat.div_eq_of_eq_mul_left hlpos
    calc L = Nat.lcm a b * G * c := hc
      _ = G * c * Nat.lcm a b := by ac_rfl
  · -- L / lcm a b ∣ G
    apply Nat.dvd_gcd
    · obtain ⟨c, hc⟩ := Nat.dvd_lcm_left a b
      refine ⟨c, ?_⟩
      apply Nat.div_eq_of_eq_mul_left ha0
      calc L = Nat.lcm a b * (L / Nat.lcm a b) := (Nat.mul_div_cancel' hl).symm
        _ = a * c * (L / Nat.lcm a b) := by rw [← hc]
        _ = L / Nat.lcm a b * c * a := by ac_rfl
    · obtain ⟨c, hc⟩ := Nat.dvd_lcm_right a b
      refine ⟨c, ?_⟩
      apply Nat.div_eq_of_eq_mul_left hb0
      calc L = Nat.lcm a b * (L / Nat.lcm a b) := (Nat.mul_div_cancel' hl).symm
        _ = b * c * (L / Nat.lcm a b) := by rw [← hc]
        _ = L / Nat.lcm a b * c * b := by ac_rfl

/-- **Duality Transport.** `gcd (L/a) (L/b) · (a·b) = gcd a b · L`. -/
theorem transport_identity (L a b : ℕ) (hL : 0 < L) (ha : a ∣ L) (hb : b ∣ L)
    (ha0 : 0 < a) (hb0 : 0 < b) :
    Nat.gcd (L / a) (L / b) * (a * b) = Nat.gcd a b * L := by
  rw [gcd_div_div L a b hL ha hb ha0 hb0]
  have hl : Nat.lcm a b ∣ L := Nat.lcm_dvd ha hb
  have hgl : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have hLl : L / Nat.lcm a b * Nat.lcm a b = L := Nat.div_mul_cancel hl
  calc L / Nat.lcm a b * (a * b)
      = L / Nat.lcm a b * (Nat.gcd a b * Nat.lcm a b) := by rw [hgl]
    _ = Nat.gcd a b * (L / Nat.lcm a b * Nat.lcm a b) := by ring
    _ = Nat.gcd a b * L := by rw [hLl]

/-- The charge-term form: `gcd (L/a) (L/b) · a = gcd a b · (L/b)`, i.e.
`gcd(d_a, d_b)/d_a = gcd(a,b)/b` cleared of denominators. -/
theorem transport_term (L a b : ℕ) (hL : 0 < L) (ha : a ∣ L) (hb : b ∣ L)
    (ha0 : 0 < a) (hb0 : 0 < b) :
    Nat.gcd (L / a) (L / b) * a = Nat.gcd a b * (L / b) := by
  have h := transport_identity L a b hL ha hb ha0 hb0
  have hbL : b * (L / b) = L := Nat.mul_div_cancel' hb
  have hcan : (Nat.gcd (L / a) (L / b) * a) * b = (Nat.gcd a b * (L / b)) * b := by
    calc (Nat.gcd (L / a) (L / b) * a) * b
        = Nat.gcd (L / a) (L / b) * (a * b) := by ring
      _ = Nat.gcd a b * L := h
      _ = Nat.gcd a b * (b * (L / b)) := by rw [hbL]
      _ = (Nat.gcd a b * (L / b)) * b := by ring
  exact Nat.eq_of_mul_eq_mul_right hb0 hcan

/-- **Dual self-bad ⟺ primal bad.** For `a ∣ L` and a finite set `s` of
divisors of `L`: the dual vertex `L/a` is self-bad against `{L/x : x ∈ s}`
iff the `L`-cleared primal charge of `a` against `s` is at least `1`. -/
theorem dual_selfbad_iff (L a : ℕ) (hL : 0 < L) (ha : a ∣ L) (ha0 : 0 < a)
    (s : Finset ℕ) (hs : ∀ x ∈ s, x ∣ L) (hs0 : ∀ x ∈ s, 0 < x) :
    (L / a ≤ ∑ x ∈ s, Nat.gcd (L / a) (L / x))
      ↔ (L ≤ ∑ x ∈ s, Nat.gcd a x * (L / x)) := by
  have key : a * ∑ x ∈ s, Nat.gcd (L / a) (L / x)
      = ∑ x ∈ s, Nat.gcd a x * (L / x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have := transport_term L a x hL ha (hs x hx) ha0 (hs0 x hx)
    calc a * Nat.gcd (L / a) (L / x) = Nat.gcd (L / a) (L / x) * a := by ring
      _ = Nat.gcd a x * (L / x) := this
  have haL : a * (L / a) = L := Nat.mul_div_cancel' ha
  constructor
  · intro h
    calc L = a * (L / a) := haL.symm
      _ ≤ a * ∑ x ∈ s, Nat.gcd (L / a) (L / x) := Nat.mul_le_mul_left a h
      _ = ∑ x ∈ s, Nat.gcd a x * (L / x) := key
  · intro h
    have h' : a * (L / a) ≤ a * ∑ x ∈ s, Nat.gcd (L / a) (L / x) := by
      rw [haL, key]; exact h
    exact Nat.le_of_mul_le_mul_left h' ha0

end Erdos488
