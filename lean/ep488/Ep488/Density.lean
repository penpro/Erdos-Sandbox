import Mathlib

/-!
# The size-5 density inequality `2δ > S` (second-order charge) — floor-free form

`2δ − S = S − 2P₂ + 2T₃ − 2T₄ + 2T₅` is an explicit rational in the pairwise/triple/…
lcms of a primitive quintuple, so `2δ > S` is a *finite algebraic* inequality — no
asymptotic-density machinery. This file formalizes the second-order-charge proof:

* `E4` — the kernel `Σ_{T⊆{1,2,3,4}} (−1)^{|T|}/((|T|+1)·lcm(m_T))`, i.e. `E[1/(1+X)]`;
* the per-element decomposition `Σ_a term_a = Q(P)` (pure `ring` identity), with
  `term_a = 2·brX − 1/x`, and the assembly `Q(P) > 0` from `x·brX ≥ 157/300` (each
  element's `E4` of reduced friends).

The one arithmetic input `E4 ≥ 157/300` (a finite lemma, exhaustively verified) is the
remaining brick; the reduction around it is machine-checked here.

Companion to `../../quintuple_density_notes.md`.
-/

namespace Erdos488.Density

open scoped BigOperators

/-- `1/x` as a rational (singleton reciprocal). -/
def inv (x : ℕ) : ℚ := (x : ℚ)⁻¹
/-- `1/lcm(x,y)`. -/
def L2 (x y : ℕ) : ℚ := ((Nat.lcm x y : ℕ) : ℚ)⁻¹
/-- `1/lcm(x,y,z)`. -/
def L3 (x y z : ℕ) : ℚ := ((Nat.lcm (Nat.lcm x y) z : ℕ) : ℚ)⁻¹
/-- `1/lcm(x,y,z,w)`. -/
def L4 (x y z w : ℕ) : ℚ := ((Nat.lcm (Nat.lcm (Nat.lcm x y) z) w : ℕ) : ℚ)⁻¹
/-- `1/lcm(x,y,z,w,v)`. -/
def L5 (x y z w v : ℕ) : ℚ := ((Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm x y) z) w) v : ℕ) : ℚ)⁻¹

/-- Second-order-charge kernel `E4 = Σ_T (−1)^{|T|}/((|T|+1)·lcm(m_T)) = E[1/(1+X)]`. -/
noncomputable def E4 (m1 m2 m3 m4 : ℕ) : ℚ :=
  1 - (1/2) * (inv m1 + inv m2 + inv m3 + inv m4)
  + (1/3) * (L2 m1 m2 + L2 m1 m3 + L2 m1 m4 + L2 m2 m3 + L2 m2 m4 + L2 m3 m4)
  - (1/4) * (L3 m1 m2 m3 + L3 m1 m2 m4 + L3 m1 m3 m4 + L3 m2 m3 m4)
  + (1/5) * (L4 m1 m2 m3 m4)

/-- The witnessing minimum: `E4 2 2 3 5 = 157/300`. -/
example : E4 2 2 3 5 = 157/300 := by
  unfold E4 inv L2 L3 L4; norm_num [Nat.lcm]

/-! ## Per-element brackets (canonical lcm order) and `Q(P)` -/

/-- Element-`a` bracket: `1/a − (1/2)Σ 1/lcm(a,f) + (1/3)Σ 1/lcm(a,f,g) − (1/4)Σ … + (1/5)/lcm`.
Note `a · brA = E4` of `a`'s four reduced friends. -/
def brA (a b c d e : ℕ) : ℚ :=
  inv a - (1/2) * (L2 a b + L2 a c + L2 a d + L2 a e)
  + (1/3) * (L3 a b c + L3 a b d + L3 a b e + L3 a c d + L3 a c e + L3 a d e)
  - (1/4) * (L4 a b c d + L4 a b c e + L4 a b d e + L4 a c d e)
  + (1/5) * (L5 a b c d e)

def brB (a b c d e : ℕ) : ℚ :=
  inv b - (1/2) * (L2 a b + L2 b c + L2 b d + L2 b e)
  + (1/3) * (L3 a b c + L3 a b d + L3 a b e + L3 b c d + L3 b c e + L3 b d e)
  - (1/4) * (L4 a b c d + L4 a b c e + L4 a b d e + L4 b c d e)
  + (1/5) * (L5 a b c d e)

def brC (a b c d e : ℕ) : ℚ :=
  inv c - (1/2) * (L2 a c + L2 b c + L2 c d + L2 c e)
  + (1/3) * (L3 a b c + L3 a c d + L3 a c e + L3 b c d + L3 b c e + L3 c d e)
  - (1/4) * (L4 a b c d + L4 a b c e + L4 a c d e + L4 b c d e)
  + (1/5) * (L5 a b c d e)

def brD (a b c d e : ℕ) : ℚ :=
  inv d - (1/2) * (L2 a d + L2 b d + L2 c d + L2 d e)
  + (1/3) * (L3 a b d + L3 a c d + L3 a d e + L3 b c d + L3 b d e + L3 c d e)
  - (1/4) * (L4 a b c d + L4 a b d e + L4 a c d e + L4 b c d e)
  + (1/5) * (L5 a b c d e)

def brE (a b c d e : ℕ) : ℚ :=
  inv e - (1/2) * (L2 a e + L2 b e + L2 c e + L2 d e)
  + (1/3) * (L3 a b e + L3 a c e + L3 a d e + L3 b c e + L3 b d e + L3 c d e)
  - (1/4) * (L4 a b c e + L4 a b d e + L4 a c d e + L4 b c d e)
  + (1/5) * (L5 a b c d e)

/-- `Q(P) = S − 2P₂ + 2T₃ − 2T₄ + 2T₅ = 2δ − S`. -/
def Q (a b c d e : ℕ) : ℚ :=
  (inv a + inv b + inv c + inv d + inv e)
  - 2 * (L2 a b + L2 a c + L2 a d + L2 a e + L2 b c + L2 b d + L2 b e + L2 c d + L2 c e + L2 d e)
  + 2 * (L3 a b c + L3 a b d + L3 a b e + L3 a c d + L3 a c e + L3 a d e
        + L3 b c d + L3 b c e + L3 b d e + L3 c d e)
  - 2 * (L4 a b c d + L4 a b c e + L4 a b d e + L4 a c d e + L4 b c d e)
  + 2 * (L5 a b c d e)

/-- **Decomposition identity.** The five per-element second-order-charge terms
`term_x = 2·brX − 1/x` sum to `Q(P)`. Pure ring identity in the `1/lcm` atoms. -/
theorem sum_terms_eq_Q (a b c d e : ℕ) :
    (2 * brA a b c d e - inv a) + (2 * brB a b c d e - inv b) + (2 * brC a b c d e - inv c)
      + (2 * brD a b c d e - inv d) + (2 * brE a b c d e - inv e)
    = Q a b c d e := by
  unfold brA brB brC brD brE Q; ring

/-- If `157/300 ≤ x·br` and `x > 0`, then the term `2·br − 1/x ≥ 7/(150 x) > 0`. -/
theorem term_pos {x : ℕ} (hx : 0 < x) {br : ℚ} (h : (157 : ℚ)/300 ≤ (x : ℚ) * br) :
    0 < 2 * br - inv x := by
  have hxq : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
  have hxne : (x : ℚ) ≠ 0 := ne_of_gt hxq
  have key : (x : ℚ) * (2 * br - inv x) = 2 * ((x : ℚ) * br) - 1 := by
    unfold inv; field_simp
  have hpos : (0 : ℚ) < (x : ℚ) * (2 * br - inv x) := by rw [key]; linarith
  exact (mul_pos_iff_of_pos_left hxq).mp hpos

/-- **Conditional density inequality.** For five positive integers, if each element's
`E4` of its reduced friends (`= x · brX`) is `≥ 157/300`, then `Q(P) = 2δ − S > 0`.
The hypotheses are exactly the four-modulus finite lemma applied at each element. -/
theorem Q_pos_of_E4_bounds (a b c d e : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : (157 : ℚ)/300 ≤ (a : ℚ) * brA a b c d e)
    (hB : (157 : ℚ)/300 ≤ (b : ℚ) * brB a b c d e)
    (hC : (157 : ℚ)/300 ≤ (c : ℚ) * brC a b c d e)
    (hD : (157 : ℚ)/300 ≤ (d : ℚ) * brD a b c d e)
    (hE : (157 : ℚ)/300 ≤ (e : ℚ) * brE a b c d e) :
    0 < Q a b c d e := by
  have tA := term_pos ha hA
  have tB := term_pos hb hB
  have tC := term_pos hc hC
  have tD := term_pos hd hD
  have tE := term_pos he hE
  rw [← sum_terms_eq_Q]
  linarith

end Erdos488.Density
