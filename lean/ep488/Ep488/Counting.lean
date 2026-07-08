import Ep488.Basic

/-!
# Counting half: the finite-n Heilbronn–Rohrbach / 3-set Bonferroni bound

`B(n) ≥ s(n) − P₂(n)`, stated additively as `s(n) ≤ B(n) + P₂(n)` to avoid ℕ
subtraction.  This is the classical inequality (Heilbronn–Rohrbach 1937 at the
density level); here in finite-n form.
-/

namespace Erdos488

open Finset

/-- multiples of `d` in `(0, n]`. -/
def mult (d n : ℕ) : Finset ℕ := (Ioc 0 n).filter (fun k => d ∣ k)

@[simp] lemma mem_mult {d n k : ℕ} : k ∈ mult d n ↔ (0 < k ∧ k ≤ n) ∧ d ∣ k := by
  simp [mult, mem_filter, mem_Ioc]

/-- number of multiples of `d` in `[1,n]` is `⌊n/d⌋`. -/
lemma mult_card (d n : ℕ) : (mult d n).card = n / d := by
  simpa [mult] using Nat.Ioc_filter_dvd_card_eq_div n d

/-- `B(n)` for the triple `{a,b,c}`: the set of multiples in `(0,n]`. -/
def Bset (a b c n : ℕ) : Finset ℕ :=
  (Ioc 0 n).filter (fun k => a ∣ k ∨ b ∣ k ∨ c ∣ k)

/-- `Bset` is the union of the three multiple-sets. -/
lemma Bset_eq_union (a b c n : ℕ) :
    Bset a b c n = mult a n ∪ mult b n ∪ mult c n := by
  ext k
  simp only [Bset, mult, mem_filter, mem_union, mem_Ioc]
  tauto

/-- intersection of two multiple-sets is the multiples of the lcm. -/
lemma mult_inter (x y n : ℕ) : mult x n ∩ mult y n = mult (Nat.lcm x y) n := by
  ext k
  simp only [mem_mult, mem_inter]
  constructor
  · rintro ⟨⟨hk, hx⟩, ⟨_, hy⟩⟩
    exact ⟨hk, Nat.lcm_dvd hx hy⟩
  · rintro ⟨hk, hl⟩
    exact ⟨⟨hk, (Nat.dvd_lcm_left x y).trans hl⟩, ⟨hk, (Nat.dvd_lcm_right x y).trans hl⟩⟩

/-- s(n) = ⌊n/a⌋ + ⌊n/b⌋ + ⌊n/c⌋. -/
def sfun (a b c n : ℕ) : ℕ := n / a + n / b + n / c

/-- P₂(n) = ⌊n/lcm(a,b)⌋ + ⌊n/lcm(a,c)⌋ + ⌊n/lcm(b,c)⌋. -/
def p2fun (a b c n : ℕ) : ℕ :=
  n / Nat.lcm a b + n / Nat.lcm a c + n / Nat.lcm b c

/-- **Bonferroni (additive form).** `s(n) ≤ B(n) + P₂(n)`. -/
lemma bonferroni (a b c n : ℕ) :
    sfun a b c n ≤ (Bset a b c n).card + p2fun a b c n := by
  set Xa := mult a n
  set Xb := mult b n
  set Xc := mult c n
  have hB : (Bset a b c n).card = (Xa ∪ Xb ∪ Xc).card := by rw [Bset_eq_union]
  -- pairwise-lcm cardinalities
  have hab : (Xa ∩ Xb).card = n / Nat.lcm a b := by rw [mult_inter, mult_card]
  have hac : (Xa ∩ Xc).card = n / Nat.lcm a c := by rw [mult_inter, mult_card]
  have hbc : (Xb ∩ Xc).card = n / Nat.lcm b c := by rw [mult_inter, mult_card]
  -- inclusion-exclusion building blocks (all additive: no ℕ subtraction)
  have h1 : (Xa ∪ Xb).card + (Xa ∩ Xb).card = Xa.card + Xb.card :=
    Finset.card_union_add_card_inter Xa Xb
  have h2 : ((Xa ∪ Xb) ∪ Xc).card + ((Xa ∪ Xb) ∩ Xc).card = (Xa ∪ Xb).card + Xc.card :=
    Finset.card_union_add_card_inter (Xa ∪ Xb) Xc
  have h3 : ((Xa ∪ Xb) ∩ Xc).card ≤ (Xa ∩ Xc).card + (Xb ∩ Xc).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hca : Xa.card = n / a := mult_card a n
  have hcb : Xb.card = n / b := mult_card b n
  have hcc : Xc.card = n / c := mult_card c n
  simp only [sfun, p2fun, hB, hca, hcb, hcc, hab, hac, hbc] at *
  omega

/-- `lcm(x,y)/x = y/gcd(x,y)` and `lcm(x,y)/y = x/gcd(x,y)`; hence the ratio
bounds `≥ 3` and `≥ 2` for a primitive pair. -/
lemma lcm_ratio {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x < y) (hnd : ¬ x ∣ y) :
    3 ≤ Nat.lcm x y / x ∧ 2 ≤ Nat.lcm x y / y := by
  obtain ⟨h3, h2⟩ := ratio_bounds hx hxy hnd
  have hgy : Nat.gcd x y ∣ y := Nat.gcd_dvd_right x y
  have hgx : Nat.gcd x y ∣ x := Nat.gcd_dvd_left x y
  have ex : Nat.lcm x y / x = y / Nat.gcd x y := by
    have h : Nat.lcm x y = x * (y / Nat.gcd x y) := by
      rw [Nat.lcm, Nat.mul_div_assoc x hgy]
    rw [h, Nat.mul_div_cancel_left _ hx]
  have ey : Nat.lcm x y / y = x / Nat.gcd x y := by
    have h : Nat.lcm x y = (x / Nat.gcd x y) * y := by
      rw [Nat.lcm, Nat.mul_comm x y, Nat.mul_div_assoc y hgx, Nat.mul_comm]
    rw [h, Nat.mul_div_cancel _ hy]
  exact ⟨ex ▸ h3, ey ▸ h2⟩

/-- nested-floor identity: `n / lcm(x,y) = (n/x) / (lcm(x,y)/x)`. -/
lemma div_lcm_eq (n x y : ℕ) :
    n / Nat.lcm x y = n / x / (Nat.lcm x y / x) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' (Nat.dvd_lcm_left x y)]

/-- **Lemma 5 (charge).** For a primitive triple `a<b<c` in the uncovered zone
(`b*c < a*(b+c)`), `s(n) ≥ 2*P₂(n) + 3` for every `n ≥ c`. -/
lemma charge {a b c n : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcn : c ≤ n)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c)
    (hunc : b * c < a * (b + c)) :
    2 * p2fun a b c n + 3 ≤ sfun a b c n := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  -- t_a, t_b, t_c >= 1
  have hta : 1 ≤ n / a := Nat.one_le_div_iff ha |>.2 (by omega)
  have htb : 1 ≤ n / b := Nat.one_le_div_iff hb |>.2 (by omega)
  have htc : 1 ≤ n / c := Nat.one_le_div_iff hc |>.2 (by omega)
  -- ratio bounds
  obtain ⟨rab_a, rab_b⟩ := lcm_ratio ha hb hab hnab           -- lcm ab / a ≥3, / b ≥2
  obtain ⟨rac_a, rac_c⟩ := lcm_ratio ha hc (hab.trans hbc) hnac -- lcm ac / a ≥3, / c ≥2
  obtain ⟨rbc_b, rbc_c⟩ := lcm_ratio hb hc hbc hnbc            -- lcm bc / b ≥3, / c ≥2
  -- parity dichotomy: not both lcm(a,c)/c=2 and lcm(b,c)/c=2
  have hpar : ¬ (Nat.lcm a c = 2 * c ∧ Nat.lcm b c = 2 * c) :=
    parity_dichotomy ha hab hbc hnac hnbc hunc
  -- nested-floor identities (both sides for each lcm)
  have iab_a := div_lcm_eq n a b
  have iac_a := div_lcm_eq n a c
  have ibc_b := div_lcm_eq n b c
  have iab_b : n / Nat.lcm a b = n / b / (Nat.lcm a b / b) := by
    rw [Nat.lcm_comm]; exact div_lcm_eq n b a
  have iac_c : n / Nat.lcm a c = n / c / (Nat.lcm a c / c) := by
    rw [Nat.lcm_comm]; exact div_lcm_eq n c a
  have ibc_c : n / Nat.lcm b c = n / c / (Nat.lcm b c / c) := by
    rw [Nat.lcm_comm]; exact div_lcm_eq n c b
  -- X_a ≥ 1: ratios (≥3,≥3)
  have Xa : 1 ≤ n / a - n / a / (Nat.lcm a b / a) - n / a / (Nat.lcm a c / a) :=
    floor_bound hta (by omega) rac_a
  -- X_b ≥ 1: ratios (≥2,≥3)
  have Xb : 1 ≤ n / b - n / b / (Nat.lcm a b / b) - n / b / (Nat.lcm b c / b) :=
    floor_bound htb rab_b rbc_b
  -- X_c ≥ 1: ratios (≥2,≥2), one ≥3 by parity
  have hc3 : 3 ≤ Nat.lcm a c / c ∨ 3 ≤ Nat.lcm b c / c := by
    by_contra h
    push_neg at h
    obtain ⟨hac2, hbc2⟩ := h
    apply hpar
    refine ⟨?_, ?_⟩
    · have hd : c ∣ Nat.lcm a c := Nat.dvd_lcm_right a c
      have he : Nat.lcm a c / c = 2 := by omega
      rw [← Nat.mul_div_cancel' hd, he]; ring
    · have hd : c ∣ Nat.lcm b c := Nat.dvd_lcm_right b c
      have he : Nat.lcm b c / c = 2 := by omega
      rw [← Nat.mul_div_cancel' hd, he]; ring
  have Xc : 1 ≤ n / c - n / c / (Nat.lcm a c / c) - n / c / (Nat.lcm b c / c) := by
    rcases hc3 with h | h
    · have hh := floor_bound htc rbc_c h; omega
    · exact floor_bound htc rac_c h
  -- assemble: feed all charge inequalities + nested-floor identities to omega
  simp only [sfun, p2fun]
  omega

/-- **Clean per-n criterion.** For an uncovered primitive triple and `n ≥ c`,
`2·B(n) ≥ s(n) + 3` (combining Bonferroni and the charge bound eliminates `P₂`). -/
lemma two_B_ge {a b c n : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcn : c ≤ n)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c)
    (hunc : b * c < a * (b + c)) :
    sfun a b c n + 3 ≤ 2 * (Bset a b c n).card := by
  have hbonf := bonferroni a b c n
  have hch := charge ha hab hbc hcn hnab hnac hnbc hunc
  omega

/-- Union bound: `B(m) ≤ s(m)`. -/
lemma B_le_s (a b c m : ℕ) : (Bset a b c m).card ≤ sfun a b c m := by
  rw [Bset_eq_union, sfun]
  calc (mult a m ∪ mult b m ∪ mult c m).card
      ≤ (mult a m ∪ mult b m).card + (mult c m).card := Finset.card_union_le _ _
    _ ≤ (mult a m).card + (mult b m).card + (mult c m).card := by
        have := Finset.card_union_le (mult a m) (mult b m); omega
    _ = m / a + m / b + m / c := by rw [mult_card, mult_card, mult_card]

/-- **Theorem 8 (integer form).** For an uncovered primitive triple and `n ≥ c`,
`n·(bc+ac+ab) < 2·B(n)·abc`, i.e. `2·B(n)/n > S`. -/
lemma two_B_gt_nS {a b c n : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcn : c ≤ n)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c)
    (hunc : b * c < a * (b + c)) :
    n * (b * c + a * c + a * b) < 2 * (Bset a b c n).card * (a * b * c) := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have h2B := two_B_ge ha hab hbc hcn hnab hnac hnbc hunc
  -- s(n)*abc + (bc*(n%a)+ac*(n%b)+ab*(n%c)) = n*(bc+ac+ab)
  have keyeq :
      a * b * c * (n / a + n / b + n / c) + (b * c * (n % a) + a * c * (n % b) + a * b * (n % c))
        = n * (b * c + a * c + a * b) := by
    have da := Nat.div_add_mod n a
    have db := Nat.div_add_mod n b
    have dc := Nat.div_add_mod n c
    calc a * b * c * (n / a + n / b + n / c)
            + (b * c * (n % a) + a * c * (n % b) + a * b * (n % c))
        = b * c * (a * (n / a) + n % a) + a * c * (b * (n / b) + n % b)
            + a * b * (c * (n / c) + n % c) := by ring
      _ = b * c * n + a * c * n + a * b * n := by rw [da, db, dc]
      _ = n * (b * c + a * c + a * b) := by ring
  have ma : n % a < a := Nat.mod_lt n ha
  have mb : n % b < b := Nat.mod_lt n hb
  have mc : n % c < c := Nat.mod_lt n hc
  simp only [sfun] at h2B
  nlinarith [keyeq, h2B, ma, mb, mc,
    mul_lt_mul_of_pos_left ma (Nat.mul_pos hb hc),
    mul_lt_mul_of_pos_left mb (Nat.mul_pos ha hc),
    mul_lt_mul_of_pos_left mc (Nat.mul_pos ha hb),
    Nat.mul_le_mul_right (a * b * c) h2B]

/-- **EP488 for an uncovered primitive triple.** For all `m > n ≥ c`,
`n·B(m) < 2·m·B(n)`. -/
theorem ep488_uncovered_triple {a b c n m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c)
    (hunc : b * c < a * (b + c)) (hn : c ≤ n) (hm : n < m) :
    n * (Bset a b c m).card < 2 * m * (Bset a b c n).card := by
  have ha' : 0 < a := ha
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have habc : 0 < a * b * c := by positivity
  -- union bound at m:  B(m)*abc ≤ m*(bc+ac+ab)
  have hub : (Bset a b c m).card * (a * b * c) ≤ m * (b * c + a * c + a * b) := by
    have hBs := B_le_s a b c m
    have hs : sfun a b c m * (a * b * c) ≤ m * (b * c + a * c + a * b) := by
      simp only [sfun]
      have h1 := mul_le_mul_right' (Nat.div_mul_le_self m a) (b * c)
      have h2 := mul_le_mul_right' (Nat.div_mul_le_self m b) (a * c)
      have h3 := mul_le_mul_right' (Nat.div_mul_le_self m c) (a * b)
      nlinarith [h1, h2, h3]
    calc (Bset a b c m).card * (a * b * c)
        ≤ sfun a b c m * (a * b * c) := Nat.mul_le_mul_right _ hBs
      _ ≤ m * (b * c + a * c + a * b) := hs
  -- Theorem 8 at n:  n*(bc+ac+ab) < 2*B(n)*abc
  have hlow := two_B_gt_nS ha hab hbc hn hnab hnac hnbc hunc
  have hm0 : 0 < m := by omega
  -- combine (cancel abc):  n*B(m) < 2*m*B(n)
  have s1 : n * ((Bset a b c m).card * (a * b * c)) ≤ n * (m * (b * c + a * c + a * b)) :=
    Nat.mul_le_mul_left n hub
  have s2 : m * (n * (b * c + a * c + a * b)) < m * (2 * (Bset a b c n).card * (a * b * c)) :=
    mul_lt_mul_of_pos_left hlow hm0
  have key : n * (Bset a b c m).card * (a * b * c)
      < 2 * m * (Bset a b c n).card * (a * b * c) := by
    calc n * (Bset a b c m).card * (a * b * c)
        = n * ((Bset a b c m).card * (a * b * c)) := by ring
      _ ≤ n * (m * (b * c + a * c + a * b)) := s1
      _ = m * (n * (b * c + a * c + a * b)) := by ring
      _ < m * (2 * (Bset a b c n).card * (a * b * c)) := s2
      _ = 2 * m * (Bset a b c n).card * (a * b * c) := by ring
  exact lt_of_mul_lt_mul_right key (Nat.zero_le _)

end Erdos488
