import Ep488.Counting

/-!
# General finite set `A`, and the singleton / pair cases

`Bgen A n` is the set of elements of `(0,n]` divisible by *some* member of the
finite set `A` — i.e. `B_A(n)` for arbitrary `A`.  This file specialises it to
`{a}`, `{a,b}`, `{a,b,c}` (reconciling with `Bset`), proves EP488 for the
singleton and pair cases by the union bound, and is the staging ground for the
primitive-core reduction.
-/

namespace Erdos488

open Finset

/-- `B_A(n)`: elements of `(0,n]` divisible by some member of the finite set `A`. -/
def Bgen (A : Finset ℕ) (n : ℕ) : Finset ℕ := A.biUnion (fun a => mult a n)

@[simp] lemma mem_Bgen {A : Finset ℕ} {n k : ℕ} :
    k ∈ Bgen A n ↔ (0 < k ∧ k ≤ n) ∧ ∃ a ∈ A, a ∣ k := by
  simp only [Bgen, Finset.mem_biUnion, mem_mult]
  constructor
  · rintro ⟨a, ha, hk, hd⟩; exact ⟨hk, a, ha, hd⟩
  · rintro ⟨hk, a, ha, hd⟩; exact ⟨a, ha, hk, hd⟩

/-- Singleton: `B_{a}(n)` is exactly the multiples of `a`. -/
lemma Bgen_singleton (a n : ℕ) : Bgen {a} n = mult a n := by
  simp [Bgen]

/-- Triple: `B_{a,b,c}(n)` reconciles with `Bset`. -/
lemma Bgen_triple (a b c n : ℕ) : Bgen {a, b, c} n = Bset a b c n := by
  ext k
  simp only [mem_Bgen, Bset, mem_filter, mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, x, hx, hd⟩
    refine ⟨hk, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hd)
  · rintro ⟨hk, hd⟩
    refine ⟨hk, ?_⟩
    rcases hd with hd | hd | hd
    · exact ⟨a, Or.inl rfl, hd⟩
    · exact ⟨b, Or.inr (Or.inl rfl), hd⟩
    · exact ⟨c, Or.inr (Or.inr rfl), hd⟩

/-- **EP488, singleton case** `A = {a}`.  Pure floor arithmetic:
`a·B(m) ≤ m` and `a·B(n) ≥ n − (n%a)` with `n%a < a ≤ a·⌊n/a⌋`. -/
theorem ep488_singleton {a n m : ℕ} (ha : 0 < a) (hn : a ≤ n) (hm : n < m) :
    n * (Bgen {a} m).card < 2 * m * (Bgen {a} n).card := by
  rw [Bgen_singleton, Bgen_singleton, mult_card, mult_card]
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
  have h1 : a * (m / a) ≤ m := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m a
  have h2 : a * (n / a) + n % a = n := Nat.div_add_mod n a
  have h3 : n % a < a := Nat.mod_lt n ha
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).2 hn
  have hae : a ≤ a * (n / a) := Nat.le_mul_of_pos_right a hq
  have hrT : n % a < a * (n / a) := lt_of_lt_of_le h3 hae
  have key : a * (n * (m / a)) < a * (2 * m * (n / a)) := by
    have e1 : a * (n * (m / a)) = n * (a * (m / a)) := by ring
    have e2 : a * (2 * m * (n / a)) = 2 * m * (a * (n / a)) := by ring
    rw [e1, e2]
    have t1 : n * (a * (m / a)) ≤ n * m := Nat.mul_le_mul_left n h1
    have t2 : n * m < 2 * m * (a * (n / a)) := by nlinarith [h2, hrT, hm0]
    exact lt_of_le_of_lt t1 t2
  exact Nat.lt_of_mul_lt_mul_left key

/-- Pair: `B_{a,b}(n)` is the union of the two multiple-sets. -/
lemma Bgen_pair_eq (a b n : ℕ) : Bgen {a, b} n = mult a n ∪ mult b n := by
  ext k
  simp only [mem_Bgen, Finset.mem_union, mem_mult, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, x, hx, hd⟩
    rcases hx with rfl | rfl
    · exact Or.inl ⟨hk, hd⟩
    · exact Or.inr ⟨hk, hd⟩
  · rintro (⟨hk, hd⟩ | ⟨hk, hd⟩)
    · exact ⟨hk, a, Or.inl rfl, hd⟩
    · exact ⟨hk, b, Or.inr rfl, hd⟩

/-- Pair union bound: `B_{a,b}(n) ≥ ⌊n/a⌋ + 1`, the `+1` supplied by `b ∉ mult a n`
(uses primitivity `¬ a ∣ b`). -/
lemma Bgen_ge_floor_add_one {a b n : ℕ} (hbpos : 0 < b) (hb : b ≤ n) (hnab : ¬ a ∣ b) :
    n / a + 1 ≤ (Bgen {a, b} n).card := by
  have hsub : mult a n ⊆ Bgen {a, b} n := by
    intro k hk; rw [mem_mult] at hk; rw [mem_Bgen]
    exact ⟨hk.1, a, by simp, hk.2⟩
  have hbmem : b ∈ Bgen {a, b} n := by
    rw [mem_Bgen]; exact ⟨⟨hbpos, hb⟩, b, by simp, dvd_rfl⟩
  have hbnot : b ∉ mult a n := by rw [mem_mult]; rintro ⟨_, h⟩; exact hnab h
  have hins : insert b (mult a n) ⊆ Bgen {a, b} n := Finset.insert_subset hbmem hsub
  calc n / a + 1 = (mult a n).card + 1 := by rw [mult_card]
    _ = (insert b (mult a n)).card := by rw [Finset.card_insert_of_notMem hbnot]
    _ ≤ (Bgen {a, b} n).card := Finset.card_le_card hins

/-- **EP488, pair case** `A = {a,b}`, `a < b`, `¬ a ∣ b`.  Union bound only:
`a·B(n) > n` (lower) and `ab·B(m) ≤ m(a+b)` (upper); combine using `a + b ≤ 2b`. -/
theorem ep488_pair {a b n m : ℕ} (ha : 0 < a) (hab : a < b) (hnab : ¬ a ∣ b)
    (hn : b ≤ n) (hm : n < m) :
    n * (Bgen {a, b} m).card < 2 * m * (Bgen {a, b} n).card := by
  have hb : 0 < b := ha.trans hab
  have hm0 : 0 < m := by omega
  -- (i) a * B(n) > n
  have hlow : n / a + 1 ≤ (Bgen {a, b} n).card := Bgen_ge_floor_add_one hb hn hnab
  have haBn : n < a * (Bgen {a, b} n).card := by
    have hd := Nat.div_add_mod n a
    have hmod := Nat.mod_lt n ha
    have hh := Nat.mul_le_mul_left a hlow
    nlinarith [hh, hd, hmod]
  -- (ii) a*b * B(m) ≤ m*(a+b)
  have hupp : a * b * (Bgen {a, b} m).card ≤ m * (a + b) := by
    have hcard : (Bgen {a, b} m).card ≤ (mult a m).card + (mult b m).card := by
      rw [Bgen_pair_eq]; exact Finset.card_union_le _ _
    rw [mult_card, mult_card] at hcard
    have e1 : a * (m / a) ≤ m := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m a
    have e2 : b * (m / b) ≤ m := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m b
    calc a * b * (Bgen {a, b} m).card
        ≤ a * b * (m / a + m / b) := Nat.mul_le_mul_left (a * b) hcard
      _ = b * (a * (m / a)) + a * (b * (m / b)) := by ring
      _ ≤ b * m + a * m := by
          have hb1 := Nat.mul_le_mul_left b e1
          have ha2 := Nat.mul_le_mul_left a e2
          omega
      _ = m * (a + b) := by ring
  -- combine (cancel a*b)
  have h2m : 0 < 2 * m := by omega
  have h2mb : 0 < 2 * m * b := Nat.mul_pos h2m hb
  have key : a * b * (n * (Bgen {a, b} m).card) < a * b * (2 * m * (Bgen {a, b} n).card) := by
    have L : a * b * (n * (Bgen {a, b} m).card) = n * (a * b * (Bgen {a, b} m).card) := by ring
    have R : a * b * (2 * m * (Bgen {a, b} n).card)
        = 2 * m * b * (a * (Bgen {a, b} n).card) := by ring
    rw [L, R]
    calc n * (a * b * (Bgen {a, b} m).card)
        ≤ n * (m * (a + b)) := Nat.mul_le_mul_left n hupp
      _ = m * (n * (a + b)) := by ring
      _ ≤ m * (n * (2 * b)) := Nat.mul_le_mul_left m (Nat.mul_le_mul_left n (by omega))
      _ = 2 * m * b * n := by ring
      _ < 2 * m * b * (a * (Bgen {a, b} n).card) := mul_lt_mul_of_pos_left haBn h2mb
  exact Nat.lt_of_mul_lt_mul_left key

/-! ## Primitive core reduction -/

/-- The **primitive core** of a finite set: its `∣`-minimal elements. -/
def core (A : Finset ℕ) : Finset ℕ := A.filter (fun a => ∀ b ∈ A, b ∣ a → b = a)

lemma mem_core {A : Finset ℕ} {a : ℕ} :
    a ∈ core A ↔ a ∈ A ∧ ∀ b ∈ A, b ∣ a → b = a := by
  simp [core, Finset.mem_filter]

lemma core_subset (A : Finset ℕ) : core A ⊆ A := Finset.filter_subset _ _

/-- Every element of `A` is a multiple of some core element (take the smallest
divisor of `a` lying in `A`). -/
lemma exists_core_dvd {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) {a : ℕ} (ha : a ∈ A) :
    ∃ b ∈ core A, b ∣ a := by
  have hne : (A.filter (fun b => b ∣ a)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, dvd_rfl⟩⟩
  obtain ⟨hbA, hbda⟩ := Finset.mem_filter.mp ((A.filter (fun b => b ∣ a)).min'_mem hne)
  refine ⟨(A.filter (fun b => b ∣ a)).min' hne, ?_, hbda⟩
  rw [mem_core]
  refine ⟨hbA, ?_⟩
  intro c hcA hcb
  have hbpos : 0 < (A.filter (fun b => b ∣ a)).min' hne := hpos _ hbA
  have hcS : c ∈ A.filter (fun b => b ∣ a) := Finset.mem_filter.mpr ⟨hcA, hcb.trans hbda⟩
  have hble : (A.filter (fun b => b ∣ a)).min' hne ≤ c := Finset.min'_le _ c hcS
  have hcle : c ≤ (A.filter (fun b => b ∣ a)).min' hne := Nat.le_of_dvd hbpos hcb
  omega

/-- **Core invariance of `B`.** `B_A(n) = B_{core A}(n)`. -/
lemma Bgen_core_eq {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) (n : ℕ) :
    Bgen A n = Bgen (core A) n := by
  ext k
  simp only [mem_Bgen]
  constructor
  · rintro ⟨hk, a, ha, hd⟩
    obtain ⟨b, hbcore, hbda⟩ := exists_core_dvd hpos ha
    exact ⟨hk, b, hbcore, hbda.trans hd⟩
  · rintro ⟨hk, a, ha, hd⟩
    exact ⟨hk, a, core_subset A ha, hd⟩

/-- The core is a `∣`-antichain: distinct core elements never divide each other. -/
lemma core_antichain {A : Finset ℕ} {x y : ℕ}
    (hx : x ∈ core A) (hy : y ∈ core A) (hxy : x ≠ y) : ¬ x ∣ y := by
  intro hdvd
  rw [mem_core] at hy
  exact hxy (hy.2 x (core_subset A hx) hdvd)

/-- Core elements are positive. -/
lemma core_pos {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) {a : ℕ} (ha : a ∈ core A) : 0 < a :=
  hpos a (core_subset A ha)

/-- EP488 for an explicitly sorted primitive triple, in `Bgen` form. -/
lemma ep488_sorted {x y z n m : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnxy : ¬ x ∣ y) (hnxz : ¬ x ∣ z) (hnyz : ¬ y ∣ z) (hn : z ≤ n) (hm : n < m) :
    n * (Bgen {x, y, z} m).card < 2 * m * (Bgen {x, y, z} n).card := by
  rw [Bgen_triple, Bgen_triple]
  exact ep488_triple hx hxy hyz hnxy hnxz hnyz hn hm

/-- **EP488 for any positive `∣`-antichain `P` of size ≤ 3.** -/
theorem ep488_primitive {P : Finset ℕ} (hpos : ∀ a ∈ P, 0 < a)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ x ∣ y)
    (hcard : P.card ≤ 3) (hne : P.Nonempty)
    {n m : ℕ} (hn : ∀ a ∈ P, a ≤ n) (hm : n < m) :
    n * (Bgen P m).card < 2 * m * (Bgen P n).card := by
  have h1 : 1 ≤ P.card := Finset.card_pos.mpr hne
  rcases (by omega : P.card = 1 ∨ P.card = 2 ∨ P.card = 3) with h | h | h
  · -- singleton
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
    have hxmem : x ∈ P := by rw [hx]; exact Finset.mem_singleton_self x
    rw [hx]
    exact ep488_singleton (hpos x hxmem) (hn x hxmem) hm
  · -- pair
    obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp h
    have hamem : a ∈ P := by rw [hP]; simp
    have hbmem : b ∈ P := by rw [hP]; simp
    rw [hP]
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact ep488_pair (hpos a hamem) hlt (hanti a hamem b hbmem hab) (hn b hbmem) hm
    · have hba : b < a := lt_of_le_of_ne hge (Ne.symm hab)
      rw [Finset.pair_comm]
      exact ep488_pair (hpos b hbmem) hba (hanti b hbmem a hamem (Ne.symm hab)) (hn a hamem) hm
  · -- triple: extract min' < middle < max'
    have hxz : P.min' hne < P.max' hne := Finset.min'_lt_max'_of_card P (by omega)
    set x := P.min' hne with hxdef
    set z := P.max' hne with hzdef
    have hxmem : x ∈ P := P.min'_mem hne
    have hzmem : z ∈ P := P.max'_mem hne
    have hz_in_erase : z ∈ P.erase x := Finset.mem_erase.mpr ⟨(ne_of_lt hxz).symm, hzmem⟩
    have herase : ((P.erase x).erase z).card = 1 := by
      have e1 := Finset.card_erase_of_mem hz_in_erase
      have e2 := Finset.card_erase_of_mem hxmem
      omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp herase
    have hy_mem_er : y ∈ (P.erase x).erase z := by rw [hy]; exact Finset.mem_singleton_self y
    have hyz_ne : y ≠ z := (Finset.mem_erase.mp hy_mem_er).1
    have hy_in_ex : y ∈ P.erase x := (Finset.mem_erase.mp hy_mem_er).2
    have hyx_ne : y ≠ x := (Finset.mem_erase.mp hy_in_ex).1
    have hymem : y ∈ P := (Finset.mem_erase.mp hy_in_ex).2
    have hxy : x < y := lt_of_le_of_ne (Finset.min'_le _ y hymem) (fun hc => hyx_ne hc.symm)
    have hyz : y < z := lt_of_le_of_ne (Finset.le_max' _ y hymem) hyz_ne
    have hcard3 : ({x, y, z} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.2 ⟨x, y, z, ne_of_lt hxy, ne_of_lt hxz, ne_of_lt hyz, rfl⟩
    have hsub : ({x, y, z} : Finset ℕ) ⊆ P := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxmem
      · exact hymem
      · exact hzmem
    have hset : ({x, y, z} : Finset ℕ) = P :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard3]; omega)
    rw [← hset]
    exact ep488_sorted (hpos x hxmem) hxy hyz
      (hanti x hxmem y hymem (ne_of_lt hxy))
      (hanti x hxmem z hzmem (ne_of_lt hxz))
      (hanti y hymem z hzmem (ne_of_lt hyz))
      (hn z hzmem) hm

/-- **EP488 for every finite `A` of positive integers whose primitive core has
size ≤ 3.**  `n·B_A(m) < 2·m·B_A(n)` for all `m > n ≥ max A`, i.e.
`B_A(m)/m < 2·B_A(n)/n`. -/
theorem ep488_core {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a)
    (hAne : A.Nonempty) (hcore : (core A).card ≤ 3)
    {n m : ℕ} (hn : ∀ a ∈ A, a ≤ n) (hm : n < m) :
    n * (Bgen A m).card < 2 * m * (Bgen A n).card := by
  rw [Bgen_core_eq hpos m, Bgen_core_eq hpos n]
  have hcne : (core A).Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb, _⟩ := exists_core_dvd hpos ha
    exact ⟨b, hb⟩
  exact ep488_primitive (fun a ha => core_pos hpos ha)
    (fun x hx y hy hxy => core_antichain hx hy hxy)
    hcore hcne (fun a ha => hn a (core_subset A ha)) hm

end Erdos488
