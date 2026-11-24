import Goldbach.WilliamsonMurIIExtensions

/-! # Mur II — simultaneous bound for k deficient lines

For a bad family at rank `P` and any finite set `D` of deficient lines,
the product of the complements `N - i` (`i ∈ D`) divides an explicit
number `deficitBudget P #D` depending only on `P` and `#D`. Consequently
`(N - P) ^ #D ≤ deficitBudget P #D`.

No `sorry`, no axiom. -/

namespace WilliamsonMurII
open Finset

/-- Exponent of the prime `r` allowed in a product of `k` deficient complements. -/
def deficitExponent (P k r : ℕ) : ℕ :=
  ∑ a ∈ Ico 1 P, if 2 * r ^ a ≤ P - 3 then min k ((P - 3) / (2 * r ^ a) + 1) else 0

/-- Explicit budget: `∏_{r < P prime} r ^ deficitExponent P k r`. -/
def deficitBudget (P k : ℕ) : ℕ :=
  ∏ r ∈ (range P).filter Nat.Prime, r ^ deficitExponent P k r

theorem idx_odd {P i : ℕ} (hi : Index P i) : i % 2 = 1 := by
  rcases hi.1.eq_two_or_odd with h | h
  · have := hi.2.1
    omega
  · exact h

theorem compl_odd {P N i : ℕ} (hb : BadFamily P N) (hi : Index P i) :
    (N - i) % 2 = 1 := by
  have hN := hb.1
  have hiP := hi.2.2
  have ho := idx_odd hi
  obtain ⟨k, hk⟩ := hb.2.1
  omega

/-- Two indices whose complements share an odd divisor `t` differ by a
    multiple of `2t`. -/
theorem same_class {P N t i j : ℕ} (hN : P < N) (hi : Index P i) (hj : Index P j)
    (ht : t % 2 = 1) (hdi : t ∣ N - i) (hdj : t ∣ N - j) (hij : i ≤ j) :
    ∃ c, j = i + 2 * t * c := by
  have hd := dvd_difference N i j t (le_trans hi.2.2 (le_of_lt hN))
    (le_trans hj.2.2 (le_of_lt hN)) hdi hdj
  rw [max_eq_right hij, min_eq_left hij] at hd
  have h2 : 2 ∣ j - i := by
    have := idx_odd hi
    have := idx_odd hj
    omega
  have hcop : Nat.Coprime 2 t := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  obtain ⟨c, hc⟩ := hcop.mul_dvd_of_dvd_of_dvd h2 hd
  exact ⟨c, by omega⟩

/-- Class bound: at most `(P-3)/(2t) + 1` lines share an odd divisor `t`. -/
theorem class_count {P N t : ℕ} (D : Finset ℕ) (hN : P < N)
    (hD : ∀ i ∈ D, Index P i) (ht : t % 2 = 1) :
    #{i ∈ D | t ∣ N - i} ≤ (P - 3) / (2 * t) + 1 := by
  classical
  have ht0 : 0 < 2 * t := by omega
  calc #{i ∈ D | t ∣ N - i}
      ≤ #(range ((P - 3) / (2 * t) + 1)) := by
        apply card_le_card_of_injOn (fun i => (i - 3) / (2 * t))
        · intro i hi
          simp only [coe_filter, Set.mem_setOf_eq, mem_coe] at hi
          simp only [coe_range, Set.mem_Iio]
          have := (hD i hi.1).2.2
          have : (i - 3) / (2 * t) ≤ (P - 3) / (2 * t) :=
            Nat.div_le_div_right (by omega)
          omega
        · intro i hi j hj hq
          simp only [coe_filter, Set.mem_setOf_eq] at hi hj
          simp only at hq
          have hi3 := (hD i hi.1).2.1
          have hj3 := (hD j hj.1).2.1
          rcases le_total i j with h | h
          · obtain ⟨c, hc⟩ := same_class hN (hD i hi.1) (hD j hj.1) ht hi.2 hj.2 h
            have he : j - 3 = (i - 3) + 2 * t * c := by omega
            rw [he, Nat.add_mul_div_left _ _ ht0] at hq
            have hc0 : c = 0 := by omega
            subst hc0
            omega
          · obtain ⟨c, hc⟩ := same_class hN (hD j hj.1) (hD i hi.1) ht hj.2 hi.2 h
            have he : i - 3 = (j - 3) + 2 * t * c := by omega
            rw [he, Nat.add_mul_div_left _ _ ht0] at hq
            have hc0 : c = 0 := by omega
            subst hc0
            omega
    _ = (P - 3) / (2 * t) + 1 := card_range _

/-- Per prime power count on deficient lines. -/
theorem deficit_count_le {P N q a : ℕ} (D : Finset ℕ) (hb : BadFamily P N)
    (hD : ∀ i ∈ D, Deficient P N i) (hq : Nat.Prime q) (ha : 0 < a) :
    #{i ∈ D | q ^ a ∣ N - i} ≤
      if 2 * q ^ a ≤ P - 3 then min #D ((P - 3) / (2 * q ^ a) + 1) else 0 := by
  classical
  split_ifs with h
  · by_cases hodd : q ^ a % 2 = 1
    · exact le_min (card_filter_le _ _)
        (class_count D hb.1 (fun i hi => (hD i hi).1) hodd)
    · have : #{i ∈ D | q ^ a ∣ N - i} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi hdiv
        have ho := compl_odd hb (hD i hi).1
        obtain ⟨m, hm⟩ := hdiv
        have : (N - i) % 2 = (q ^ a % 2 * (m % 2)) % 2 := by rw [hm, Nat.mul_mod]
        have hz : q ^ a % 2 = 0 := by omega
        rw [hz, zero_mul, Nat.zero_mod] at this
        omega
      rw [this]; exact Nat.zero_le _
  · have : #{i ∈ D | q ^ a ∣ N - i} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i hi hdiv
      exact h (deficient_prime_power_bound hb (hD i hi) hq ha hdiv)
    rw [this]

/-- **k-line bound.** The product of the complements of any set of deficient
    lines divides `deficitBudget P #D`. -/
theorem deficit_product_dvd_budget {P N : ℕ} (D : Finset ℕ) (hb : BadFamily P N)
    (hD : ∀ i ∈ D, Deficient P N i) :
    (∏ i ∈ D, (N - i)) ∣ deficitBudget P #D := by
  classical
  have hpos : ∀ i ∈ D, N - i ≠ 0 := by
    intro i hi
    have := (hD i hi).1.2.2
    have := hb.1
    omega
  have hprod0 : (∏ i ∈ D, (N - i)) ≠ 0 := prod_ne_zero_iff.mpr hpos
  have hrpos : ∀ r ∈ (range P).filter Nat.Prime, r ^ deficitExponent P #D r ≠ 0 :=
    fun r hr => pow_ne_zero _ (mem_filter.1 hr).2.ne_zero
  have hB0 : deficitBudget P #D ≠ 0 := prod_ne_zero_iff.mpr hrpos
  rw [← Nat.factorization_le_iff_dvd hprod0 hB0, Finsupp.le_def]
  intro q
  rw [Nat.factorization_prod hpos, Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hq : Nat.Prime q
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  by_cases hqP : P ≤ q
  · have : ∀ i ∈ D, (N - i).factorization q = 0 := by
      intro i hi
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      have := (hb.2.2 i (hD i hi).1).2 q hq hd
      omega
    rw [sum_eq_zero this]
    exact Nat.zero_le _
  push Not at hqP
  -- the budget side
  have hRHS : (deficitBudget P #D).factorization q = deficitExponent P #D q := by
    rw [deficitBudget, Nat.factorization_prod hrpos, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finset.sum_eq_single_of_mem q
        (mem_filter.2 ⟨mem_range.2 hqP, hq⟩)]
    · rw [hq.factorization_pow, Finsupp.single_eq_same]
    · intro r hr hne
      rw [(mem_filter.1 hr).2.factorization_pow, Finsupp.single_apply, ite_eq_right_iff.mpr (fun h => absurd h hne)]
  rw [hRHS]
  -- the product side, counted through prime powers
  set B := N + P
  have hcount : ∀ i ∈ D, (N - i).factorization q = #{a ∈ Ico 1 B | q ^ a ∣ N - i} := by
    intro i hi
    apply Nat.factorization_eq_card_pow_dvd_of_lt hq (Nat.pos_of_ne_zero (hpos i hi))
    calc N - i ≤ N := Nat.sub_le _ _
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ q ^ N := Nat.pow_le_pow_left hq.two_le _
      _ ≤ q ^ B := Nat.pow_le_pow_right hq.pos (by omega)
  rw [sum_congr rfl hcount]
  simp only [card_filter]
  rw [sum_comm]
  set g : ℕ → ℕ := fun a =>
    if 2 * q ^ a ≤ P - 3 then min #D ((P - 3) / (2 * q ^ a) + 1) else 0
  have hstep : ∑ a ∈ Ico 1 B, ∑ i ∈ D, (if q ^ a ∣ N - i then 1 else 0)
      ≤ ∑ a ∈ Ico 1 B, g a := by
    apply sum_le_sum
    intro a ha
    have ha0 : 0 < a := by simp at ha; omega
    rw [← card_filter]
    exact deficit_count_le D hb hD hq ha0
  have hsub : ∑ a ∈ Ico 1 P, g a = ∑ a ∈ Ico 1 B, g a := by
    apply sum_subset
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha hna
      simp only [mem_Ico] at ha hna
      have haP : P ≤ a := by omega
      have h1 : a < 2 ^ a := Nat.lt_two_pow_self
      have h2 : 2 ^ a ≤ q ^ a := Nat.pow_le_pow_left hq.two_le _
      simp only [g]
      rw [if_neg (by omega)]
  calc ∑ a ∈ Ico 1 B, ∑ i ∈ D, (if q ^ a ∣ N - i then 1 else 0)
      ≤ ∑ a ∈ Ico 1 B, g a := hstep
    _ = ∑ a ∈ Ico 1 P, g a := hsub.symm
    _ = deficitExponent P #D q := rfl

/-- **Height bound for k deficient lines.** -/
theorem deficit_height_bound {P N : ℕ} (D : Finset ℕ) (hb : BadFamily P N)
    (hD : ∀ i ∈ D, Deficient P N i) :
    (N - P) ^ #D ≤ deficitBudget P #D := by
  classical
  have hB0 : 0 < deficitBudget P #D := by
    apply Nat.pos_of_ne_zero
    exact prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (mem_filter.1 hr).2.ne_zero
  calc (N - P) ^ #D = ∏ _i ∈ D, (N - P) := (prod_const _).symm
    _ ≤ ∏ i ∈ D, (N - i) := by
        apply prod_le_prod'
        intro i hi
        exact Nat.sub_le_sub_left (hD i hi).1.2.2 N
    _ ≤ deficitBudget P #D :=
        Nat.le_of_dvd hB0 (deficit_product_dvd_budget D hb hD)

#print axioms deficit_product_dvd_budget
#print axioms deficit_height_bound

end WilliamsonMurII
