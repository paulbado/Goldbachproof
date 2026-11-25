import Goldbach.WilliamsonMurIIClosure

/-! # Wall II: joint (pairwise-gcd) height bound for deficient rows

`WallIIAt` is **not** proved here. New unconditional result: the complements of the
deficient rows all divide `deficitBudget P 1`, and two of them share at most an odd divisor
of their index gap, hence a gcd `≤ (P - 3) / 2`. Therefore, for every set `D` of `k`
deficient rows,

  `(N - P)^k ≤ deficitBudget P 1 * ((P - 3) / 2)^(k (k - 1) / 2)`.

For `k = 2` this replaces `(N - P)^2 ≤ deficitBudget P 2 = (deficitBudget P 1)^2`
(`wallII_height_ceiling`) by `(N - P)^2 ≤ deficitBudget P 1 * ((P - 3) / 2)`. -/

namespace WilliamsonMurII
open Finset

/-- `gcd x (lcm of f over S)` divides the product of the `gcd x (f s)`. -/
theorem gcd_finset_lcm_dvd (x : ℕ) (S : Finset ℕ) (f : ℕ → ℕ) :
    Nat.gcd x (S.lcm f) ∣ ∏ s ∈ S, Nat.gcd x (f s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert b S hb ih =>
    rw [Finset.lcm_insert, Finset.prod_insert hb]
    have h1 : Nat.gcd x (Nat.lcm (f b) (S.lcm f)) ∣ Nat.gcd x (f b * S.lcm f) :=
      Nat.gcd_dvd_gcd_of_dvd_right x (Nat.lcm_dvd_mul _ _)
    exact dvd_trans h1 (dvd_trans (Nat.gcd_mul_right_dvd_mul_gcd x _ _) (mul_dvd_mul_left _ ih))

/-- If the values `f s` are nonzero with pairwise gcd `≤ W`, their product divides
    `lcm * T` with `T ≤ W^(0 + 1 + ⋯ + (#S - 1))`. -/
theorem prod_dvd_lcm_mul (S : Finset ℕ) (f : ℕ → ℕ) (W : ℕ)
    (hpos : ∀ a ∈ S, f a ≠ 0)
    (hW : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd (f a) (f b) ≤ W) :
    ∃ T, 0 < T ∧ (∏ s ∈ S, f s) ∣ S.lcm f * T ∧ T ≤ W ^ (∑ m ∈ range #S, m) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨T, hT0, hTd, hTle⟩ := ih (fun x hx => hpos x (mem_insert_of_mem hx))
      (fun x hx y hy hne => hW x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hne)
    have hfa : f a ≠ 0 := hpos a (mem_insert_self a S)
    set g := Nat.gcd (f a) (S.lcm f) with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hfa)
    have hprod0 : 0 < ∏ s ∈ S, Nat.gcd (f a) (f s) :=
      Finset.prod_pos fun s _ => Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hfa)
    have hgle : g ≤ W ^ #S := by
      calc g ≤ ∏ s ∈ S, Nat.gcd (f a) (f s) :=
            Nat.le_of_dvd hprod0 (gcd_finset_lcm_dvd (f a) S f)
        _ ≤ ∏ _s ∈ S, W := by
            apply Finset.prod_le_prod'
            intro s hs
            exact hW a (mem_insert_self a S) s (mem_insert_of_mem hs)
              (fun h => ha (h ▸ hs))
        _ = W ^ #S := Finset.prod_const _
    refine ⟨g * T, Nat.mul_pos hg0 hT0, ?_, ?_⟩
    · rw [Finset.prod_insert ha, Finset.lcm_insert]
      have h2 : f a * S.lcm f = Nat.lcm (f a) (S.lcm f) * g := by
        rw [hg, mul_comm (Nat.lcm _ _)]; exact (Nat.gcd_mul_lcm _ _).symm
      calc f a * ∏ s ∈ S, f s ∣ f a * (S.lcm f * T) := mul_dvd_mul_left _ hTd
        _ = Nat.lcm (f a) (S.lcm f) * (g * T) := by rw [← mul_assoc, h2, mul_assoc]
    · rw [card_insert_of_notMem ha, Finset.sum_range_succ, pow_add, mul_comm]
      exact Nat.mul_le_mul hTle hgle

/-- The complement of a deficient row divides `deficitBudget P 1`. -/
theorem deficient_dvd_budget {P N i : ℕ} (hb : BadFamily P N) (hi : Deficient P N i) :
    N - i ∣ deficitBudget P 1 := by
  have h := deficit_product_dvd_budget {i} hb (by
    intro x hx; rw [mem_singleton] at hx; subst hx; exact hi)
  rwa [prod_singleton, card_singleton] at h

/-- Two deficient (indeed any two) rows of a bad family have complements with
    gcd at most `(P - 3) / 2`. -/
theorem compl_gcd_le {P N i j : ℕ} (hb : BadFamily P N) (hi : Index P i) (hj : Index P j)
    (hne : i ≠ j) : Nat.gcd (N - i) (N - j) ≤ (P - 3) / 2 := by
  have ho : Odd (N - i) := Nat.odd_iff.2 (compl_odd hb hi)
  have ht : Nat.gcd (N - i) (N - j) % 2 = 1 :=
    Nat.odd_iff.1 (Odd.of_dvd_nat ho (Nat.gcd_dvd_left _ _))
  have := shared_odd_bound hb.1 hi hj hne ht (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  omega

/-- **Joint height bound.** For every set `D` of deficient rows,
    `(N - P)^#D ≤ deficitBudget P 1 * ((P - 3) / 2)^(0 + 1 + ⋯ + (#D - 1))`. -/
theorem deficit_pairwise_height_bound {P N : ℕ} (D : Finset ℕ) (hb : BadFamily P N)
    (hD : ∀ i ∈ D, Deficient P N i) :
    (N - P) ^ #D ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (∑ m ∈ range #D, m) := by
  classical
  have hB0 : 0 < deficitBudget P 1 := by
    apply Nat.pos_of_ne_zero
    exact prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (mem_filter.1 hr).2.ne_zero
  obtain ⟨T, hT0, hTd, hTle⟩ := prod_dvd_lcm_mul D (fun i => N - i) ((P - 3) / 2)
    (fun a ha => by have := (hD a ha).1.2.2; have := hb.1; omega)
    (fun a ha b hb' hne => compl_gcd_le hb (hD a ha).1 (hD b hb').1 hne)
  have hlcm : D.lcm (fun i => N - i) ∣ deficitBudget P 1 :=
    Finset.lcm_dvd fun i hi => deficient_dvd_budget hb (hD i hi)
  have hM0 : 0 < D.lcm (fun i => N - i) :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_dvd_iff] at hlcm; omega
  calc (N - P) ^ #D = ∏ _i ∈ D, (N - P) := (prod_const _).symm
    _ ≤ ∏ i ∈ D, (N - i) := by
        apply Finset.prod_le_prod'
        intro i hi
        exact Nat.sub_le_sub_left (hD i hi).1.2.2 N
    _ ≤ D.lcm (fun i => N - i) * T := Nat.le_of_dvd (Nat.mul_pos hM0 hT0) hTd
    _ ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (∑ m ∈ range #D, m) :=
        Nat.mul_le_mul (Nat.le_of_dvd hB0 hlcm) hTle

/-- Same bound with the exponent written `k (k - 1) / 2`. -/
theorem deficit_pairwise_height_bound' {P N : ℕ} (D : Finset ℕ) (hb : BadFamily P N)
    (hD : ∀ i ∈ D, Deficient P N i) :
    (N - P) ^ #D ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (#D * (#D - 1) / 2) := by
  have h := deficit_pairwise_height_bound D hb hD
  rwa [Finset.sum_range_id] at h

/-- **Sharper Wall II ceiling.** With two deficient rows,
    `(N - P)^2 ≤ deficitBudget P 1 * ((P - 3) / 2)`. -/
theorem wallII_height_ceiling_sharp {P N : ℕ} (hb : BadFamily P N)
    (hII : MultipleDeficits P N) : (N - P) ^ 2 ≤ deficitBudget P 1 * ((P - 3) / 2) := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := hII
  have hD : ∀ x ∈ ({i, j} : Finset ℕ), Deficient P N x := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj
  have h := deficit_pairwise_height_bound {i, j} hb hD
  rw [card_pair hij] at h
  simpa [Finset.sum_range_succ] using h

/-- For every `k` not exceeding the number of deficient rows. -/
theorem height_of_deficient_count {P N k : ℕ} (hb : BadFamily P N)
    (hk : k ≤ #(defSet P N)) :
    (N - P) ^ k ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (k * (k - 1) / 2) := by
  classical
  obtain ⟨D, hDs, hDc⟩ := Finset.exists_subset_card_eq hk
  have hD : ∀ i ∈ D, Deficient P N i := by
    intro i hi
    have := hDs hi
    unfold defSet at this
    exact (mem_filter.1 this).2
  have h := deficit_pairwise_height_bound' D hb hD
  rwa [hDc] at h

/-- With `a` absent primes there are at least `1 + a` deficient rows (17.1), hence the
    joint bound for every `k ≤ 1 + a`. -/
theorem height_of_absent_count {P N k : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) (hk : k ≤ 1 + #(absentSet P N)) :
    (N - P) ^ k ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (k * (k - 1) / 2) :=
  height_of_deficient_count hb (le_trans hk (one_add_absent_le_deficient hP h3 hb))

/-- **Excluded region of Wall II.** No first-failure family with two deficient rows has
    `(N - P)^2 > deficitBudget P 1 * ((P - 3) / 2)`. -/
theorem wallII_excluded_region {P p N : ℕ} (_hprev : PreviousRankConditions p P N)
    (hb : BadFamily P N) (hII : MultipleDeficits P N)
    (hN : deficitBudget P 1 * ((P - 3) / 2) < (N - P) ^ 2) : False :=
  absurd (wallII_height_ceiling_sharp hb hII) (not_le.2 hN)

#print axioms deficit_pairwise_height_bound
#print axioms wallII_height_ceiling_sharp
#print axioms height_of_absent_count
#print axioms wallII_excluded_region

end WilliamsonMurII
