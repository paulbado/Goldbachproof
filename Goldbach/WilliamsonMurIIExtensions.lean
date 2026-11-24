import Goldbach.WilliamsonMurII

/-! Arithmetic extensions for Mur II. Compiles against Mathlib v4.36.0. No new axioms are declared; the closure is not asserted. -/
namespace WilliamsonMurII

/-- A rank fails for some height, and every smaller odd-prime rank succeeds
    at every height `N ≥ 6`. The guard `6 ≤ N` is necessary: `BadFamily 3 4`
    holds trivially (`4 - 3 = 1`), so without it `FirstFailure P` would be
    false for every `P ≥ 5` (see `not_firstFailure_unguarded` in
    `WilliamsonMurIIBridge`). Since `P < N`, the guard is automatic for `P ≥ 5`. -/
def FirstFailure (P : ℕ) : Prop :=
  Nat.Prime P ∧ (∃ N, BadFamily P N) ∧
    ∀ q : ℕ, Nat.Prime q → 3 ≤ q → q < P → ∀ N, 6 ≤ N → ¬ BadFamily q N

private theorem six_le_of_prev {p P N : ℕ} (hp : PreviousPrime p P)
    (hb : BadFamily P N) : 6 ≤ N := by
  have h1 := hp.1.2.1
  have h2 := hp.2.1
  have h3 := hb.1
  obtain ⟨k, hk⟩ := hb.2.1
  omega

private theorem index_mod_two {P i : ℕ} (hi : Index P i) : i % 2 = 1 := by
  rcases hi.1.eq_two_or_odd with h | h
  · have := hi.2.1
    omega
  · exact h

private theorem complement_mod_two {P N i : ℕ}
    (hb : BadFamily P N) (hi : Index P i) : (N - i) % 2 = 1 := by
  have hN := hb.1
  have hiP := hi.2.2
  have ho := index_mod_two hi
  obtain ⟨k, hk⟩ := hb.2.1
  omega

/-- Previous success and a bad family force a factor equal to p. -/
theorem previous_prime_divides {P p N : ℕ}
    (hp : PreviousPrime p P) (hb : BadFamily P N)
    (hs : ¬ BadFamily p N) :
    ∃ j, Index p j ∧ p ∣ N - j := by
  classical
  by_contra hn
  apply hs
  refine ⟨lt_trans hp.2.1 hb.1, hb.2.1, ?_⟩
  intro j hj
  have hjP : Index P j := ⟨hj.1, hj.2.1, le_trans hj.2.2 (le_of_lt hp.2.1)⟩
  refine ⟨(hb.2.2 j hjP).1, ?_⟩
  intro r hr hd
  have hrP := (hb.2.2 j hjP).2 r hr hd
  have hrp := hp.2.2 r hr hrP
  by_contra hlt
  have he : r = p := by omega
  exact hn ⟨j, hj, he ▸ hd⟩

/-- Derive the full previous-rank conditions, given its preceding prime. -/
theorem first_failure_previous_conditions {P p N : ℕ}
    (hf : FirstFailure P) (hp : PreviousPrime p P)
    (hb : BadFamily P N) : PreviousRankConditions p P N := by
  have hs := hf.2.2 p hp.1.1 hp.1.2.1 hp.2.1 N (six_le_of_prev hp hb)
  obtain ⟨j, hj, hd⟩ := previous_prime_divides hp hb hs
  have hjP : Index P j := ⟨hj.1, hj.2.1, le_trans hj.2.2 (le_of_lt hp.2.1)⟩
  have ho := complement_mod_two hb hjP
  have hp3 := hp.1.2.1
  have hj3 := hj.2.1
  have hjN : j < N := lt_of_le_of_lt hjP.2.2 hb.1
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, mul_one] at hk
    exact (hb.2.2 j hjP).1 (hk.symm ▸ hp.1.1)
  have hk2 : k ≠ 2 := by
    intro h
    rw [h, mul_two] at hk
    omega
  have hk3 : 3 ≤ k := by omega
  have hm : p * 3 ≤ p * k := Nat.mul_le_mul_left p hk3
  have he : N = j + p * k := by omega
  refine ⟨hp, ?_, j, hj, ?_⟩
  · rw [mul_comm p 3] at hm
    omega
  · rw [he, Nat.add_mod]
    simp

/-- An odd shared divisor has size at most half the index range. -/
theorem shared_odd_bound {P N i j t : ℕ}
    (hN : P < N) (hi : Index P i) (hj : Index P j) (hne : i ≠ j)
    (ht : t % 2 = 1) (hdi : t ∣ N - i) (hdj : t ∣ N - j) :
    2 * t ≤ P - 3 := by
  have hgap_pos : 0 < max i j - min i j := by omega
  have hgap_le : max i j - min i j ≤ P - 3 := by
    have := hi.2.1; have := hi.2.2
    have := hj.2.1; have := hj.2.2
    omega
  have hoi := index_mod_two hi
  have hoj := index_mod_two hj
  have hgap_even : (max i j - min i j) % 2 = 0 := by omega
  obtain ⟨k, hk⟩ := dvd_difference N i j t
    (le_trans hi.2.2 (le_of_lt hN)) (le_trans hj.2.2 (le_of_lt hN)) hdi hdj
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, mul_one] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  have hm : t * 2 ≤ t * k := Nat.mul_le_mul_left t hk2
  rw [mul_comm t 2] at hm
  omega

/-- Every prime power on a deficient line is at most (P-3)/2. -/
theorem deficient_prime_power_bound {P N i r a : ℕ}
    (hb : BadFamily P N) (hi : Deficient P N i)
    (hr : Nat.Prime r) (ha : 0 < a) (hd : r ^ a ∣ N - i) :
    2 * r ^ a ≤ P - 3 := by
  have ho := complement_mod_two hb hi.1
  have ht : r ^ a % 2 = 1 := by
    obtain ⟨k, hk⟩ := hd
    have hm : (N - i) % 2 = (r ^ a % 2 * (k % 2)) % 2 := by
      rw [hk, Nat.mul_mod]
    by_contra hn
    have hz : r ^ a % 2 = 0 := by omega
    rw [hz, zero_mul, Nat.zero_mod] at hm
    omega
  obtain ⟨j, hj, hji, hdj⟩ := shared_power hi hr ha hd
  exact shared_odd_bound hb.1 hi.1 hj (Ne.symm hji) ht hd hdj

/-- Large odd primes, if present, have exactly one line and a private witness. -/
theorem large_prime_private {P N i r : ℕ}
    (hb : BadFamily P N) (hi : Index P i) (hr : Nat.Prime r)
    (hr3 : 3 ≤ r) (hlarge : P - 3 < 2 * r) (hd : r ∣ N - i) :
    Private P N i := by
  have ht : r % 2 = 1 := by
    rcases hr.eq_two_or_odd with h | h
    · omega
    · exact h
  refine ⟨r, 1, hr, by decide, by simpa using hd, ?_⟩
  intro j hj hji hdj
  have hh : 2 * r ≤ P - 3 := shared_odd_bound hb.1 hi hj (Ne.symm hji) ht hd (by simpa using hdj)
  omega

/-- Bertrand supplies the size condition for the preceding prime. -/
theorem previous_prime_large {p P : ℕ}
    (_hP : Nat.Prime P) (hp : PreviousPrime p P) : P - 3 < 2 * p := by
  have hp3 := hp.1.2.1
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul p (by omega)
  have hPq : P ≤ q := by
    by_contra h
    have hqp := hp.2.2 q hq (by omega)
    omega
  omega

/-- The preceding prime cannot be absent and owns a nondeficient line. -/
theorem previous_prime_has_private_owner {P p N : ℕ}
    (hf : FirstFailure P) (hp : PreviousPrime p P) (hb : BadFamily P N) :
    ∃ j, Index P j ∧ p ∣ N - j ∧ Private P N j := by
  obtain ⟨j, hj, hd⟩ := previous_prime_divides hp hb
    (hf.2.2 p hp.1.1 hp.1.2.1 hp.2.1 N (six_le_of_prev hp hb))
  have hjP : Index P j := ⟨hj.1, hj.2.1, le_trans hj.2.2 (le_of_lt hp.2.1)⟩
  exact ⟨j, hjP, hd, large_prime_private hb hjP hp.1.1 hp.1.2.1
    (previous_prime_large hf.1 hp) hd⟩

/-- Private powers of the same prime cannot belong to distinct lines. -/
theorem private_prime_unique {P N i j r a b : ℕ}
    (hi : Index P i) (hj : Index P j)
    (hdi : r ^ a ∣ N - i) (hdj : r ^ b ∣ N - j)
    (hpi : ∀ k, Index P k → k ≠ i → ¬ r ^ a ∣ N - k)
    (hpj : ∀ k, Index P k → k ≠ j → ¬ r ^ b ∣ N - k) : i = j := by
  by_contra hne
  rcases le_total a b with h | h
  · have hd : r ^ a ∣ r ^ b := by
      refine ⟨r ^ (b - a), ?_⟩
      have he : a + (b - a) = b := by omega
      rw [← pow_add, he]
    exact hpi j hj (Ne.symm hne) (dvd_trans hd hdj)
  · have hd : r ^ b ∣ r ^ a := by
      refine ⟨r ^ (a - b), ?_⟩
      have he : b + (a - b) = a := by omega
      rw [← pow_add, he]
    exact hpj i hi hne (dvd_trans hd hdi)

/-- Abstract budget: a chosen private prime per nondeficient line is injective.
    I and R are finite sets of indices and allowed primes, represented as types. -/
theorem private_owner_budget {I R : Type*} [Fintype I] [Fintype R]
    (index : I → ℕ) (prime : R → ℕ) (hindex : Function.Injective index)
    (P N : ℕ) (hI : ∀ i, Index P (index i))
    (owner : I → R) (power : I → ℕ)
    (hd : ∀ i, prime (owner i) ^ power i ∣ N - index i)
    (hpriv : ∀ i j, Index P j → j ≠ index i →
      ¬ prime (owner i) ^ power i ∣ N - j) :
    Fintype.card I ≤ Fintype.card R := by
  apply Fintype.card_le_of_injective owner
  intro i j h
  apply hindex
  have he : prime (owner i) = prime (owner j) := congrArg prime h
  have hdj : prime (owner i) ^ power j ∣ N - index j := by
    rw [he]; exact hd j
  have hpj : ∀ k, Index P k → k ≠ index j →
      ¬ prime (owner i) ^ power j ∣ N - k := by
    rw [he]; exact hpriv j
  exact private_prime_unique (hI i) (hI j) (hd i) hdj (hpriv i) hpj

/-- A pair of deficient complements cannot have a product exceeding L times
    the gap when L is a positive common multiple of their certificates. -/
theorem pair_height_bound {P N i j L : ℕ}
    (hN : P < N) (hi : Index P i) (hj : Index P j) (hne : i ≠ j)
    (hL : 0 < L) (hdi : N - i ∣ L) (hdj : N - j ∣ L) :
    (N - P)^2 ≤ L * (max i j - min i j) := by
  have hgap : 0 < max i j - min i j := by omega
  have hg := Nat.le_of_dvd hgap (dvd_difference N i j _
    (le_trans hi.2.2 (le_of_lt hN)) (le_trans hj.2.2 (le_of_lt hN))
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  have hl := Nat.le_of_dvd hL (Nat.lcm_dvd hdi hdj)
  have hprod := Nat.mul_le_mul hg hl
  have hbase₁ : N - P ≤ N - i := Nat.sub_le_sub_left hi.2.2 N
  have hbase₂ : N - P ≤ N - j := Nat.sub_le_sub_left hj.2.2 N
  calc
    (N - P)^2 = (N - P) * (N - P) := by rw [pow_two]
    _ ≤ (N - i) * (N - j) := Nat.mul_le_mul hbase₁ hbase₂
    _ = Nat.gcd (N - i) (N - j) * Nat.lcm (N - i) (N - j) :=
      (Nat.gcd_mul_lcm _ _).symm
    _ ≤ (max i j - min i j) * L := hprod
    _ = L * (max i j - min i j) := Nat.mul_comm _ _

/-- Sharper pair bound in a bad family: the gcd is odd. -/
theorem pair_height_bound_odd {P N i j L : ℕ}
    (hb : BadFamily P N) (hi : Index P i) (hj : Index P j) (hne : i ≠ j)
    (hL : 0 < L) (hdi : N - i ∣ L) (hdj : N - j ∣ L) :
    2 * (N - P)^2 ≤ L * (P - 3) := by
  let g := Nat.gcd (N - i) (N - j)
  have hgi : g ∣ N - i := Nat.gcd_dvd_left _ _
  have hgj : g ∣ N - j := Nat.gcd_dvd_right _ _
  have ho := complement_mod_two hb hi
  have hgodd : g % 2 = 1 := by
    obtain ⟨k, hk⟩ := hgi
    have hm : (N - i) % 2 = (g % 2 * (k % 2)) % 2 := by
      rw [hk, Nat.mul_mod]
    by_contra hn
    have hz : g % 2 = 0 := by omega
    rw [hz, zero_mul, Nat.zero_mod] at hm
    omega
  have hg := shared_odd_bound hb.1 hi hj hne hgodd hgi hgj
  have hl := Nat.le_of_dvd hL (Nat.lcm_dvd hdi hdj)
  have hbase₁ : N - P ≤ N - i := Nat.sub_le_sub_left hi.2.2 N
  have hbase₂ : N - P ≤ N - j := Nat.sub_le_sub_left hj.2.2 N
  have hprod : (N - P)^2 ≤ (N - i) * (N - j) := by
    rw [pow_two]
    exact Nat.mul_le_mul hbase₁ hbase₂
  calc
    2 * (N - P)^2 ≤ 2 * ((N - i) * (N - j)) := Nat.mul_le_mul_left 2 hprod
    _ = 2 * (g * Nat.lcm (N - i) (N - j)) := by
      change 2 * ((N - i) * (N - j)) =
        2 * (Nat.gcd (N - i) (N - j) * Nat.lcm (N - i) (N - j))
      rw [Nat.gcd_mul_lcm]
    _ = (2 * g) * Nat.lcm (N - i) (N - j) := by ring
    _ ≤ (P - 3) * L := Nat.mul_le_mul hg hl
    _ = L * (P - 3) := Nat.mul_comm _ _

#print axioms pair_height_bound_odd
#print axioms first_failure_previous_conditions
#print axioms deficient_prime_power_bound
#print axioms previous_prime_has_private_owner
#print axioms private_owner_budget
#print axioms pair_height_bound
end WilliamsonMurII
