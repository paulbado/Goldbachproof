import Goldbach.WilliamsonMurIIKLines

/-! # Mur II — exact bridge to Goldbach

* `badFamily_iff_not_goldbach`: at the rank `P = ` largest prime `< N`,
  `BadFamily P N` is *exactly* the failure of (odd) Goldbach at `N`.
* `goldbach_of_walls`: Wall I + Wall II above `P₀`, plus the finite range
  `5 ≤ P < P₀`, imply Goldbach for every even `N ≥ 8`.
* `first_failure_rank_chain`: the owner constraint that a first failure
  imposes at *every* smaller rank, not only the previous prime.

Fully proved: only the standard axioms are used. -/

namespace WilliamsonMurII

/-- `N` is a sum of two odd primes. -/
def GoldbachAt (N : ℕ) : Prop :=
  ∃ i q : ℕ, Nat.Prime i ∧ Nat.Prime q ∧ 3 ≤ i ∧ 3 ≤ q ∧ i + q = N

/-- Without the guard `6 ≤ N`, a first failure at rank `≥ 5` is impossible. -/
theorem badFamily_three_four : BadFamily 3 4 := by
  refine ⟨by norm_num, by decide, ?_⟩
  intro i hi
  have : i = 3 := by have := hi.2.1; have := hi.2.2; omega
  subst this
  refine ⟨by norm_num, ?_⟩
  intro r hr hd
  exact absurd (Nat.le_of_dvd (by norm_num) hd) (by have := hr.two_le; omega)

theorem not_firstFailure_unguarded (P : ℕ) (hP : 5 ≤ P) :
    ¬ (Nat.Prime P ∧ (∃ N, BadFamily P N) ∧
      ∀ q : ℕ, Nat.Prime q → 3 ≤ q → q < P → ∀ N, ¬ BadFamily q N) :=
  fun hf => hf.2.2 3 Nat.prime_three le_rfl (by omega) 4 badFamily_three_four

/-- Rank 3 never fails at a height `N ≥ 6`. -/
theorem no_badFamily_three {N : ℕ} (hN : 6 ≤ N) : ¬ BadFamily 3 N := by
  intro hb
  have h3 : Index 3 3 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have ho := compl_odd hb h3
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (n := N - 3) (by omega)
  have hlt := (hb.2.2 3 h3).2 r hr hd
  have : r = 2 := by have := hr.two_le; omega
  subst this
  omega

/-- A Goldbach failure gives a bad family at the largest prime below `N`. -/
theorem badFamily_of_not_goldbach {P N : ℕ} (hN : 6 ≤ N) (hNe : Even N)
    (hP : Nat.Prime P) (hPN : P < N) (hmax : ∀ q, Nat.Prime q → q < N → q ≤ P)
    (hg : ¬ GoldbachAt N) : BadFamily P N := by
  refine ⟨hPN, hNe, fun i hi => ?_⟩
  have hio := idx_odd hi
  obtain ⟨k, hk⟩ := hNe
  have hnp : ¬ Nat.Prime (N - i) := by
    intro hpr
    apply hg
    have := hpr.two_le
    exact ⟨i, N - i, hi.1, hpr, hi.2.1, by omega, by have := hi.2.2; omega⟩
  refine ⟨hnp, fun r hr hd => ?_⟩
  have hpos : 0 < N - i := by have := hi.2.2; omega
  have hrle : r ≤ N - i := Nat.le_of_dvd hpos hd
  have hrP : r ≤ P := hmax r hr (by have := hi.2.1; omega)
  rcases Nat.lt_or_ge r P with h | h
  · exact h
  · exfalso
    have hrP' : r = P := le_antisymm hrP h
    subst hrP'
    obtain ⟨m, hm⟩ := hd
    -- Bertrand: a prime in (N/2, N]
    obtain ⟨s, hs, hs1, hs2⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
    have hsN : s ≠ N := by
      intro he
      subst he
      have := hs.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩
      omega
    have hsP : s ≤ r := hmax s hs (by omega)
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · omega
      · exact hnp (by rw [hm, mul_one]; exact hr)
      · omega
    · have : r * 3 ≤ r * m := Nat.mul_le_mul_left r hm3
      omega

/-- Conversely, a bad family at the largest prime below `N` forbids Goldbach. -/
theorem not_goldbach_of_badFamily {P N : ℕ} (hb : BadFamily P N)
    (hmax : ∀ q, Nat.Prime q → q < N → q ≤ P) : ¬ GoldbachAt N := by
  rintro ⟨i, q, hi, hq, hi3, hq3, hsum⟩
  have hidx : Index P i := ⟨hi, hi3, hmax i hi (by omega)⟩
  have : N - i = q := by omega
  exact (hb.2.2 i hidx).1 (this ▸ hq)

/-- **Exact bridge.** At the rank `P` = largest prime `< N`, a bad family is
    the same thing as a Goldbach failure. -/
theorem badFamily_iff_not_goldbach {P N : ℕ} (hN : 6 ≤ N) (hNe : Even N)
    (hP : Nat.Prime P) (hPN : P < N) (hmax : ∀ q, Nat.Prime q → q < N → q ≤ P) :
    BadFamily P N ↔ ¬ GoldbachAt N :=
  ⟨fun hb => not_goldbach_of_badFamily hb hmax,
   badFamily_of_not_goldbach hN hNe hP hPN hmax⟩

/-- **Rank chain.** A first failure forces, at *every* smaller prime rank `q`,
    an owner: a line `j ≤ q` whose complement has a prime factor in `[q, P)`. -/
theorem first_failure_rank_chain {P N q : ℕ} (hf : FirstFailure P)
    (hb : BadFamily P N) (hq : Nat.Prime q) (hq3 : 3 ≤ q) (hqP : q < P)
    (hN6 : 6 ≤ N) :
    ∃ j r, Index q j ∧ Nat.Prime r ∧ q ≤ r ∧ r < P ∧ r ∣ N - j := by
  classical
  by_contra hn
  apply hf.2.2 q hq hq3 hqP N hN6
  refine ⟨lt_trans hqP hb.1, hb.2.1, fun j hj => ?_⟩
  have hjP : Index P j := ⟨hj.1, hj.2.1, le_trans hj.2.2 (le_of_lt hqP)⟩
  refine ⟨(hb.2.2 j hjP).1, fun r hr hd => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hn ⟨j, r, hj, hr, hlt, (hb.2.2 j hjP).2 r hr hd, hd⟩

/-- **Full reduction.** Wall I and Wall II above `P₀`, together with the finite
    range of ranks `5 ≤ P < P₀`, imply Goldbach for every even `N ≥ 8`. -/
theorem goldbach_of_walls (P₀ : ℕ) (hI : WallIAt P₀) (hII : WallIIAt P₀)
    (hsmall : ∀ P N, Nat.Prime P → 5 ≤ P → P < P₀ → ¬ BadFamily P N) :
    ∀ N, 8 ≤ N → Even N → GoldbachAt N := by
  classical
  intro N hN hNe
  by_contra hg
  -- the largest prime below N
  set P := Nat.findGreatest Nat.Prime (N - 1) with hPdef
  have h7 : 7 ≤ P := Nat.le_findGreatest (by omega) (by norm_num)
  have hPp : Nat.Prime P := Nat.findGreatest_spec (m := 7) (by omega) (by norm_num)
  have hPN : P < N := by have := Nat.findGreatest_le (P := Nat.Prime) (N - 1); omega
  have hmax : ∀ q, Nat.Prime q → q < N → q ≤ P :=
    fun q hq hqN => Nat.le_findGreatest (by omega) hq
  have hbN := badFamily_of_not_goldbach (by omega) hNe hPp hPN hmax hg
  -- the least failing rank ≥ 5
  have hex : ∃ R, Nat.Prime R ∧ 5 ≤ R ∧ ∃ M, BadFamily R M :=
    ⟨P, hPp, by omega, N, hbN⟩
  set R := Nat.find hex
  obtain ⟨hRp, hR5, M, hbM⟩ := Nat.find_spec hex
  have hff : FirstFailure R := by
    refine ⟨hRp, ⟨M, hbM⟩, fun q hq hq3 hqR M' hM' hb' => ?_⟩
    rcases Nat.lt_or_ge q 5 with h | h
    · have : q = 3 ∨ q = 4 := by omega
      rcases this with rfl | rfl
      · exact no_badFamily_three hM' hb'
      · exact absurd hq (by norm_num)
    · exact Nat.find_min hex hqR ⟨hq, h, M', hb'⟩
  -- the previous prime of R
  set p := Nat.findGreatest Nat.Prime (R - 1)
  have hp3 : 3 ≤ p := Nat.le_findGreatest (by omega) Nat.prime_three
  have hpp : Nat.Prime p := Nat.findGreatest_spec (m := 3) (by omega) Nat.prime_three
  have hpR : p < R := by have := Nat.findGreatest_le (P := Nat.Prime) (R - 1); omega
  have hprev : PreviousPrime p R :=
    ⟨⟨hpp, hp3, le_of_lt hpR⟩, hpR, fun q hq hqR => Nat.le_findGreatest (by omega) hq⟩
  rcases Nat.lt_or_ge R P₀ with hlt | hge
  · exact hsmall R M hRp hR5 hlt hbM
  · exact combine_walls P₀ P₀ hI hII R p M (by simpa using hge) hR5 hRp
      (first_failure_previous_conditions hff hprev hbM) hbM

#print axioms badFamily_iff_not_goldbach
#print axioms first_failure_rank_chain
#print axioms goldbach_of_walls

end WilliamsonMurII
