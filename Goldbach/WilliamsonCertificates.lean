import Goldbach.WilliamsonMurIIClosure

/-! # Compulsory private certificates

* An odd prime `p < P` dividing `N` is a private certificate of the row `p`.
* Under `PreviousRankConditions`, the preceding prime `p` is a private certificate of some row.
* Such rows are not deficient; a prime dividing `N` is never absent.

These are exact restrictions. `docs/tex/localized-buchstab-wall-ii.tex` §9 discusses what they
add to Wall II (nothing beyond what the difference certificates already imply). -/

namespace WilliamsonMurII
open Finset

/-- If an odd prime `p ≤ P` divides `N` (`P < N`), then `p` is a private certificate of row `p`:
    `p ∣ N - p`, and `p` divides no other complement. -/
theorem private_of_dvd_N {P N p : ℕ} (hPN : P < N) (hp : Index P p) (hpN : p ∣ N) :
    Private P N p := by
  refine ⟨p, 1, hp.1, one_pos, by rw [pow_one]; exact Nat.dvd_sub hpN dvd_rfl, ?_⟩
  intro j hj hne hd
  rw [pow_one] at hd
  have hjN : j ≤ N := by have := hj.2.2; omega
  have hpj : p ∣ j := by
    have h := Nat.dvd_sub hpN hd
    rwa [Nat.sub_sub_self hjN] at h
  rcases (Nat.dvd_prime hj.1).1 hpj with h | h
  · exact absurd h hp.1.one_lt.ne'
  · exact hne h.symm

/-- Hence a row `p ∣ N` is not deficient. -/
theorem not_deficient_of_dvd_N {P N p : ℕ} (hPN : P < N) (hp : Index P p) (hpN : p ∣ N) :
    ¬ Deficient P N p := fun h => h.2 (private_of_dvd_N hPN hp hpN)

/-- No deficient row `i` has a complement sharing a prime factor `q ≤ P`, `q ≥ 3`, with `N`,
    except through `i = q`, which is excluded. -/
theorem deficient_coprime_odd_divisors {P N i q : ℕ} (hPN : P < N) (hi : Deficient P N i)
    (hq : Index P q) (hqN : q ∣ N) : ¬ q ∣ N - i := by
  intro hd
  have hiN : i ≤ N := by have := hi.1.2.2; omega
  have hqi : q ∣ i := by
    have h := Nat.dvd_sub hqN hd
    rwa [Nat.sub_sub_self hiN] at h
  rcases (Nat.dvd_prime hi.1.1).1 hqi with h | h
  · exact hq.1.one_lt.ne' h
  · subst h; exact not_deficient_of_dvd_N hPN hq hqN hi

/-- Under `PreviousRankConditions`, the preceding prime `p` divides some complement and is a
    private certificate of that row (no first-failure hypothesis needed). -/
theorem previous_prime_private_of_prc {P p N : ℕ} (hP : Nat.Prime P)
    (hprc : PreviousRankConditions p P N) (hb : BadFamily P N) :
    ∃ j, Index P j ∧ p ∣ N - j ∧ Private P N j := by
  obtain ⟨hp, -, j, hj, hmod⟩ := hprc
  have hjP : Index P j := ⟨hj.1, hj.2.1, le_trans hj.2.2 (le_of_lt hp.2.1)⟩
  have hjN : j ≤ N := by have := hjP.2.2; have := hb.1; omega
  have hd : p ∣ N - j := (Nat.modEq_iff_dvd' hjN).1 hmod.symm
  exact ⟨j, hjP, hd, large_prime_private hb hjP hp.1.1 hp.1.2.1
    (previous_prime_large hP hp) hd⟩

/-- That row is not deficient. -/
theorem previous_prime_row_not_deficient {P p N : ℕ} (hP : Nat.Prime P)
    (hprc : PreviousRankConditions p P N) (hb : BadFamily P N) :
    ∃ j, Index P j ∧ p ∣ N - j ∧ ¬ Deficient P N j := by
  obtain ⟨j, hj, hd, hpriv⟩ := previous_prime_private_of_prc hP hprc hb
  exact ⟨j, hj, hd, fun h => h.2 hpriv⟩

/-- A prime `3 ≤ q < P` dividing `N` is never absent (it divides the row `q`). -/
theorem not_absent_of_dvd_N {P N q : ℕ} (_hPN : P < N) (hq : Nat.Prime q) (hq3 : 3 ≤ q)
    (hqP : q < P) (hqN : q ∣ N) : q ∉ absentSet P N := by
  intro h
  simp only [absentSet, mem_filter] at h
  exact h.2 q (mem_idxSet.2 ⟨hq, hq3, le_of_lt hqP⟩) (Nat.dvd_sub hqN dvd_rfl)

#print axioms private_of_dvd_N
#print axioms deficient_coprime_odd_divisors
#print axioms previous_prime_private_of_prc
#print axioms not_absent_of_dvd_N

end WilliamsonMurII
