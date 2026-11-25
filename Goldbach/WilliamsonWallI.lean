import Goldbach.WilliamsonSmallRanks

/-! # Wall I: forced structure of a family with a single deficient row

`WallIAt` is **not** proved here. These are the unconditional consequences of the
Wall I branch (`¬ MultipleDeficits`) that follow from the counting identity `z ≥ 1 + a`:
no absent prime, a unique deficient row, every other row privately owned, and an odd
multiple of every odd prime `q < P` in `[N - P, N]`.

Also: the passage from `GoldbachAt` (two odd primes, `N ≥ 8`) to the usual statement
(`N ≥ 4`), which is unconditional as an implication. -/

namespace WilliamsonMurII
open Finset

theorem card_defSet_le_one {P N : ℕ} (h : ¬ MultipleDeficits P N) : #(defSet P N) ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hne
  unfold defSet at hi hj
  exact h ⟨i, j, hne, (mem_filter.1 hi).2, (mem_filter.1 hj).2⟩

/-- Wall I branch: no prime of `[3, P)` is absent. -/
theorem wallI_absent_empty {P N : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P) (hb : BadFamily P N)
    (h : ¬ MultipleDeficits P N) : absentSet P N = ∅ := by
  have h1 := one_add_absent_le_deficient hP h3 hb
  have h2 := card_defSet_le_one h
  exact Finset.card_eq_zero.1 (by omega)

/-- Wall I branch: every odd prime `q < P` divides some complement. -/
theorem wallI_every_prime_divides {P N q : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) (h : ¬ MultipleDeficits P N)
    (hq : Nat.Prime q) (hq3 : 3 ≤ q) (hqP : q < P) :
    ∃ ℓ, Index P ℓ ∧ q ∣ N - ℓ := by
  by_contra hn
  have hmem : q ∈ absentSet P N := by
    simp only [absentSet, supSet, mem_filter, mem_range]
    exact ⟨⟨hqP, hq, hq3⟩, fun ℓ hℓ hd => hn ⟨ℓ, mem_idxSet.1 hℓ, hd⟩⟩
  rw [wallI_absent_empty hP h3 hb h] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- Wall I branch: `[N - P, N]` contains an odd multiple of every odd prime `q < P`
    (in particular there is no geometric absence). -/
theorem wallI_odd_multiple {P N q : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) (h : ¬ MultipleDeficits P N)
    (hq : Nat.Prime q) (hq3 : 3 ≤ q) (hqP : q < P) :
    ∃ m, N - P ≤ q * (2 * m + 1) ∧ q * (2 * m + 1) ≤ N := by
  obtain ⟨ℓ, hℓ, k, hk⟩ := wallI_every_prime_divides hP h3 hb h hq hq3 hqP
  have ho : Odd (N - ℓ) := Nat.odd_iff.2 (compl_odd hb hℓ)
  rw [hk, Nat.odd_mul] at ho
  obtain ⟨m, hm⟩ := ho.2
  refine ⟨m, ?_, ?_⟩
  · rw [← hm, ← hk]; exact Nat.sub_le_sub_left hℓ.2.2 N
  · rw [← hm, ← hk]; exact Nat.sub_le N ℓ

/-- Wall I branch: there is a deficient row `ℓ₀` whose complement divides
    `deficitBudget P 1`, and every other row has a private prime power. -/
theorem wallI_unique_deficient {P N : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) (h : ¬ MultipleDeficits P N) :
    ∃ ℓ₀, Deficient P N ℓ₀ ∧ N - ℓ₀ ∣ deficitBudget P 1 ∧
      ∀ j, Index P j → j ≠ ℓ₀ → Private P N j := by
  obtain ⟨ℓ₀, hdef, hdvd⟩ := exists_deficient_dvd_budget hP h3 hb
  refine ⟨ℓ₀, hdef, hdvd, fun j hj hne => ?_⟩
  by_contra hnp
  exact h ⟨j, ℓ₀, hne, ⟨hj, hnp⟩, hdef⟩

/-- **Exact reduction of Wall I.** `WallIAt P₀` follows from prime absence: if every
    first-failure bad family of rank `P ≥ P₀` misses some prime of `[3, P)`, then Wall I
    holds at `P₀`. The hypothesis is the statement of [CC] Prop. "An absent prime under a
    uniform height bound" + height bounds, known there only for `P ≥ P_I` (effective,
    not computed). It is a hypothesis here, not a theorem. -/
theorem wallIAt_of_absent (P₀ : ℕ)
    (h : ∀ P p N, P₀ ≤ P → 5 ≤ P → Nat.Prime P → PreviousRankConditions p P N →
      BadFamily P N → (absentSet P N).Nonempty) : WallIAt P₀ := by
  intro P p N hP h5 hp hprev hb hnm
  have hne := h P p N hP h5 hp hprev hb
  rw [wallI_absent_empty hp (by omega) hb hnm] at hne
  exact Finset.not_nonempty_empty hne

/-- From `GoldbachAt` for even `N ≥ 8` to the usual statement for even `N ≥ 4`. -/
theorem goldbach_usual_of_goldbachAt (h : ∀ N, 8 ≤ N → Even N → GoldbachAt N) :
    ∀ N, 4 ≤ N → Even N → ∃ a b, Nat.Prime a ∧ Nat.Prime b ∧ a + b = N := by
  intro N hN hNe
  rcases Nat.lt_or_ge N 8 with hlt | hge
  · obtain ⟨k, hk⟩ := hNe
    have : N = 4 ∨ N = 6 := by omega
    rcases this with rfl | rfl
    · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
    · exact ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  · obtain ⟨i, q, hi, hq, -, -, hs⟩ := h N hge hNe
    exact ⟨i, q, hi, hq, hs⟩

#print axioms wallI_absent_empty
#print axioms wallI_odd_multiple
#print axioms wallI_unique_deficient
#print axioms wallIAt_of_absent
#print axioms goldbach_usual_of_goldbachAt

end WilliamsonMurII
