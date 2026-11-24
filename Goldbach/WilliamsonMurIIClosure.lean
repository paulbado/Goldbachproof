import Goldbach.WilliamsonMurIIKLines

/-! # Mur II — link with *A Closure Chain Toward Williamson's Conjecture*, §17

Notation of §17.1 (I. O. Bado, 2026, DOI 10.13140/RG.2.2.34840.97281):
`I = P ∩ [3, P]` (`idxSet`), `S = P ∩ [3, P)` (`supSet`), `D` the deficient rows
(`defSet`, `z = #D`), `a` the primes of `S` absent from every complement
(`absentSet`), `G(N,P)` the geometric absences of (17.31) (`geomAbsSet`).

Formalized here, elementarily:
* `card_idxSet`              : `|I| = |S| + 1`;
* `one_add_absent_le_deficient` : `z ≥ 1 + a`, the half of identity (17.1)
  `z = 1 + a + t + e` that is used (the terms `t, e` are nonnegative);
* `geomAbs_subset_absent`    : (17.32), `a ≥ G(N,P)`;
* `height_of_geomAbs`        : for every `k ≤ 1 + G(N,P)`,
  `(N - P)^k ≤ deficitBudget P k`.

Not formalized (analytic, outside Mathlib today): the lower bound
`G(N,P) ≥ 3P/(20 log P)` for `N > P^{3/2}` (Prop. 17.13 and (17.47)), which
uses an effective prime number theorem and exponential sums over primes.
It enters `height_of_geomAbs` only through the explicit hypothesis on `k`.

Fully proved: only the standard axioms are used. -/

namespace WilliamsonMurII
open Finset

/-- `I = P ∩ [3, P]`. -/
def idxSet (P : ℕ) : Finset ℕ := (range (P + 1)).filter (fun i => Nat.Prime i ∧ 3 ≤ i)
/-- `S = P ∩ [3, P)`. -/
def supSet (P : ℕ) : Finset ℕ := (range P).filter (fun q => Nat.Prime q ∧ 3 ≤ q)
/-- Primes of `S` dividing no complement. -/
def absentSet (P N : ℕ) : Finset ℕ :=
  (supSet P).filter (fun q => ∀ ℓ ∈ idxSet P, ¬ q ∣ N - ℓ)
open Classical in
/-- Deficient rows. -/
noncomputable def defSet (P N : ℕ) : Finset ℕ := (idxSet P).filter (fun ℓ => Deficient P N ℓ)
open Classical in
/-- Geometric absences (17.31): primes `q ∈ (P/2, P)` such that `[N - P, N]`
    contains no odd multiple of `q`. -/
noncomputable def geomAbsSet (P N : ℕ) : Finset ℕ :=
  (range P).filter (fun q => Nat.Prime q ∧ P < 2 * q ∧
    ∀ m, N - P ≤ q * (2 * m + 1) → ¬ q * (2 * m + 1) ≤ N)

theorem mem_idxSet {P i : ℕ} : i ∈ idxSet P ↔ Index P i := by
  simp only [idxSet, mem_filter, mem_range, Index]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h2⟩

theorem card_idxSet {P : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P) :
    #(idxSet P) = #(supSet P) + 1 := by
  have he : idxSet P = insert P (supSet P) := by
    ext i
    simp only [idxSet, supSet, mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨h1, h2, h3'⟩
      rcases Nat.lt_or_ge i P with h | h
      · exact Or.inr ⟨h, h2, h3'⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨h1, h2, h3'⟩)
      · exact ⟨by omega, hP, h3⟩
      · exact ⟨by omega, h2, h3'⟩
  rw [he, card_insert_of_notMem]
  simp [supSet]

/-- **(17.1), used half.** `z ≥ 1 + a`: every nondeficient row owns a private
    prime, distinct rows own distinct primes, and no absent prime is owned. -/
theorem one_add_absent_le_deficient {P N : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) : 1 + #(absentSet P N) ≤ #(defSet P N) := by
  classical
  set O := (idxSet P).filter (fun ℓ => ¬ Deficient P N ℓ)
  have hsplit : #(defSet P N) + #O = #(idxSet P) := by
    unfold defSet
    convert card_filter_add_card_filter_not (s := idxSet P) (fun ℓ => Deficient P N ℓ)
  have hcard := card_idxSet hP h3
  -- choose a private prime for each nondeficient row
  let f : ℕ → ℕ := fun ℓ => if h : Private P N ℓ then Classical.choose h else 0
  have hpriv : ∀ ℓ ∈ O, Private P N ℓ := by
    intro ℓ hℓ
    simp only [O, mem_filter] at hℓ
    by_contra hn
    exact hℓ.2 ⟨mem_idxSet.1 hℓ.1, hn⟩
  have hspec : ∀ ℓ ∈ O, ∃ a, Nat.Prime (f ℓ) ∧ 0 < a ∧ f ℓ ^ a ∣ N - ℓ ∧
      ∀ j, Index P j → j ≠ ℓ → ¬ f ℓ ^ a ∣ N - j := by
    intro ℓ hℓ
    have h := hpriv ℓ hℓ
    have hf : f ℓ = Classical.choose h := dif_pos h
    rw [hf]
    exact Classical.choose_spec h
  have hmaps : Set.MapsTo f O ((supSet P \ absentSet P N : Finset ℕ) : Set ℕ) := by
    intro ℓ hℓ
    have hℓI : Index P ℓ := mem_idxSet.1 (mem_filter.1 hℓ).1
    obtain ⟨a, hr, ha, hd, -⟩ := hspec ℓ hℓ
    have hdvd : f ℓ ∣ N - ℓ := dvd_trans (dvd_pow_self _ ha.ne') hd
    have hlt := (hb.2.2 ℓ hℓI).2 _ hr hdvd
    have ho := compl_odd hb hℓI
    have h3r : 3 ≤ f ℓ := by
      rcases hr.eq_two_or_odd with h2 | h2
      · exfalso
        rw [h2] at hdvd
        omega
      · have := hr.two_le; omega
    rw [mem_coe, mem_sdiff]
    refine ⟨mem_filter.2 ⟨mem_range.2 hlt, hr, h3r⟩, fun habs => ?_⟩
    exact (mem_filter.1 habs).2 ℓ (mem_idxSet.2 hℓI) hdvd
  have hinj : Set.InjOn f O := by
    intro ℓ hℓ ℓ' hℓ' he
    obtain ⟨a, -, -, hd, hp⟩ := hspec ℓ hℓ
    obtain ⟨b, -, -, hd', hp'⟩ := hspec ℓ' hℓ'
    rw [he] at hd hp
    exact private_prime_unique (mem_idxSet.1 (mem_filter.1 hℓ).1)
      (mem_idxSet.1 (mem_filter.1 hℓ').1) hd hd' hp hp'
  have hO := card_le_card_of_injOn f hmaps hinj
  have hsub : absentSet P N ⊆ supSet P := filter_subset _ _
  rw [card_sdiff_of_subset hsub] at hO
  have := card_le_card hsub
  omega

/-- **(17.32).** A geometric absence is an absent prime: `G(N,P) ≤ a`. -/
theorem geomAbs_subset_absent {P N : ℕ} (h5 : 5 ≤ P) (hb : BadFamily P N) :
    geomAbsSet P N ⊆ absentSet P N := by
  intro q hq
  simp only [geomAbsSet, mem_filter, mem_range] at hq
  obtain ⟨hqP, hqp, h2q, hno⟩ := hq
  have hq3 : 3 ≤ q := by omega
  refine mem_filter.2 ⟨mem_filter.2 ⟨mem_range.2 hqP, hqp, hq3⟩, ?_⟩
  intro ℓ hℓ hd
  have hℓI := mem_idxSet.1 hℓ
  have ho := compl_odd hb hℓI
  obtain ⟨k, hk⟩ := hd
  have hkodd : k % 2 = 1 := by
    have hm : (N - ℓ) % 2 = (q % 2 * (k % 2)) % 2 := by rw [hk, Nat.mul_mod]
    by_contra hn
    have hz : k % 2 = 0 := by omega
    rw [hz, mul_zero, Nat.zero_mod] at hm
    omega
  have hkm : k = 2 * (k / 2) + 1 := by omega
  have hlo : N - P ≤ q * (2 * (k / 2) + 1) := by
    rw [← hkm, ← hk]
    exact Nat.sub_le_sub_left hℓI.2.2 N
  exact hno (k / 2) hlo (by rw [← hkm, ← hk]; exact Nat.sub_le _ _)

/-- **Link with `WilliamsonMurIIKLines`.** Any `k ≤ 1 + G(N,P)` deficient rows
    are available, hence `(N - P)^k ≤ deficitBudget P k`. -/
theorem height_of_geomAbs {P N k : ℕ} (hP : Nat.Prime P) (h5 : 5 ≤ P)
    (hb : BadFamily P N) (hk : k ≤ 1 + #(geomAbsSet P N)) :
    (N - P) ^ k ≤ deficitBudget P k := by
  classical
  have hG := card_le_card (geomAbs_subset_absent h5 hb)
  have hz := one_add_absent_le_deficient hP (by omega) hb
  obtain ⟨D, hDsub, hDcard⟩ := exists_subset_card_eq (s := defSet P N) (n := k) (by omega)
  have hD : ∀ i ∈ D, Deficient P N i := by
    intro i hi
    have h := hDsub hi
    unfold defSet at h
    exact (mem_filter.1 h).2
  have := deficit_height_bound D hb hD
  rwa [hDcard] at this

#print axioms one_add_absent_le_deficient
#print axioms geomAbs_subset_absent
#print axioms height_of_geomAbs

end WilliamsonMurII
