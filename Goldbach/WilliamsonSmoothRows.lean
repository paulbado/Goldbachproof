import Goldbach.WilliamsonMurII

/-! # Smooth rows and the large-prime incidences below `P²`

For `N < P²`, a row `N - ℓ` has at most one prime factor `r ≥ P`. Hence the rows that are
not `P`-rough-free ("good" rows, with a prime factor `≥ P`) are counted exactly by the
incidences `Σ_{r ≥ P} n_N(r)`, and a bad family is the case where the smooth rows exhaust
all rows (`docs/tex/localized-buchstab-wall-ii.tex`, §8). -/

namespace WilliamsonMurII
open Finset

/-- Below `P²`, two primes `≥ P` dividing the same row coincide. -/
theorem large_prime_factor_unique {P N ℓ r r' : ℕ} (hN : N < P * P)
    (hr : Nat.Prime r) (hr' : Nat.Prime r') (hPr : P ≤ r) (hPr' : P ≤ r')
    (h : r ∣ N - ℓ) (h' : r' ∣ N - ℓ) (hpos : 0 < N - ℓ) : r = r' := by
  by_contra hne
  have hcop : Nat.Coprime r r' := (Nat.coprime_primes hr hr').2 hne
  have hd : r * r' ∣ N - ℓ := hcop.mul_dvd_of_dvd_of_dvd h h'
  have h1 := Nat.le_of_dvd hpos hd
  have h2 : P * P ≤ r * r' := Nat.mul_le_mul hPr hPr'
  have h3 : N - ℓ ≤ N := Nat.sub_le N ℓ
  omega

/-- The prime indices `3 ≤ ℓ ≤ P`, as a finset. -/
noncomputable def idxFin (P : ℕ) : Finset ℕ := by
  classical exact (range (P + 1)).filter (Index P)

theorem mem_idxFin {P ℓ : ℕ} : ℓ ∈ idxFin P ↔ Index P ℓ := by
  classical
  unfold idxFin
  simp only [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by have := h.2.2; omega, h⟩⟩

/-- **Exact incidence count below `P²`.** The number of rows with a prime factor `≥ P`
    equals `Σ_{P ≤ r ≤ N, r prime} #{ℓ : r ∣ N - ℓ}`. -/
theorem card_good_rows_eq_sum {P N : ℕ} (hN : N < P * P) (hPN : P < N) :
    (by classical exact ((idxFin P).filter
        (fun ℓ => ∃ r, Nat.Prime r ∧ P ≤ r ∧ r ∣ N - ℓ)).card) =
    ∑ r ∈ (Icc P N).filter Nat.Prime,
      (by classical exact ((idxFin P).filter (fun ℓ => r ∣ N - ℓ)).card) := by
  classical
  rw [← card_biUnion]
  · congr 1
    ext ℓ
    simp only [mem_filter, mem_biUnion, mem_Icc]
    constructor
    · rintro ⟨hℓ, r, hr, hPr, hd⟩
      have hℓP := (mem_idxFin.1 hℓ).2.2
      have hpos : 0 < N - ℓ := by omega
      exact ⟨r, ⟨⟨hPr, le_trans (Nat.le_of_dvd hpos hd) (Nat.sub_le N ℓ)⟩, hr⟩, hℓ, hd⟩
    · rintro ⟨r, ⟨⟨hPr, -⟩, hr⟩, hℓ, hd⟩
      exact ⟨hℓ, r, hr, hPr, hd⟩
  · intro r hr r' hr' hne
    simp only [coe_filter, mem_Icc] at hr hr'
    rw [Function.onFun, disjoint_left]
    intro ℓ h1 h2
    simp only [mem_filter] at h1 h2
    have hℓP := (mem_idxFin.1 h1.1).2.2
    exact hne (large_prime_factor_unique hN hr.2 hr'.2 hr.1.1 hr'.1.1 h1.2 h2.2 (by omega))

/-- A bad family has no good row: every row is `P`-smooth (all prime factors `< P`). -/
theorem badFamily_no_good_row {P N : ℕ} (hb : BadFamily P N) :
    ∀ ℓ ∈ idxFin P, ¬ ∃ r, Nat.Prime r ∧ P ≤ r ∧ r ∣ N - ℓ := by
  rintro ℓ hℓ ⟨r, hr, hPr, hd⟩
  have := (hb.2.2 ℓ (mem_idxFin.1 hℓ)).2 r hr hd
  omega

/-- Hence below `P²`: if some prime `r ≥ P` has a row in its class, there is no bad family.
    Equivalently, a bad family forces every incidence `n_N(r)`, `P ≤ r ≤ N`, to vanish. -/
theorem not_badFamily_of_incidence {P N r ℓ : ℕ} (hr : Nat.Prime r) (hPr : P ≤ r)
    (hℓ : Index P ℓ) (hd : r ∣ N - ℓ) : ¬ BadFamily P N := fun hb =>
  badFamily_no_good_row hb ℓ (mem_idxFin.2 hℓ) ⟨r, hr, hPr, hd⟩

#print axioms large_prime_factor_unique
#print axioms card_good_rows_eq_sum
#print axioms badFamily_no_good_row

end WilliamsonMurII
