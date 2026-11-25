import Goldbach.WilliamsonMurII

/-! # Dual form of a bad family

For `2P ≤ N`, a bad family of rank `P` at height `N` is exactly an even `N` whose
residues modulo every prime `r ≥ P` avoid the prime indices `3 ≤ ℓ ≤ P`.  Writing
`N = ℓ + m r`, excluding a family at `N` is therefore the existence of a solution of
`ℓ + m r = N` with `ℓ ≤ P` and `r ≥ P` both prime (`docs/switched-sieve.md` §4). -/

namespace WilliamsonMurII

theorem badFamily_iff_residues {P N : ℕ} (hP : 3 ≤ P) (hPN : 2 * P ≤ N) (hN : Even N) :
    BadFamily P N ↔ ∀ r, Nat.Prime r → P ≤ r → ∀ ℓ, Index P ℓ → ¬ ℓ ≡ N [MOD r] := by
  constructor
  · rintro ⟨-, -, h⟩ r hr hPr ℓ hℓ hmod
    have hle : ℓ ≤ N := by have := hℓ.2.2; omega
    have hd : r ∣ N - ℓ := (Nat.modEq_iff_dvd' hle).1 hmod
    have := (h ℓ hℓ).2 r hr hd
    omega
  · intro h
    refine ⟨by omega, hN, fun ℓ hℓ => ⟨fun hpr => ?_, fun r hr hd => ?_⟩⟩
    · have hle : ℓ ≤ N := by have := hℓ.2.2; omega
      have hge : P ≤ N - ℓ := by have := hℓ.2.2; omega
      exact h (N - ℓ) hpr hge ℓ hℓ ((Nat.modEq_iff_dvd' hle).2 dvd_rfl)
    · by_contra hlt
      push Not at hlt
      have hle : ℓ ≤ N := by have := hℓ.2.2; omega
      exact h r hr hlt ℓ hℓ ((Nat.modEq_iff_dvd' hle).2 hd)

/-- Equivalently: `N` is *not* a bad family iff `N = ℓ + m r` for some prime index `ℓ`,
    prime `r ≥ P` and `m ≥ 0`. -/
theorem not_badFamily_iff_rep {P N : ℕ} (hP : 3 ≤ P) (hPN : 2 * P ≤ N) (hN : Even N) :
    ¬ BadFamily P N ↔ ∃ ℓ r m, Index P ℓ ∧ Nat.Prime r ∧ P ≤ r ∧ ℓ + m * r = N := by
  rw [badFamily_iff_residues hP hPN hN]
  push Not
  constructor
  · rintro ⟨r, hr, hPr, ℓ, hℓ, hmod⟩
    have hle : ℓ ≤ N := by have := hℓ.2.2; omega
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hle).1 hmod
    exact ⟨ℓ, r, m, hℓ, hr, hPr, by rw [mul_comm, ← hm]; omega⟩
  · rintro ⟨ℓ, r, m, hℓ, hr, hPr, hs⟩
    refine ⟨r, hr, hPr, ℓ, hℓ, (Nat.modEq_iff_dvd' (by omega)).2 ⟨m, by rw [mul_comm]; omega⟩⟩

#print axioms badFamily_iff_residues
#print axioms not_badFamily_iff_rep

end WilliamsonMurII
