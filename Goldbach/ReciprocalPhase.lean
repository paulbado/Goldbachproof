import Mathlib

/-!
# Algebraic steps of Proposition 16.2χ and of the top-range theorem

See `docs/prop-16-2-chi-top-range.md`. Only the exact algebraic identities are formalized here;
the analytic estimates (Kusmin–Landau, van der Corput, Vaughan, Selberg, Vaaler) are not.
-/

namespace ReciprocalPhase

/-- Type I, residue classes: writing `m = d k + r` turns the phase `Y/(t m)` into a
shifted reciprocal phase `A/(k + s)` with `A = Y/(t d)` and `s = r/d`. -/
theorem phase_residue_shift (Y t d k r : ℝ) (ht : t ≠ 0) (hd : d ≠ 0) (hm : d * k + r ≠ 0) :
    Y / (t * (d * k + r)) = (Y / (t * d)) / (k + r / d) := by
  have hk : k + r / d ≠ 0 := by
    intro h
    apply hm
    have : d * (k + r / d) = d * k + r := by field_simp
    rw [← this, h, mul_zero]
  field_simp

/-- Type II, after Cauchy–Schwarz: the difference of two reciprocal phases is again a
reciprocal phase in the free variable, with coefficient `Y (m' - m)/(m m')`. -/
theorem phase_difference (Y m m' k : ℝ) (hm : m ≠ 0) (hm' : m' ≠ 0) (hk : k ≠ 0) :
    Y / (m * k) - Y / (m' * k) = (Y * (m' - m) / (m * m')) / k := by
  field_simp

/-- The sawtooth `ψ(z) = z - ⌊z⌋ - 1/2`. -/
noncomputable def saw (z : ℝ) : ℝ := z - ⌊z⌋ - 1 / 2

/-- Exact count of integers in `[x, y]` (identity (7.1) of `hypothesis-T.md` after rescaling):
`⌊y⌋ - ⌈x⌉ + 1 = (y - x) - ψ(y) - ψ(-x)`. -/
theorem floor_sub_ceil_eq (x y : ℝ) :
    ((⌊y⌋ - ⌈x⌉ + 1 : ℤ) : ℝ) = (y - x) - saw y - saw (-x) := by
  unfold saw
  have hc : ⌈x⌉ = -⌊-x⌋ := by rw [Int.floor_neg]; ring
  rw [hc]
  push_cast
  ring

/-- CRT for the sieve: for odd `e`, the conditions "`b` odd and `b ≡ c (mod e)`" define a
single class modulo `2e`. -/
theorem odd_class_mod_two_mul {e : ℤ} (he : e % 2 = 1) (c : ℤ) :
    ∃ β : ℤ, ∀ b : ℤ, (b % 2 = 1 ∧ b ≡ c [ZMOD e]) ↔ b ≡ β [ZMOD (2 * e)] := by
  have hg : Int.gcd 2 e = 1 := by
    have : Int.gcd 2 e = Int.gcd 2 (e % 2) := by
      rw [Int.gcd_comm, ← Int.gcd_emod, Int.gcd_comm]
    rw [this, he]; rfl
  have hcop : (Int.natAbs 2).Coprime (Int.natAbs e) := hg
  -- choose β odd with β ≡ c mod e
  obtain ⟨β, hβ2, hβe⟩ : ∃ β : ℤ, β % 2 = 1 ∧ β ≡ c [ZMOD e] := by
    rcases Int.emod_two_eq_zero_or_one c with h | h
    · refine ⟨c + e, ?_, ?_⟩
      · omega
      · show (c + e) % e = c % e
        simp
    · exact ⟨c, h, Int.ModEq.refl c⟩
  refine ⟨β, fun b => ?_⟩
  rw [← Int.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · rintro ⟨hb2, hbe⟩
    refine ⟨?_, hbe.trans hβe.symm⟩
    show b % 2 = β % 2
    rw [hb2, hβ2]
  · rintro ⟨hb2, hbe⟩
    refine ⟨?_, hbe.trans hβe⟩
    have : b % 2 = β % 2 := hb2
    omega

end ReciprocalPhase

#print axioms ReciprocalPhase.phase_residue_shift
#print axioms ReciprocalPhase.phase_difference
#print axioms ReciprocalPhase.floor_sub_ceil_eq
#print axioms ReciprocalPhase.odd_class_mod_two_mul
