import Mathlib

/-! # Residual region — cofactor injectivity above quadratic height

If `N ≥ P²`, two numbers `C·q^b` and `C·q'^b` with the same cofactor `C ≥ 1` and the same
exponent `b ≥ 1` cannot both lie in the window `[N - P, N - 3]` of the complements, unless `q = q'`
(for `q, q' < P`). So in a restricted-support family with `N ≥ P²`, the map
`q ↦ (b_q, C_q)` (exponent and cofactor on a row carrying `q`) is injective.

Fully proved: only the standard axioms are used. -/

namespace WilliamsonResidual

theorem cofactor_injective {P N q q' b C : ℕ} (hP : 3 ≤ P) (hN : P * P ≤ N)
    (hq : q < P) (hq' : q' < P) (hb : 1 ≤ b) (hC : 1 ≤ C)
    (h1 : N - P ≤ C * q ^ b) (h2 : C * q ^ b ≤ N - 3)
    (h3 : N - P ≤ C * q' ^ b) (h4 : C * q' ^ b ≤ N - 3) : q = q' := by
  -- symmetric statement; treat q' < q, the other case is the same
  have key : ∀ {x y : ℕ}, x < P → y < x → N - P ≤ C * x ^ b → C * x ^ b ≤ N - 3 →
      N - P ≤ C * y ^ b → False := by
    intro x y hx hyx hx1 hx2 hy1
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have hpow : y ^ c ≤ x ^ c := Nat.pow_le_pow_left (le_of_lt hyx) c
    have ex : C * x ^ (c + 1) = x * (C * x ^ c) := by ring
    have ey : C * y ^ (c + 1) = y * (C * y ^ c) := by ring
    rw [ex] at hx1 hx2
    rw [ey] at hy1
    set t := C * x ^ c with ht
    have hyt : y * (C * y ^ c) ≤ y * t := Nat.mul_le_mul_left y (Nat.mul_le_mul_left C hpow)
    -- t ≥ P, because x * t ≥ N - P ≥ P*(P-1) and x ≤ P - 1
    have hNP : P * (P - 1) ≤ N - P := by
      have : P * (P - 1) + P = P * P := by
        cases P with
        | zero => omega
        | succ n => simp [Nat.mul_succ]
      omega
    have htP : P ≤ t := by
      by_contra hlt
      push Not at hlt
      have : x * t ≤ (P - 1) * (P - 1) := Nat.mul_le_mul (by omega) (by omega)
      have : (P - 1) * (P - 1) < P * (P - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      omega
    -- x*t ≥ y*t + t ≥ (N - P) + P = N, contradiction with x*t ≤ N - 3
    have hxy : y * t + t ≤ x * t := by
      have : (y + 1) * t ≤ x * t := Nat.mul_le_mul_right t (by omega)
      nlinarith
    have hN3 : 3 ≤ N := by nlinarith
    omega
  rcases lt_trichotomy q q' with h | h | h
  · exact (key hq' h h3 h4 h1).elim
  · exact h
  · exact (key hq h h1 h2 h3).elim

#print axioms cofactor_injective

end WilliamsonResidual
