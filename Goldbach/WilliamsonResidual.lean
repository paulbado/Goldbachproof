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

/-! ## Near-injectivity below quadratic height -/

/-- **Near-injectivity.** If `q' < q ≤ P`, `b ≥ 1`, and `C·q^b`, `C·q'^b` both lie in
    `[N - P, N - 3]`, then `(q - q')·(N - P) ≤ P·(P - 3)`. -/
theorem near_injective {P N q q' b C : ℕ} (hP : 3 ≤ P) (hPN : P ≤ N) (hq : q ≤ P)
    (hlt : q' < q) (hb : 1 ≤ b)
    (h1 : N - P ≤ C * q ^ b) (h2 : C * q ^ b ≤ N - 3)
    (h3 : N - P ≤ C * q' ^ b) :
    (q - q') * (N - P) ≤ P * (P - 3) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hpow : q' ^ c ≤ q ^ c := Nat.pow_le_pow_left (le_of_lt hlt) c
  have ex : C * q ^ (c + 1) = q * (C * q ^ c) := by ring
  have ey : C * q' ^ (c + 1) = q' * (C * q' ^ c) := by ring
  rw [ex] at h1 h2
  rw [ey] at h3
  set t := C * q ^ c with ht
  have hyt : q' * (C * q' ^ c) ≤ q' * t := Nat.mul_le_mul_left q' (Nat.mul_le_mul_left C hpow)
  -- (q - q') * t ≤ P - 3
  have hdiff : (q - q') * t ≤ P - 3 := by
    have e : (q - q') * t + q' * t = q * t := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hlt)]
    omega
  calc (q - q') * (N - P) ≤ (q - q') * (q * t) := Nat.mul_le_mul_left _ h1
    _ = q * ((q - q') * t) := by ring
    _ ≤ P * (P - 3) := Nat.mul_le_mul hq hdiff

/-- A finite set of naturals whose pairwise gaps satisfy `(x - y)·D₁ ≤ D₂` (with `D₁ > 0`) has at most
    `D₂ / D₁ + 1` elements. -/
theorem card_le_of_gaps (S : Finset ℕ) {D₁ D₂ : ℕ} (hD : 0 < D₁)
    (hgap : ∀ x ∈ S, ∀ y ∈ S, y < x → (x - y) * D₁ ≤ D₂) :
    S.card ≤ D₂ / D₁ + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with h | hne
  · simp [h]
  set m := S.min' hne
  have hbound : ∀ x ∈ S, x - m ≤ D₂ / D₁ := by
    intro x hx
    rcases Nat.eq_or_lt_of_le (S.min'_le x hx) with he | hl
    · rw [← he, Nat.sub_self]; exact Nat.zero_le _
    · exact (Nat.le_div_iff_mul_le hD).2 (hgap x hx m (S.min'_mem hne) hl)
  generalize D₂ / D₁ = k at hbound ⊢
  have hsub : S ⊆ Finset.Icc m (m + k) := by
    intro x hx
    have hmx : m ≤ x := S.min'_le x hx
    have := hbound x hx
    rw [Finset.mem_Icc]
    omega
  calc S.card ≤ (Finset.Icc m (m + k)).card := Finset.card_le_card hsub
    _ = k + 1 := by rw [Nat.card_Icc]; omega

/-- **Counting by fibers `(b, C)`.** Let `Q` be a set of naturals `≤ P`, each with an exponent
    `1 ≤ e q ≤ β` and a cofactor `1 ≤ c q ≤ Cmax` such that `c q · q^(e q) ∈ [N - P, N - 3]`. Then
    `#Q ≤ (P(P-3)/(N-P) + 1) · (β · Cmax)`. -/
theorem card_small_cofactor (Q : Finset ℕ) {P N β Cmax : ℕ} (e c : ℕ → ℕ)
    (hP : 3 ≤ P) (hPN : P < N)
    (hQ : ∀ q ∈ Q, q ≤ P ∧ 1 ≤ e q ∧ e q ≤ β ∧ 1 ≤ c q ∧ c q ≤ Cmax ∧
      N - P ≤ c q * q ^ e q ∧ c q * q ^ e q ≤ N - 3) :
    Q.card ≤ (P * (P - 3) / (N - P) + 1) * (β * Cmax) := by
  classical
  let f : ℕ → ℕ × ℕ := fun q => (e q, c q)
  have himg : Q.image f ⊆ Finset.Icc 1 β ×ˢ Finset.Icc 1 Cmax := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨-, h1, h2, h3, h4, -, -⟩ := hQ q hq
    simp [f, Finset.mem_product, Finset.mem_Icc, h1, h2, h3, h4]
  have hfib : ∀ x ∈ Q.image f, (Q.filter fun q => f q = x).card ≤ P * (P - 3) / (N - P) + 1 := by
    intro x _
    apply card_le_of_gaps _ (by omega)
    intro q hq q' hq' hlt
    obtain ⟨hqQ, hfq⟩ := Finset.mem_filter.1 hq
    obtain ⟨hq'Q, hfq'⟩ := Finset.mem_filter.1 hq'
    obtain ⟨hqP, he1, -, -, -, h1, h2⟩ := hQ q hqQ
    obtain ⟨-, -, -, -, -, h3, -⟩ := hQ q' hq'Q
    have hee : e q' = e q := congrArg Prod.fst (hfq'.trans hfq.symm)
    have hcc : c q' = c q := congrArg Prod.snd (hfq'.trans hfq.symm)
    rw [hee, hcc] at h3
    exact near_injective hP (le_of_lt hPN) hqP hlt he1 h1 h2 h3
  calc Q.card ≤ (P * (P - 3) / (N - P) + 1) * (Q.image f).card :=
        Finset.card_le_mul_card_image Q _ hfib
    _ ≤ (P * (P - 3) / (N - P) + 1) * (Finset.Icc 1 β ×ˢ Finset.Icc 1 Cmax).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)
    _ = (P * (P - 3) / (N - P) + 1) * (β * Cmax) := by
        rw [Finset.card_product]; simp

#print axioms near_injective
#print axioms card_small_cofactor

end WilliamsonResidual
