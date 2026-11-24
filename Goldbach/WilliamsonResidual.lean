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

/-! ## Structure of the complements below `P^2`: powersmooth rows -/

/-- A divisor `t > P - 3` divides at most one complement `N - ℓ` with `3 ≤ ℓ ≤ P`. -/
theorem high_power_unique_row {P N ℓ ℓ' t : ℕ} (hℓ : ℓ ≤ P) (hℓ' : ℓ' ≤ P)
    (h3 : 3 ≤ ℓ) (h3' : 3 ≤ ℓ') (hN : P < N) (ht : P - 3 < t)
    (h1 : t ∣ N - ℓ) (h2 : t ∣ N - ℓ') : ℓ = ℓ' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hd : t ∣ (N - ℓ) - (N - ℓ') := Nat.dvd_sub h1 h2
    have he : (N - ℓ) - (N - ℓ') = ℓ' - ℓ := by omega
    rw [he] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : t ∣ (N - ℓ') - (N - ℓ) := Nat.dvd_sub h2 h1
    have he : (N - ℓ') - (N - ℓ) = ℓ - ℓ' := by omega
    rw [he] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- A number whose prime-power components are all `≤ P` divides `lcm(1, …, P)`. -/
theorem powersmooth_dvd_lcm {m P : ℕ} (hm : m ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ^ (m.factorization p) ≤ P) :
    m ∣ (Finset.Icc 1 P).lcm id := by
  classical
  have hpos : ∀ n ∈ Finset.Icc 1 P, id n ≠ 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [id]
    omega
  have hL : (Finset.Icc 1 P).lcm id ≠ 0 := by
    intro h0
    have hd : (Finset.Icc 1 P).lcm id ∣ ∏ n ∈ Finset.Icc 1 P, id n := Finset.lcm_dvd_prod _ _
    rw [h0, zero_dvd_iff] at hd
    exact Finset.prod_ne_zero_iff.mpr hpos hd
  rw [← Nat.factorization_le_iff_dvd hm hL, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Finset.factorization_lcm hpos p]
    have hmem : p ^ (m.factorization p) ∈ Finset.Icc 1 P := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_pow _ _ hp.pos, h p hp⟩
    have hle := Finset.le_sup (f := fun n => (id n).factorization p) hmem
    simp only [id] at hle ⊢
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hle
    exact hle
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]


/-! ### Multiplicative rigidity of the rows (residual note, §7.6)

Two products of two rows coincide only trivially once `N > P²`; below `P²` the
coincidence forces `N · |(a+b) − (c+d)| ≤ P²`. -/

/-- Integer core: `(N-a)(N-b) = (N-c)(N-d)` with `0 ≤ a,b,c,d ≤ P < N/P` forces equal sums and products. -/
theorem mult_rigidity_int {N P a b c d : ℤ} (hPN : P * P < N)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ P) (hb : b ≤ P) (hc : c ≤ P) (hd : d ≤ P)
    (h : (N - a) * (N - b) = (N - c) * (N - d)) :
    a + b = c + d ∧ a * b = c * d := by
  have key : N * ((a + b) - (c + d)) = a * b - c * d := by linear_combination -h
  have hab : a * b ≤ P * P := mul_le_mul ha hb hb0 (by linarith)
  have hcd : c * d ≤ P * P := mul_le_mul hc hd hd0 (by linarith)
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hcd0 : 0 ≤ c * d := mul_nonneg hc0 hd0
  have hs : a + b = c + d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (a + b) - (c + d) ≤ -1 := by linarith
      have hN0 : 0 < N := by nlinarith
      nlinarith
    · have : 1 ≤ (a + b) - (c + d) := by linarith
      have hN0 : 0 < N := by nlinarith
      nlinarith
  refine ⟨hs, ?_⟩
  rw [hs, sub_self, mul_zero] at key
  linarith

/-- Two pairs with the same sum and product coincide (as unordered pairs). -/
theorem pair_eq_of_sum_prod {a b c d : ℤ} (hs : a + b = c + d) (hp : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h0 : (a - c) * (a - d) = 0 := by
    have : b = c + d - a := by linarith
    subst this
    linear_combination -hp
  rcases mul_eq_zero.mp h0 with h1 | h1
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- **Multiplicative rigidity.** For `N > P²` and shifts `a,b,c,d ≤ P`,
`(N-a)(N-b) = (N-c)(N-d)` implies `{a,b} = {c,d}`. -/
theorem mult_rigidity {N P a b c d : ℕ} (hPN : P * P < N)
    (ha : a ≤ P) (hb : b ≤ P) (hc : c ≤ P) (hd : d ≤ P)
    (h : (N - a) * (N - b) = (N - c) * (N - d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hPle : P ≤ N := by nlinarith
  have hz : ((N : ℤ) - a) * ((N : ℤ) - b) = ((N : ℤ) - c) * ((N : ℤ) - d) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub (le_trans ha hPle), Nat.cast_sub (le_trans hb hPle),
      Nat.cast_sub (le_trans hc hPle), Nat.cast_sub (le_trans hd hPle)] at this
    exact this
  have hPN' : (P : ℤ) * P < N := by exact_mod_cast hPN
  obtain ⟨hs, hp⟩ := mult_rigidity_int hPN' (by positivity) (by positivity) (by positivity)
    (by positivity) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast hd) hz
  rcases pair_eq_of_sum_prod hs hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · right; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **Near-rigidity below `P²`.** If `(N-a)(N-b) = (N-c)(N-d)` with `0 ≤ a,b,c,d ≤ P`,
then `N · |(a+b) − (c+d)| ≤ P²`. -/
theorem mult_near_rigidity_int {N P a b c d : ℤ} (hN : 0 ≤ N)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ P) (hb : b ≤ P) (hc : c ≤ P) (hd : d ≤ P)
    (h : (N - a) * (N - b) = (N - c) * (N - d)) :
    N * |(a + b) - (c + d)| ≤ P * P := by
  have key : N * ((a + b) - (c + d)) = a * b - c * d := by linear_combination -h
  have hab : a * b ≤ P * P := mul_le_mul ha hb hb0 (by linarith)
  have hcd : c * d ≤ P * P := mul_le_mul hc hd hd0 (by linarith)
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hcd0 : 0 ≤ c * d := mul_nonneg hc0 hd0
  rw [← abs_of_nonneg hN, ← abs_mul, key, abs_le]
  constructor <;> linarith

#print axioms high_power_unique_row
#print axioms powersmooth_dvd_lcm
#print axioms mult_rigidity
#print axioms mult_near_rigidity_int

end WilliamsonResidual
