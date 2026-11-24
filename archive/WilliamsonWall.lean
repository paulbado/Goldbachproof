import Mathlib

/-! Williamson certificate reduction and finite cover.
    Compiles against Mathlib v4.36.0. No sorry or new axiom declarations.
    The asymptotic cover is a proposition, not an asserted theorem. -/

namespace Williamson

/-- Pigeonhole step: more rows than columns implies a row with no
    positive strictly private maximum. -/
theorem exists_nonprivate {I R : Type*} [Fintype I] [Fintype R]
    (v : I → R → ℕ) (hc : Fintype.card R < Fintype.card I) :
    ∃ i : I, ∀ r : R, 0 < v i r →
      ∃ j : I, j ≠ i ∧ v i r ≤ v j r := by
  classical
  by_contra h
  have hp : ∀ i : I, ∃ r : R, 0 < v i r ∧
      ∀ j : I, j ≠ i → v j r < v i r := by
    intro i
    by_contra hn
    apply h
    refine ⟨i, ?_⟩
    intro r hr
    by_contra hno
    apply hn
    refine ⟨r, hr, ?_⟩
    intro j hj
    by_contra hlt
    exact hno ⟨j, hj, by omega⟩
  choose f hf using hp
  have hi : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h₁ := (hf i).2 j (Ne.symm hne)
    have h₂ := (hf j).2 i hne
    rw [hij] at h₁
    omega
  have hh := Fintype.card_le_of_injective f hi
  omega

/-- Two reflected complements sharing a divisor force that divisor
    to divide the difference of their indices. -/
theorem dvd_index_difference (N i j t : ℕ)
    (hi : i ≤ N) (hj : j ≤ N)
    (h₁ : t ∣ N - i) (h₂ : t ∣ N - j) :
    t ∣ max i j - min i j := by
  rcases le_total i j with h | h
  · rw [max_eq_right h, min_eq_left h]
    have he : (N - i) - (N - j) = j - i := by omega
    rw [← he]
    exact Nat.dvd_sub h₁ h₂
  · rw [max_eq_left h, min_eq_right h]
    have he : (N - j) - (N - i) = i - j := by omega
    rw [← he]
    exact Nat.dvd_sub h₂ h₁

/-- The exact finite arithmetic predicates. -/
def PrimeIndex (P i : ℕ) : Prop := Nat.Prime i ∧ 3 ≤ i ∧ i ≤ P

def PreviousPrime (p P : ℕ) : Prop :=
  PrimeIndex P p ∧ p < P ∧
  ∀ q : ℕ, Nat.Prime q → q < P → q ≤ p

def DifferenceCertificate (P i d : ℕ) : Prop :=
  0 < d ∧ Odd d ∧
  ∀ r a : ℕ, Nat.Prime r → 0 < a → r ^ a ∣ d →
    ∃ j : ℕ, PrimeIndex P j ∧ j ≠ i ∧
      r ^ a ∣ (max i j - min i j)

def Admissible (P p i d : ℕ) : Prop :=
  PrimeIndex P i ∧ DifferenceCertificate P i d ∧
  Even (i + d) ∧ 3 * p + 3 ≤ i + d ∧
  ∃ j : ℕ, PrimeIndex p j ∧ (i + d) % p = j % p

def LargePrimeWitness (P i d B : ℕ) : Prop :=
  ∃ j q : ℕ, PrimeIndex P j ∧ j ≠ i ∧
    Nat.Prime q ∧ P ≤ q ∧ q ≤ B ∧ q ∣ (i + d - j)

/-- OPEN: a polynomial-window covering theorem sufficient for eventual
    exclusion of first failing endpoints. -/
def UniformCertificateExclusion : Prop :=
  ∃ A P₀ : ℕ, 1 < A ∧ ∀ P p i d : ℕ,
    5 ≤ P → P₀ ≤ P → Nat.Prime P → PreviousPrime p P →
    Admissible P p i d → LargePrimeWitness P i d (P ^ A)

/-- OPEN, stronger target suggested by finite experiments only. -/
def LinearCertificateExclusion : Prop :=
  ∃ C P₀ : ℕ, ∀ P p i d : ℕ,
    5 ≤ P → P₀ ≤ P → Nat.Prime P → PreviousPrime p P →
    Admissible P p i d → LargePrimeWitness P i d (C * P)

/-- A linear cover implies the polynomial cover (exponent 2). -/
theorem polynomial_of_linear (h : LinearCertificateExclusion) :
    UniformCertificateExclusion := by
  obtain ⟨C, P₀, hC⟩ := h
  refine ⟨2, max C P₀, by decide, ?_⟩
  intro P p i d h5 hP hprime hp ha
  have h₀ : P₀ ≤ P := le_trans (le_max_right C P₀) hP
  have hCP : C ≤ P := le_trans (le_max_left C P₀) hP
  obtain ⟨j, q, hj, hji, hq, hlow, hu, hdvd⟩ :=
    hC P p i d h5 h₀ hprime hp ha
  refine ⟨j, q, hj, hji, hq, hlow, ?_, hdvd⟩
  calc
    q ≤ C * P := hu
    _ ≤ P * P := Nat.mul_le_mul_right P hCP
    _ = P ^ 2 := (pow_two P).symm

/-- An admissible line incompatible with a large-prime witness. -/
def NoLargeFactors (P N : ℕ) : Prop :=
  ∀ j q : ℕ, PrimeIndex P j → Nat.Prime q →
    q ∣ (N - j) → q < P

theorem excludes_line (P i d B : ℕ)
    (hbad : NoLargeFactors P (i+d))
    (hw : LargePrimeWitness P i d B) : False := by
  obtain ⟨j, q, hj, _, hq, hlow, _, hdvd⟩ := hw
  exact (not_lt_of_ge hlow) (hbad j q hj hq hdvd)

/-! Executable arithmetic checker. The completeness of the divisor
    enumeration relative to DifferenceCertificate remains to be formalized.
    The #eval below is a computation, not a proof of the universal theorem. -/

def primeIndices (P : ℕ) : List ℕ :=
  (List.range (P+1)).filter (fun r => decide (3 ≤ r ∧ Nat.Prime r))

def previousPrime (P : ℕ) : ℕ :=
  ((primeIndices (P-1)).reverse.head?).getD 0

def powersAt (P i r : ℕ) : List ℕ :=
  let js := (primeIndices P).filter (fun j => decide (j ≠ i))
  1 :: (List.range (Nat.log 2 P)).filterMap (fun a =>
    let t := r^(a+1)
    if js.any (fun j => decide ((max i j - min i j) % t = 0))
    then some t else none)

def certificateDivisors (P i : ℕ) : List ℕ :=
  (primeIndices ((P-3)/2)).foldl (fun ds r =>
    let ts := powersAt P i r
    ds.flatMap (fun d => ts.map (fun t => d*t))) [1]

def admissibleDivisors (P p i : ℕ) : List ℕ :=
  let js := primeIndices p
  (certificateDivisors P i).filter (fun d =>
    decide (3*p+3 ≤ i+d) && decide ((i+d)%2 = 0) &&
    js.any (fun j => decide ((i+d)%p = j%p)))

def rowStats (P C : ℕ) : ℕ × ℕ :=
  let p := previousPrime P
  let is := primeIndices P
  let qs := (primeIndices (C*P)).filter (fun q => decide (P ≤ q))
  is.foldl (fun acc i =>
    let js := is.filter (fun j => decide (j ≠ i))
    let ds := admissibleDivisors P p i
    let covered := fun d : ℕ => qs.any (fun q =>
      js.any (fun j => decide ((i+d)%q = j%q)))
    (acc.1 + ds.length, acc.2 + (ds.filter (fun d => !(covered d))).length)) (0,0)

def rangeStats (B C : ℕ) : ℕ × ℕ :=
  ((primeIndices B).filter (fun P => decide (5 ≤ P))).foldl
    (fun acc P => let s := rowStats P C; (acc.1+s.1, acc.2+s.2)) (0,0)

-- Independent Python run: expected output (229153, 0).
-- Lean replay (also run in CI): see scripts/CheckRangeStats.lean
-- #eval rangeStats 151 13

#print axioms exists_nonprivate
#print axioms dvd_index_difference
#print axioms polynomial_of_linear
#print axioms excludes_line

end Williamson
