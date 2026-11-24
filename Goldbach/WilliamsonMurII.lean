import Mathlib

/-! Mur II, arithmetic route. Compiles against Mathlib v4.36.0. The open assertion is a
    definition, not an axiom or a theorem. No numerical cutoff is assumed. -/
namespace WilliamsonMurII

def Index (P i : ℕ) : Prop := Nat.Prime i ∧ 3 ≤ i ∧ i ≤ P

def BadFamily (P N : ℕ) : Prop :=
  P < N ∧ Even N ∧
  ∀ i : ℕ, Index P i →
    ¬ Nat.Prime (N - i) ∧
    ∀ r : ℕ, Nat.Prime r → r ∣ (N - i) → r < P

/-- A prime power present on one line and on no other. -/
def Private (P N i : ℕ) : Prop :=
  ∃ r a : ℕ, Nat.Prime r ∧ 0 < a ∧ r ^ a ∣ (N - i) ∧
    ∀ j : ℕ, Index P j → j ≠ i → ¬ r ^ a ∣ (N - j)

def Deficient (P N i : ℕ) : Prop := Index P i ∧ ¬ Private P N i

def MultipleDeficits (P N : ℕ) : Prop :=
  ∃ i j : ℕ, i ≠ j ∧ Deficient P N i ∧ Deficient P N j

def PreviousPrime (p P : ℕ) : Prop :=
  Index P p ∧ p < P ∧
    ∀ q : ℕ, Nat.Prime q → q < P → q ≤ p

/-- Necessary conditions inherited from a first failure (proved in the
    manuscript; derivation from first failure is not formalized here). -/
def PreviousRankConditions (p P N : ℕ) : Prop :=
  PreviousPrime p P ∧ 3 * p + 3 ≤ N ∧
  ∃ j : ℕ, Index p j ∧ N % p = j % p

def DifferenceCertificate (P i d : ℕ) : Prop :=
  ∀ r a : ℕ, Nat.Prime r → 0 < a → r ^ a ∣ d →
    ∃ j : ℕ, Index P j ∧ j ≠ i ∧
      r ^ a ∣ (max i j - min i j)

theorem dvd_difference (N i j t : ℕ)
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

/-- Absence of a private prime power forces each prime power to be shared. -/
theorem shared_power {P N i r a : ℕ}
    (hi : Deficient P N i) (hr : Nat.Prime r) (ha : 0 < a)
    (hd : r ^ a ∣ N - i) :
    ∃ j : ℕ, Index P j ∧ j ≠ i ∧ r ^ a ∣ N - j := by
  classical
  by_contra h
  apply hi.2
  refine ⟨r, a, hr, ha, hd, ?_⟩
  intro j hj hji hjd
  exact h ⟨j, hj, hji, hjd⟩

theorem deficient_certificate {P N i : ℕ}
    (hN : P < N) (hi : Deficient P N i) :
    DifferenceCertificate P i (N - i) := by
  intro r a hr ha hd
  obtain ⟨j, hj, hji, hjd⟩ := shared_power hi hr ha hd
  refine ⟨j, hj, hji, ?_⟩
  exact dvd_difference N i j _ (le_trans hi.1.2.2 (Nat.le_of_lt hN))
    (le_trans hj.2.2 (Nat.le_of_lt hN)) hd hjd

/-- Simultaneous arithmetic constraints, retaining the common N. -/
theorem joint_certificate {P N : ℕ}
    (hN : P < N) (hII : MultipleDeficits P N) :
    ∃ i j : ℕ, Index P i ∧ Index P j ∧ i ≠ j ∧
      DifferenceCertificate P i (N - i) ∧
      DifferenceCertificate P j (N - j) ∧
      Nat.gcd (N - i) (N - j) ∣ (max i j - min i j) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hII
  refine ⟨i, j, hi.1, hj.1, hij, deficient_certificate hN hi,
    deficient_certificate hN hj, ?_⟩
  exact dvd_difference N i j _ (le_trans hi.1.2.2 (Nat.le_of_lt hN))
    (le_trans hj.1.2.2 (Nat.le_of_lt hN))
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

/-- OPEN target: exclude only bad families with multiple deficits and
    first-failure necessary conditions. No polynomial sieve bound imposed. -/
def WallIIAt (P₀ : ℕ) : Prop :=
  ∀ P p N : ℕ, P₀ ≤ P → 5 ≤ P → Nat.Prime P →
    PreviousRankConditions p P N → BadFamily P N →
    MultipleDeficits P N → False

/-- Interface for the complementary branch; the old Wall I theorem
    must be connected to it via the private-owner counting reduction. -/
def WallIAt (P₀ : ℕ) : Prop :=
  ∀ P p N : ℕ, P₀ ≤ P → 5 ≤ P → Nat.Prime P →
    PreviousRankConditions p P N → BadFamily P N →
    ¬ MultipleDeficits P N → False

/-- Logical assembly only; neither closure is asserted here. -/
theorem combine_walls (P₁ P₂ : ℕ)
    (hI : WallIAt P₁) (hII : WallIIAt P₂) :
    ∀ P p N : ℕ, max P₁ P₂ ≤ P → 5 ≤ P → Nat.Prime P →
      PreviousRankConditions p P N → BadFamily P N → False := by
  intro P p N hP h5 hp hprev hb
  by_cases h : MultipleDeficits P N
  · exact hII P p N (le_trans (le_max_right P₁ P₂) hP) h5 hp hprev hb h
  · exact hI P p N (le_trans (le_max_left P₁ P₂) hP) h5 hp hprev hb h

#print axioms shared_power
#print axioms joint_certificate
#print axioms combine_walls
end WilliamsonMurII
