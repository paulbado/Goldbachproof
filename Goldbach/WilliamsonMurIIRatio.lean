import Goldbach.WilliamsonMurIIClosure

/-! # Mur II — exact ratio identities (17.4), (17.1), (17.5)–(17.6)

Reference: I. O. Bado, *A Closure Chain Toward Williamson's Conjecture*,
§17.1–17.2 (DOI 10.13140/RG.2.2.34840.97281).

Generic part (any finite index set `I` and positive values `M ℓ`):
* `L = lcm_{ℓ ∈ I} M ℓ`, `b q = v_q(L) = max_ℓ v_q(M ℓ)`;
* an assignment `ψ` sends each prime `q ∣ L` to a row where the maximum is attained;
* `R ℓ = M ℓ / ∏_{ψ q = ℓ} q^{b q}` and `B = ∏_ℓ R ℓ`.

Proved:
* `ratio_identity` (17.4):   `∏_ℓ M ℓ = L * B`;
* `untouched_prod_dvd` (17.5): untouched rows satisfy `∏_{ℓ ∈ U} M ℓ ∣ B`;
* `count_identity`:          `z + #F = #I + e + t` (generic form of (17.1));
* `pow_le_B` (17.6):         `A ^ (z - t) ≤ B` whenever every `M ℓ ≥ A`.

Mur II specialization (`I = P ∩ [3,P]`, `M ℓ = N - ℓ`, bad family):
* `deficit_identity` (17.1): `z = 1 + a + t + e`;
* `factor_one_budget` (17.6): `(N - P)^(1 + a + e) ≤ B`, with `L * B = ∏ (N - ℓ)`;
* `deficient_iff_rowDef`: the manuscript's "no private certificate" is `Deficient`.

Fully proved: only the standard axioms are used. -/

namespace WilliamsonMurII
namespace Ratio
open Finset
open scoped Classical

variable (I : Finset ℕ) (M : ℕ → ℕ)

/-- `L = lcm_{ℓ ∈ I} M ℓ`. -/
def L : ℕ := I.lcm M
/-- `b q = v_q(L)`. -/
def b (q : ℕ) : ℕ := (L I M).factorization q
/-- The present primes. -/
def F : Finset ℕ := (L I M).primeFactors

/-- An assignment of maximal powers. -/
def IsAssignment (ψ : ℕ → ℕ) : Prop :=
  ∀ q ∈ F I M, ψ q ∈ I ∧ (M (ψ q)).factorization q = b I M q

/-- The maximal powers assigned to the row `ℓ`. -/
def assigned (ψ : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  ∏ q ∈ (F I M).filter (fun q => ψ q = ℓ), q ^ b I M q

/-- `R ℓ` of (17.3). -/
def R (ψ : ℕ → ℕ) (ℓ : ℕ) : ℕ := M ℓ / assigned I M ψ ℓ

/-- The budget `B = ∏ R ℓ`. -/
def B (ψ : ℕ → ℕ) : ℕ := ∏ ℓ ∈ I, R I M ψ ℓ

/-- `q` has its maximum strictly on the row `ℓ` alone (a private certificate). -/
def privAt (ℓ q : ℕ) : Prop :=
  q ∈ F I M ∧ (M ℓ).factorization q = b I M q ∧
    ∀ ℓ' ∈ I, ℓ' ≠ ℓ → (M ℓ').factorization q < b I M q

/-- A present prime whose maximum is not private (a tied maximum). -/
def tied (q : ℕ) : Prop := q ∈ F I M ∧ ¬ ∃ ℓ ∈ I, privAt I M ℓ q

/-- A row with no private certificate. -/
def rowDef (ℓ : ℕ) : Prop := ¬ ∃ q, privAt I M ℓ q

variable {I M}

theorem b_eq (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) (q : ℕ) :
    b I M q = I.sup (fun ℓ => (M ℓ).factorization q) :=
  Finset.factorization_lcm hM q

theorem L_ne_zero (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) : L I M ≠ 0 := by
  intro h
  have hd : L I M ∣ ∏ ℓ ∈ I, M ℓ := Finset.lcm_dvd_prod I M
  rw [h, zero_dvd_iff] at hd
  exact prod_ne_zero_iff.mpr hM hd

theorem le_b (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ℓ q : ℕ} (hℓ : ℓ ∈ I) :
    (M ℓ).factorization q ≤ b I M q := by
  rw [b_eq hM]
  exact le_sup (f := fun ℓ => (M ℓ).factorization q) hℓ

/-- Assignments exist. -/
theorem exists_assignment (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) : ∃ ψ, IsAssignment I M ψ := by
  classical
  have h : ∀ q ∈ F I M, ∃ ℓ ∈ I, (M ℓ).factorization q = b I M q := by
    intro q hq
    have hpos : 0 < b I M q := by
      simp only [F, b] at hq ⊢
      exact (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd
        (L_ne_zero hM) (Nat.dvd_of_mem_primeFactors hq)
    have hne : I.Nonempty := by
      by_contra hI
      rw [not_nonempty_iff_eq_empty] at hI
      rw [b_eq hM, hI, sup_empty] at hpos
      exact absurd hpos (lt_irrefl 0)
    obtain ⟨ℓ, hℓ, he⟩ := exists_mem_eq_sup I hne (fun ℓ => (M ℓ).factorization q)
    exact ⟨ℓ, hℓ, by rw [b_eq hM]; exact he.symm⟩
  refine ⟨fun q => if hq : q ∈ F I M then Classical.choose (h q hq) else 0, ?_⟩
  intro q hq
  simp only [dif_pos hq]
  exact Classical.choose_spec (h q hq)

theorem assigned_ne_zero (ψ : ℕ → ℕ) (ℓ : ℕ) : assigned I M ψ ℓ ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro q hq
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hq).1).ne_zero

theorem assigned_dvd (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ} (hψ : IsAssignment I M ψ)
    {ℓ : ℕ} (hℓ : ℓ ∈ I) : assigned I M ψ ℓ ∣ M ℓ := by
  classical
  have hpow : ∀ q ∈ (F I M).filter (fun q => ψ q = ℓ), q ^ b I M q ≠ 0 :=
    fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hq).1).ne_zero
  rw [← Nat.factorization_le_iff_dvd (assigned_ne_zero ψ ℓ) (hM ℓ hℓ), Finsupp.le_def]
  intro p
  rw [assigned, Nat.factorization_prod hpow, Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hp : p ∈ (F I M).filter (fun q => ψ q = ℓ)
  · rw [sum_eq_single_of_mem p hp]
    · rw [(Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).factorization_pow,
        Finsupp.single_eq_same]
      have h := (hψ p (mem_filter.1 hp).1).2
      rw [(mem_filter.1 hp).2] at h
      exact h.symm.le
    · intro q hq hne
      rw [(Nat.prime_of_mem_primeFactors (mem_filter.1 hq).1).factorization_pow,
        Finsupp.single_apply, if_neg hne]
  · rw [sum_eq_zero]
    · exact Nat.zero_le _
    · intro q hq
      have hne : q ≠ p := fun h => hp (h ▸ hq)
      rw [(Nat.prime_of_mem_primeFactors (mem_filter.1 hq).1).factorization_pow,
        Finsupp.single_apply, if_neg hne]

theorem prod_assigned (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ} (hψ : IsAssignment I M ψ) :
    ∏ ℓ ∈ I, assigned I M ψ ℓ = L I M := by
  classical
  unfold assigned
  rw [prod_fiberwise_of_maps_to (fun q hq => (hψ q hq).1)]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (L_ne_zero hM)]
  rw [Finsupp.prod, Nat.support_factorization]
  rfl

/-- **(17.4).** `∏_ℓ M ℓ = L · B`. -/
theorem ratio_identity (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ} (hψ : IsAssignment I M ψ) :
    ∏ ℓ ∈ I, M ℓ = L I M * B I M ψ := by
  have h : ∀ ℓ ∈ I, M ℓ = assigned I M ψ ℓ * R I M ψ ℓ :=
    fun ℓ hℓ => (Nat.mul_div_cancel' (assigned_dvd hM hψ hℓ)).symm
  rw [prod_congr rfl h, prod_mul_distrib, prod_assigned hM hψ]
  rfl

theorem B_ne_zero (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ} (hψ : IsAssignment I M ψ) :
    B I M ψ ≠ 0 := by
  intro h
  have := ratio_identity hM hψ
  rw [h, mul_zero] at this
  exact prod_ne_zero_iff.mpr hM this

/-- **(17.5).** Untouched rows divide `B`. -/
theorem untouched_prod_dvd {ψ : ℕ → ℕ} {U : Finset ℕ} (hUI : U ⊆ I)
    (hU : ∀ ℓ ∈ U, ∀ q ∈ F I M, ψ q ≠ ℓ) : ∏ ℓ ∈ U, M ℓ ∣ B I M ψ := by
  classical
  have hR : ∀ ℓ ∈ U, R I M ψ ℓ = M ℓ := by
    intro ℓ hℓ
    have he : (F I M).filter (fun q => ψ q = ℓ) = ∅ :=
      filter_eq_empty_iff.mpr (fun q hq => hU ℓ hℓ q hq)
    simp [R, assigned, he]
  rw [← prod_congr rfl hR]
  exact prod_dvd_prod_of_subset U I _ hUI

/-- A touched deficient row consumes a distinct tied prime. -/
theorem card_touched_le_tied (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ}
    (hψ : IsAssignment I M ψ) :
    #(I.filter (fun ℓ => rowDef I M ℓ ∧ ∃ q ∈ F I M, ψ q = ℓ)) ≤
      #((F I M).filter (tied I M)) := by
  classical
  set T := I.filter (fun ℓ => rowDef I M ℓ ∧ ∃ q ∈ F I M, ψ q = ℓ)
  have h : ∀ ℓ ∈ T, ∃ q ∈ F I M, ψ q = ℓ := fun ℓ hℓ => (mem_filter.1 hℓ).2.2
  let g : ℕ → ℕ := fun ℓ => if hℓ : ℓ ∈ T then Classical.choose (h ℓ hℓ) else 0
  have hg : ∀ ℓ ∈ T, g ℓ ∈ F I M ∧ ψ (g ℓ) = ℓ := by
    intro ℓ hℓ
    have hgℓ : g ℓ = Classical.choose (h ℓ hℓ) := dif_pos hℓ
    rw [hgℓ]
    exact Classical.choose_spec (h ℓ hℓ)
  apply card_le_card_of_injOn g
  · intro ℓ hℓ
    have hℓ' := mem_coe.1 hℓ
    obtain ⟨hq, hψq⟩ := hg ℓ hℓ'
    obtain ⟨hℓI, hdef, -⟩ := mem_filter.1 hℓ'
    refine mem_coe.2 (mem_filter.2 ⟨hq, hq, ?_⟩)
    rintro ⟨ℓ'', hℓ'', hpriv⟩
    have hmax := (hψ (g ℓ) hq).2
    rw [hψq] at hmax
    by_cases he : ℓ'' = ℓ
    · subst he
      exact hdef ⟨g ℓ'', hpriv⟩
    · have := hpriv.2.2 ℓ hℓI (Ne.symm he)
      omega
  · intro ℓ hℓ ℓ' hℓ' he
    have h1 := (hg ℓ (mem_coe.1 hℓ)).2
    have h2 := (hg ℓ' (mem_coe.1 hℓ')).2
    rw [← h1, ← h2, he]

/-- **(17.6), generic.** If every row is at least `A`, then `A^(z - t) ≤ B`. -/
theorem pow_le_B (hM : ∀ ℓ ∈ I, M ℓ ≠ 0) {ψ : ℕ → ℕ} (hψ : IsAssignment I M ψ)
    {A : ℕ} (hA0 : 0 < A) (hA : ∀ ℓ ∈ I, A ≤ M ℓ) :
    A ^ (#(I.filter (rowDef I M)) - #((F I M).filter (tied I M))) ≤ B I M ψ := by
  classical
  set U := I.filter (fun ℓ => rowDef I M ℓ ∧ ¬ ∃ q ∈ F I M, ψ q = ℓ)
  set T := I.filter (fun ℓ => rowDef I M ℓ ∧ ∃ q ∈ F I M, ψ q = ℓ)
  have hsplit : #U + #T = #(I.filter (rowDef I M)) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext ℓ
      simp only [U, T, mem_union, mem_filter]
      tauto
    · rw [disjoint_left]
      intro ℓ h1 h2
      exact (mem_filter.1 h1).2.2 (mem_filter.1 h2).2.2
  have hT : #T ≤ #((F I M).filter (tied I M)) := by
    convert card_touched_le_tied hM hψ using 2
  have hUI : U ⊆ I := filter_subset _ _
  have hdvd := untouched_prod_dvd (M := M) (ψ := ψ) hUI (by
    intro ℓ hℓ q hq he
    exact (mem_filter.1 hℓ).2.2 ⟨q, hq, he⟩)
  have hB := Nat.pos_of_ne_zero (B_ne_zero hM hψ)
  calc A ^ (#(I.filter (rowDef I M)) - #((F I M).filter (tied I M)))
      ≤ A ^ #U := Nat.pow_le_pow_right hA0 (by omega)
    _ = ∏ _ℓ ∈ U, A := (prod_const _).symm
    _ ≤ ∏ ℓ ∈ U, M ℓ := prod_le_prod (fun ℓ hℓ => hA ℓ (hUI hℓ))
    _ ≤ B I M ψ := Nat.le_of_dvd hB hdvd

/-- Number of private certificates of the row `ℓ`. -/
noncomputable def c (ℓ : ℕ) : ℕ := by
  classical
  exact #((F I M).filter (privAt I M ℓ))

/-- **(17.1), generic.** `z + #F = #I + e + t`, with `e = Σ (c ℓ - 1)`. -/
theorem count_identity :
    #(I.filter (rowDef I M)) + #(F I M) =
      #I + (∑ ℓ ∈ I, (c (I := I) (M := M) ℓ - 1)) + #((F I M).filter (tied I M)) := by
  classical
  -- private primes are counted once, by their owner
  set Pv := (F I M).filter (fun q => ∃ ℓ ∈ I, privAt I M ℓ q)
  have hF : #Pv + #((F I M).filter (tied I M)) = #(F I M) := by
    rw [← card_filter_add_card_filter_not (s := F I M) (fun q => ∃ ℓ ∈ I, privAt I M ℓ q)]
    congr 2
    ext q
    simp only [mem_filter, tied]
    tauto
  have hunion : Pv = I.biUnion (fun ℓ => (F I M).filter (privAt I M ℓ)) := by
    ext q
    simp only [Pv, mem_filter, mem_biUnion]
    constructor
    · rintro ⟨hq, ℓ, hℓ, hp⟩; exact ⟨ℓ, hℓ, hq, hp⟩
    · rintro ⟨ℓ, hℓ, hq, hp⟩; exact ⟨hq, ℓ, hℓ, hp⟩
  have hdisj : (I : Set ℕ).PairwiseDisjoint (fun ℓ => (F I M).filter (privAt I M ℓ)) := by
    intro ℓ hℓ ℓ' hℓ' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro q h1 h2
    have p1 := (mem_filter.1 h1).2
    have p2 := (mem_filter.1 h2).2
    have := p1.2.2 ℓ' hℓ' (Ne.symm hne)
    rw [p2.2.1] at this
    exact lt_irrefl _ this
  have hsum : #Pv = ∑ ℓ ∈ I, c (I := I) (M := M) ℓ := by
    rw [hunion, card_biUnion hdisj]
    rfl
  have hrow : ∀ ℓ, rowDef I M ℓ ↔ c (I := I) (M := M) ℓ = 0 := by
    intro ℓ
    simp only [rowDef, c, card_eq_zero, filter_eq_empty_iff]
    constructor
    · intro h q _ hp; exact h ⟨q, hp⟩
    · rintro h ⟨q, hp⟩; exact h hp.1 hp
  have hcount : ∑ ℓ ∈ I, c (I := I) (M := M) ℓ =
      #(I.filter (fun ℓ => ¬ rowDef I M ℓ)) + ∑ ℓ ∈ I, (c (I := I) (M := M) ℓ - 1) := by
    rw [card_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro ℓ _
    by_cases h : rowDef I M ℓ
    · rw [if_neg (not_not.2 h), (hrow ℓ).1 h]
    · rw [if_pos h]
      have := (hrow ℓ).not.1 h
      omega
  have hsplit := card_filter_add_card_filter_not (s := I) (rowDef I M)
  omega

end Ratio

/-! ## Specialization to Mur II -/

open Finset Ratio
open scoped Classical

/-- The complements `M ℓ = N - ℓ`. -/
def compl (N : ℕ) : ℕ → ℕ := fun ℓ => N - ℓ

variable {P N : ℕ}

theorem compl_ne_zero (hb : BadFamily P N) : ∀ ℓ ∈ idxSet P, compl N ℓ ≠ 0 := by
  intro ℓ hℓ
  have := (mem_idxSet.1 hℓ).2.2
  have := hb.1
  simp only [compl]
  omega

theorem mem_F_iff (hb : BadFamily P N) {q : ℕ} :
    q ∈ F (idxSet P) (compl N) ↔ Nat.Prime q ∧ ∃ ℓ ∈ idxSet P, q ∣ N - ℓ := by
  have hM := compl_ne_zero hb
  simp only [F, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hd, -⟩
    refine ⟨hq, ?_⟩
    have hpos := hq.factorization_pos_of_dvd (L_ne_zero hM) hd
    change 0 < b (idxSet P) (compl N) q at hpos
    rw [b_eq hM, Finset.lt_sup_iff] at hpos
    obtain ⟨ℓ, hℓ, hpos⟩ := hpos
    exact ⟨ℓ, hℓ, Nat.dvd_of_factorization_pos hpos.ne'⟩
  · rintro ⟨hq, ℓ, hℓ, hd⟩
    exact ⟨hq, dvd_trans hd (Finset.dvd_lcm hℓ), L_ne_zero hM⟩

theorem F_subset_sup (hb : BadFamily P N) : F (idxSet P) (compl N) ⊆ supSet P := by
  intro q hq
  obtain ⟨hp, ℓ, hℓ, hd⟩ := (mem_F_iff hb).1 hq
  have hℓI := mem_idxSet.1 hℓ
  have hlt := (hb.2.2 ℓ hℓI).2 q hp hd
  have ho := compl_odd hb hℓI
  have h3 : 3 ≤ q := by
    rcases hp.eq_two_or_odd with h | h
    · subst h; omega
    · have := hp.two_le; omega
  exact mem_filter.2 ⟨mem_range.2 hlt, hp, h3⟩

theorem absent_eq (hb : BadFamily P N) :
    absentSet P N = supSet P \ F (idxSet P) (compl N) := by
  ext q
  simp only [absentSet, mem_filter, mem_sdiff, mem_F_iff hb, not_and, not_exists]
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun _ ℓ hℓ hd => h ℓ hℓ hd⟩
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun ℓ hℓ hd => h (mem_filter.1 hS).2.1 ℓ hℓ hd⟩

/-- The manuscript's deficient rows (no private certificate) are `Deficient`. -/
theorem deficient_iff_rowDef (hb : BadFamily P N) {ℓ : ℕ} (hℓ : ℓ ∈ idxSet P) :
    Deficient P N ℓ ↔ rowDef (idxSet P) (compl N) ℓ := by
  have hM := compl_ne_zero hb
  have hℓI := mem_idxSet.1 hℓ
  simp only [Deficient, rowDef, hℓI, true_and]
  apply not_congr
  constructor
  · rintro ⟨r, a, hr, ha, hd, hpriv⟩
    have hv : a ≤ (compl N ℓ).factorization r :=
      (hr.pow_dvd_iff_le_factorization (hM ℓ hℓ)).1 hd
    have hlt : ∀ j ∈ idxSet P, j ≠ ℓ → (compl N j).factorization r < a := by
      intro j hj hne
      by_contra hge
      push Not at hge
      exact hpriv j (mem_idxSet.1 hj) hne
        ((hr.pow_dvd_iff_le_factorization (hM j hj)).2 hge)
    have hbeq : b (idxSet P) (compl N) r = (compl N ℓ).factorization r := by
      apply le_antisymm
      · rw [b_eq hM]
        apply Finset.sup_le
        intro j hj
        by_cases hne : j = ℓ
        · rw [hne]
        · exact le_of_lt (lt_of_lt_of_le (hlt j hj hne) hv)
      · exact le_b hM hℓ
    refine ⟨r, (mem_F_iff hb).2 ⟨hr, ℓ, hℓ, ?_⟩, hbeq.symm, ?_⟩
    · exact dvd_trans (dvd_pow_self r ha.ne') hd
    · intro j hj hne
      rw [hbeq]
      exact lt_of_lt_of_le (hlt j hj hne) hv
  · rintro ⟨q, hqF, hmax, hlt⟩
    have hp := ((mem_F_iff hb).1 hqF).1
    have hpos : 0 < b (idxSet P) (compl N) q := by
      have := hp.factorization_pos_of_dvd (L_ne_zero hM) (Nat.dvd_of_mem_primeFactors hqF)
      exact this
    refine ⟨q, b (idxSet P) (compl N) q, hp, hpos, ?_, ?_⟩
    · exact (hp.pow_dvd_iff_le_factorization (hM ℓ hℓ)).2 hmax.ge
    · intro j hj hne hd
      have := (hp.pow_dvd_iff_le_factorization (hM j (mem_idxSet.2 hj))).1 hd
      have := hlt j (mem_idxSet.2 hj) hne
      omega

/-- **(17.1).** `z = 1 + a + t + e`. -/
theorem deficit_identity (hP : Nat.Prime P) (h3 : 3 ≤ P) (hb : BadFamily P N) :
    #((idxSet P).filter (rowDef (idxSet P) (compl N))) =
      1 + #(absentSet P N) + #((F (idxSet P) (compl N)).filter (tied (idxSet P) (compl N)))
        + ∑ ℓ ∈ idxSet P, (c (I := idxSet P) (M := compl N) ℓ - 1) := by
  have h1 := count_identity (I := idxSet P) (M := compl N)
  have h2 := card_idxSet hP h3
  have hsub := F_subset_sup hb
  have h3' : #(absentSet P N) + #(F (idxSet P) (compl N)) = #(supSet P) := by
    rw [absent_eq hb, card_sdiff_of_subset hsub]
    have := card_le_card hsub
    omega
  omega

/-- **(17.6).** `(N - P)^(1 + a + e) ≤ B`, where `L · B = ∏ (N - ℓ)`. -/
theorem factor_one_budget (hP : Nat.Prime P) (h3 : 3 ≤ P) (hb : BadFamily P N)
    {ψ : ℕ → ℕ} (hψ : IsAssignment (idxSet P) (compl N) ψ) :
    (N - P) ^ (1 + #(absentSet P N)
        + ∑ ℓ ∈ idxSet P, (c (I := idxSet P) (M := compl N) ℓ - 1))
      ≤ B (idxSet P) (compl N) ψ ∧
    ∏ ℓ ∈ idxSet P, (N - ℓ) = L (idxSet P) (compl N) * B (idxSet P) (compl N) ψ := by
  have hM := compl_ne_zero hb
  refine ⟨?_, ratio_identity hM hψ⟩
  have hA : ∀ ℓ ∈ idxSet P, N - P ≤ compl N ℓ := fun ℓ hℓ =>
    Nat.sub_le_sub_left (mem_idxSet.1 hℓ).2.2 N
  have h := pow_le_B hM hψ (by have := hb.1; omega) hA
  have hid := deficit_identity hP h3 hb
  have he : #((idxSet P).filter (rowDef (idxSet P) (compl N))) -
      #((F (idxSet P) (compl N)).filter (tied (idxSet P) (compl N))) =
      1 + #(absentSet P N) + ∑ ℓ ∈ idxSet P, (c (I := idxSet P) (M := compl N) ℓ - 1) := by
    omega
  rwa [he] at h

#print axioms ratio_identity
#print axioms deficit_identity
#print axioms factor_one_budget
#print axioms deficient_iff_rowDef

end WilliamsonMurII
