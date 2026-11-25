import Goldbach.WilliamsonMurIIBridge
import Goldbach.WilliamsonMurIIClosure

/-! # Small ranks: finite height bound, sharper bridge, certified eliminations

* `badFamily_height_le_budget` — every bad family of prime rank `P ≥ 3` satisfies
  `N ≤ P + deficitBudget P 1` (universal finite height bound).
* `exists_deficient_dvd_budget` — more precisely some deficient row `ℓ` has
  `N - ℓ ∣ deficitBudget P 1`.
* `goldbach_of_walls_prev` — the reduction of `goldbach_of_walls` with the small-rank
  hypothesis weakened to configurations satisfying `PreviousRankConditions` and the
  finite height bound.
* A certificate checker (`checkCert`, `candidates`, `rank_clear`): a finite, kernel-checked
  computation eliminating every bad family of a given small rank under the first-failure
  conditions. Completeness of the enumeration is proved, not assumed.

Everything here is proved from the standard axioms; the computations are checked by the
kernel (`decide +kernel`); no native code evaluation is used. -/

namespace WilliamsonMurII
open Finset

/-! ## Task 1: universal finite height bound -/

/-- Some deficient row has its complement dividing `deficitBudget P 1`. -/
theorem exists_deficient_dvd_budget {P N : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) : ∃ ℓ, Deficient P N ℓ ∧ N - ℓ ∣ deficitBudget P 1 := by
  classical
  have h := one_add_absent_le_deficient hP h3 hb
  have hne : (defSet P N).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨ℓ, hℓ⟩ := hne
  have hdef : Deficient P N ℓ := by
    unfold defSet at hℓ
    exact (Finset.mem_filter.1 hℓ).2
  have hD : ∀ i ∈ ({ℓ} : Finset ℕ), Deficient P N i := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hdef
  have hdiv := deficit_product_dvd_budget {ℓ} hb hD
  rw [Finset.prod_singleton, Finset.card_singleton] at hdiv
  exact ⟨ℓ, hdef, hdiv⟩

/-- **Universal finite height bound.** A bad family of prime rank `P ≥ 3`
    has `N ≤ P + deficitBudget P 1`. -/
theorem badFamily_height_le_budget {P N : ℕ} (hP : Nat.Prime P) (h3 : 3 ≤ P)
    (hb : BadFamily P N) : N ≤ P + deficitBudget P 1 := by
  classical
  have h := one_add_absent_le_deficient hP h3 hb
  have hne : (defSet P N).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨ℓ, hℓ⟩ := hne
  have hdef : Deficient P N ℓ := by
    unfold defSet at hℓ
    exact (Finset.mem_filter.1 hℓ).2
  have hD : ∀ i ∈ ({ℓ} : Finset ℕ), Deficient P N i := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact hdef
  have hh := deficit_height_bound {ℓ} hb hD
  rw [Finset.card_singleton, pow_one] at hh
  have := hb.1
  omega

/-! ## Task 2: bridge with the small-rank hypothesis restricted to first-failure configurations -/

/-- **Sharper reduction.** As `goldbach_of_walls`, but the finite range only has to exclude
    bad families that satisfy the previous-rank conditions and the finite height bound. -/
theorem goldbach_of_walls_prev (P₀ : ℕ) (hI : WallIAt P₀) (hII : WallIIAt P₀)
    (hsmall : ∀ P p N, Nat.Prime P → 5 ≤ P → P < P₀ →
      PreviousRankConditions p P N → N ≤ P + deficitBudget P 1 → ¬ BadFamily P N) :
    ∀ N, 8 ≤ N → Even N → GoldbachAt N := by
  classical
  intro N hN hNe
  by_contra hg
  set P := Nat.findGreatest Nat.Prime (N - 1) with hPdef
  have h7 : 7 ≤ P := Nat.le_findGreatest (by omega) (by norm_num)
  have hPp : Nat.Prime P := Nat.findGreatest_spec (m := 7) (by omega) (by norm_num)
  have hPN : P < N := by have := Nat.findGreatest_le (P := Nat.Prime) (N - 1); omega
  have hmax : ∀ q, Nat.Prime q → q < N → q ≤ P :=
    fun q hq hqN => Nat.le_findGreatest (by omega) hq
  have hbN := badFamily_of_not_goldbach (by omega) hNe hPp hPN hmax hg
  have hex : ∃ R, Nat.Prime R ∧ 5 ≤ R ∧ ∃ M, BadFamily R M :=
    ⟨P, hPp, by omega, N, hbN⟩
  set R := Nat.find hex
  obtain ⟨hRp, hR5, M, hbM⟩ := Nat.find_spec hex
  have hff : FirstFailure R := by
    refine ⟨hRp, ⟨M, hbM⟩, fun q hq hq3 hqR M' hM' hb' => ?_⟩
    rcases Nat.lt_or_ge q 5 with h | h
    · have : q = 3 ∨ q = 4 := by omega
      rcases this with rfl | rfl
      · exact no_badFamily_three hM' hb'
      · exact absurd hq (by norm_num)
    · exact Nat.find_min hex hqR ⟨hq, h, M', hb'⟩
  set p := Nat.findGreatest Nat.Prime (R - 1)
  have hp3 : 3 ≤ p := Nat.le_findGreatest (by omega) Nat.prime_three
  have hpp : Nat.Prime p := Nat.findGreatest_spec (m := 3) (by omega) Nat.prime_three
  have hpR : p < R := by have := Nat.findGreatest_le (P := Nat.Prime) (R - 1); omega
  have hprev : PreviousPrime p R :=
    ⟨⟨hpp, hp3, le_of_lt hpR⟩, hpR, fun q hq hqR => Nat.le_findGreatest (by omega) hq⟩
  have hprc := first_failure_previous_conditions hff hprev hbM
  rcases Nat.lt_or_ge R P₀ with hlt | hge
  · exact hsmall R p M hRp hR5 hlt hprc
      (badFamily_height_le_budget hRp (by omega) hbM) hbM
  · exact combine_walls P₀ P₀ hI hII R p M (by simpa using hge) hR5 hRp hprc hbM

/-! ## Task 3: certified eliminations of small ranks -/

/-! ### A kernel-friendly primality test -/

/-- Trial division by `k, k+1, …` until `k² > n`, with fuel. -/
def trialOK (n k : ℕ) : ℕ → Bool
  | 0 => decide (n < k * k)
  | f + 1 => if n < k * k then true else if n % k = 0 then false else trialOK n (k + 1) f

/-- Boolean primality test. -/
def primeB (n : ℕ) : Bool := decide (2 ≤ n) && trialOK n 2 n

theorem prime_of_no_small_div {n k : ℕ} (hn : 2 ≤ n) (hk : n < k * k)
    (h : ∀ m, 2 ≤ m → m < k → ¬ m ∣ n) : Nat.Prime n := by
  by_contra hnp
  have hm := Nat.minFac_prime (show n ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hlt : n.minFac < k := by
    by_contra hge
    push Not at hge
    have : k * k ≤ n.minFac * n.minFac := Nat.mul_le_mul hge hge
    rw [sq] at hsq
    omega
  exact h _ hm.two_le hlt (Nat.minFac_dvd n)

theorem trialOK_sound {n : ℕ} (hn : 2 ≤ n) :
    ∀ f k, trialOK n k f = true → (∀ m, 2 ≤ m → m < k → ¬ m ∣ n) → Nat.Prime n := by
  intro f
  induction f with
  | zero =>
    intro k hk h
    simp only [trialOK, decide_eq_true_eq] at hk
    exact prime_of_no_small_div hn hk h
  | succ f ih =>
    intro k hk h
    simp only [trialOK] at hk
    by_cases h1 : n < k * k
    · exact prime_of_no_small_div hn h1 h
    · rw [if_neg h1] at hk
      by_cases h2 : n % k = 0
      · rw [if_pos h2] at hk; exact absurd hk (by simp)
      · rw [if_neg h2] at hk
        apply ih (k + 1) hk
        intro m hm2 hmk hmd
        rcases Nat.lt_or_ge m k with hlt | hge
        · exact h m hm2 hlt hmd
        · have : m = k := by omega
          subst this
          exact h2 (Nat.mod_eq_zero_of_dvd hmd)

theorem trialOK_complete {n : ℕ} (hp : Nat.Prime n) :
    ∀ f k, 2 ≤ k → n < k + f → trialOK n k f = true := by
  intro f
  induction f with
  | zero =>
    intro k hk hnk
    simp only [trialOK, decide_eq_true_eq]
    have : k ≤ k * k := Nat.le_mul_self k
    omega
  | succ f ih =>
    intro k hk hnk
    simp only [trialOK]
    by_cases h1 : n < k * k
    · rw [if_pos h1]
    · rw [if_neg h1]
      have h2 : ¬ n % k = 0 := by
        intro h0
        have hkd : k ∣ n := Nat.dvd_of_mod_eq_zero h0
        rcases hp.eq_one_or_self_of_dvd k hkd with h | h
        · omega
        · have : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
          omega
      rw [if_neg h2]
      exact ih (k + 1) (by omega) (by omega)

theorem primeB_iff {n : ℕ} : primeB n = true ↔ Nat.Prime n := by
  unfold primeB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, ht⟩
    exact trialOK_sound h2 n 2 ht (fun m hm hmk => by omega)
  · intro hp
    exact ⟨hp.two_le, trialOK_complete hp n 2 le_rfl (by have := hp.two_le; omega)⟩

/-! ### Index lists -/

/-- The indices `I = ℙ ∩ [3, P]`, as a list. -/
def idxList (P : ℕ) : List ℕ := (List.range (P + 1)).filter (fun i => decide (3 ≤ i) && primeB i)

theorem mem_idxList {P i : ℕ} : i ∈ idxList P ↔ Index P i := by
  simp only [idxList, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    primeB_iff, Index]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h1⟩

/-! ### Divisors from a factorisation -/

/-- `∏ r^e` over a list of pairs `(r, e)`. -/
def prodF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: fs => x.1 ^ x.2 * prodF fs

/-- All products `∏ r^k` with `k ≤ e`. -/
def divsF : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | x :: fs => (List.range (x.2 + 1)).flatMap (fun k => (divsF fs).map (fun d => x.1 ^ k * d))

/-- **Completeness of the divisor enumeration.** Every divisor of `prodF fs` is listed,
    provided the bases are prime. -/
theorem mem_divsF : ∀ (fs : List (ℕ × ℕ)), (∀ x ∈ fs, Nat.Prime x.1) →
    ∀ d, d ∣ prodF fs → d ∈ divsF fs := by
  intro fs
  induction fs with
  | nil =>
    intro _ d hd
    simp only [prodF, Nat.dvd_one] at hd
    simp [divsF, hd]
  | cons x fs ih =>
    intro hfs d hd
    simp only [prodF] at hd
    obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 hd
    have hx : Nat.Prime x.1 := hfs x (List.mem_cons_self ..)
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hx).1 h1
    have hd2 := ih (fun y hy => hfs y (List.mem_cons_of_mem _ hy)) d2 h2
    simp only [divsF, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨k, by omega, d2, hd2, rfl⟩

/-! ### Candidates and certificates -/

/-- Boolean form of the conditions on a candidate height `N` at rank `P` with previous
    prime `p`: `P < N`, `N` even, and `PreviousRankConditions`. -/
def prcB (P p N : ℕ) : Bool :=
  decide (P < N) && N % 2 == 0 && decide (3 * p + 3 ≤ N) &&
    (idxList p).any (fun j => N % p == j % p)

/-- Candidate heights: `N = ℓ + d` with `ℓ ∈ I` and `d` a divisor of `prodF fs`. -/
def candidates (P p : ℕ) (fs : List (ℕ × ℕ)) : List ℕ :=
  (idxList P).flatMap (fun ℓ => ((divsF fs).map (fun d => ℓ + d)).filter (prcB P p))

/-- A witness `(i, r)` kills `N`: `i ∈ I`, `r` prime, `P ≤ r`, `r ∣ N - i`. -/
def killB (P N : ℕ) (w : ℕ × ℕ) : Bool :=
  primeB w.1 && decide (3 ≤ w.1) && decide (w.1 ≤ P) &&
    primeB w.2 && decide (P ≤ w.2) && (N - w.1) % w.2 == 0

/-- Check a list of candidates against a list of witnesses, in order. -/
def checkCert (P : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | N :: Ns, w :: ws => killB P N w && checkCert P Ns ws

theorem killB_sound {P N : ℕ} {w : ℕ × ℕ} (h : killB P N w = true) : ¬ BadFamily P N := by
  simp only [killB, Bool.and_eq_true, decide_eq_true_eq, primeB_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hi, hi3⟩, hiP⟩, hr⟩, hPr⟩, hmod⟩ := h
  intro hb
  have hlt := (hb.2.2 w.1 ⟨hi, hi3, hiP⟩).2 w.2 hr (Nat.dvd_of_mod_eq_zero hmod)
  omega

theorem checkCert_sound {P : ℕ} : ∀ (Ns : List ℕ) (ws : List (ℕ × ℕ)),
    checkCert P Ns ws = true → ∀ N ∈ Ns, ¬ BadFamily P N := by
  intro Ns
  induction Ns with
  | nil => intro _ _ N hN; simp at hN
  | cons M Ns ih =>
    intro ws h N hN
    cases ws with
    | nil => simp [checkCert] at h
    | cons w ws =>
      simp only [checkCert, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hN with rfl | hN
      · exact killB_sound h.1
      · exact ih ws h.2 N hN

/-- Boolean check that `p` is the prime preceding `P`. -/
def prevB (P p : ℕ) : Bool :=
  primeB p && decide (3 ≤ p) && decide (p < P) &&
    (List.range P).all (fun q => !primeB q || decide (q ≤ p))

theorem prevB_sound {P p : ℕ} (h : prevB P p = true) : PreviousPrime p P := by
  simp only [prevB, Bool.and_eq_true, decide_eq_true_eq, primeB_iff, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hp, hp3⟩, hpP⟩, hall⟩ := h
  refine ⟨⟨hp, hp3, by omega⟩, hpP, fun q hq hqP => ?_⟩
  rcases hall q hqP with h | h
  · have := primeB_iff.2 hq; simp_all
  · simpa using h

theorem previousPrime_unique {p p' P : ℕ} (h : PreviousPrime p P) (h' : PreviousPrime p' P) :
    p = p' :=
  le_antisymm (h'.2.2 p h.1.1 h.2.1) (h.2.2 p' h'.1.1 h'.2.1)

/-- **Rank elimination from a certificate.** If `deficitBudget P 1 = 2^a · ∏ r^e` (odd primes
    `r`), and every candidate `N = ℓ + d` (`d ∣ ∏ r^e`) satisfying the first-failure conditions
    is killed by a witness, then no bad family of rank `P` satisfies the previous-rank
    conditions. The enumeration is proved complete (`mem_divsF`, `mem_idxList`). -/
theorem rank_clear {P p a : ℕ} {fs ws : List (ℕ × ℕ)}
    (hP : primeB P = true) (h3 : 3 ≤ P) (hprev : prevB P p = true)
    (hB : deficitBudget P 1 = 2 ^ a * prodF fs)
    (hfs : (fs.all fun x => primeB x.1) = true)
    (hc : checkCert P (candidates P p fs) ws = true) :
    ∀ p' N, PreviousRankConditions p' P N → ¬ BadFamily P N := by
  intro p' N hprc hb
  have hPp := primeB_iff.1 hP
  have hpp : p' = p := previousPrime_unique hprc.1 (prevB_sound hprev)
  subst hpp
  obtain ⟨ℓ, hdef, hdvd⟩ := exists_deficient_dvd_budget hPp h3 hb
  have hℓN : ℓ ≤ N := le_trans hdef.1.2.2 (le_of_lt hb.1)
  have hodd := compl_odd hb hdef.1
  have hcop : Nat.Coprime (N - ℓ) (2 ^ a) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    exact Nat.odd_iff.2 hodd
  rw [hB] at hdvd
  have hd : N - ℓ ∣ prodF fs := hcop.dvd_of_dvd_mul_left hdvd
  have hfs' : ∀ x ∈ fs, Nat.Prime x.1 := by
    intro x hx
    simp only [List.all_eq_true] at hfs
    exact primeB_iff.1 (hfs x hx)
  have hmemd := mem_divsF fs hfs' _ hd
  have hprcB : prcB P p' N = true := by
    obtain ⟨-, h3p, j, hj, hjmod⟩ := hprc
    obtain ⟨k, hk⟩ := hb.2.1
    simp only [prcB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true]
    exact ⟨⟨⟨hb.1, by omega⟩, h3p⟩, j, mem_idxList.2 hj, hjmod⟩
  have hmem : N ∈ candidates P p' fs := by
    simp only [candidates, List.mem_flatMap, List.mem_filter, List.mem_map]
    exact ⟨ℓ, mem_idxList.2 hdef.1, ⟨N - ℓ, hmemd, by omega⟩, hprcB⟩
  exact checkCert_sound _ ws hc N hmem hb

/-- Candidates attached to one row `ℓ`. -/
def candsAt (P p : ℕ) (fs : List (ℕ × ℕ)) (ℓ : ℕ) : List ℕ :=
  ((divsF fs).map (fun d => ℓ + d)).filter (prcB P p)

/-- **Rank elimination, row by row.** Same as `rank_clear`, with the certificate split by
    the deficient row `ℓ`, so that each row can be checked by a separate kernel computation. -/
theorem rank_clear_rows {P p a : ℕ} {fs : List (ℕ × ℕ)} (cert : ℕ → List (ℕ × ℕ))
    (hP : primeB P = true) (h3 : 3 ≤ P) (hprev : prevB P p = true)
    (hB : deficitBudget P 1 = 2 ^ a * prodF fs)
    (hfs : (fs.all fun x => primeB x.1) = true)
    (hc : ∀ ℓ ∈ idxList P, checkCert P (candsAt P p fs ℓ) (cert ℓ) = true) :
    ∀ p' N, PreviousRankConditions p' P N → ¬ BadFamily P N := by
  intro p' N hprc hb
  have hPp := primeB_iff.1 hP
  have hpp : p' = p := previousPrime_unique hprc.1 (prevB_sound hprev)
  subst hpp
  obtain ⟨ℓ, hdef, hdvd⟩ := exists_deficient_dvd_budget hPp h3 hb
  have hodd := compl_odd hb hdef.1
  have hcop : Nat.Coprime (N - ℓ) (2 ^ a) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    exact Nat.odd_iff.2 hodd
  rw [hB] at hdvd
  have hd : N - ℓ ∣ prodF fs := hcop.dvd_of_dvd_mul_left hdvd
  have hfs' : ∀ x ∈ fs, Nat.Prime x.1 := by
    intro x hx
    simp only [List.all_eq_true] at hfs
    exact primeB_iff.1 (hfs x hx)
  have hmemd := mem_divsF fs hfs' _ hd
  have hprcB : prcB P p' N = true := by
    obtain ⟨-, h3p, j, hj, hjmod⟩ := hprc
    obtain ⟨k, hk⟩ := hb.2.1
    simp only [prcB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true]
    exact ⟨⟨⟨hb.1, by omega⟩, h3p⟩, j, mem_idxList.2 hj, hjmod⟩
  have hℓN : ℓ ≤ N := le_trans hdef.1.2.2 (le_of_lt hb.1)
  have hmem : N ∈ candsAt P p' fs ℓ := by
    simp only [candsAt, List.mem_filter, List.mem_map]
    exact ⟨⟨N - ℓ, hmemd, by omega⟩, hprcB⟩
  exact checkCert_sound _ _ (hc ℓ (mem_idxList.2 hdef.1)) N hmem hb

#print axioms badFamily_height_le_budget
#print axioms exists_deficient_dvd_budget
#print axioms goldbach_of_walls_prev
#print axioms primeB_iff
#print axioms mem_divsF
#print axioms rank_clear
#print axioms rank_clear_rows

end WilliamsonMurII
