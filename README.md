# Goldbach — Williamson certificate reduction (Lean 4 + Mathlib)

[![Build & verify](https://github.com/paulbado/Goldbachproof/actions/workflows/lean.yml/badge.svg)](https://github.com/paulbado/Goldbachproof/actions/workflows/lean.yml)

Formal (Lean 4 / Mathlib) and computational material for a certificate-based
attack on first failing endpoints of Goldbach-type decompositions.

## Status — read this first

This repository does **not** prove the Goldbach conjecture. Current strategy:
**Mur II (arithmetic route)**.

### What is proved in Lean (no `sorry`, standard axioms only)

| File | Result |
|---|---|
| `WilliamsonMurII` | `shared_power`, `deficient_certificate`, `joint_certificate`, `combine_walls` |
| `WilliamsonMurIIExtensions` | `first_failure_previous_conditions`, `deficient_prime_power_bound` (2r^a ≤ P−3), `previous_prime_has_private_owner`, `private_owner_budget`, `pair_height_bound_odd` |
| `WilliamsonMurIIKLines` | **k-line bound**: for any set D of deficient lines, ∏_{i∈D}(N−i) ∣ `deficitBudget P #D`, hence (N−P)^#D ≤ `deficitBudget P #D`; `wallII_height_ceiling` |
| `WilliamsonMurIIClosure` | link with §17 of *A Closure Chain Toward Williamson's Conjecture*: `one_add_absent_le_deficient` (z ≥ 1 + a, the used half of (17.1)), `geomAbs_subset_absent` ((17.32), a ≥ G(N,P)), `height_of_geomAbs`: for every k ≤ 1 + G(N,P), (N−P)^k ≤ `deficitBudget P k`. The analytic input G(N,P) ≥ 3P/(20 log P) for N > P^{3/2} (Prop. 17.13, (17.47)) is **not** formalized; it enters only as the hypothesis on k. |
| `WilliamsonMurIIRatio` | exact identities of §17: **(17.4)** `ratio_identity` ∏ M_ℓ = L·B for every assignment of maxima; **(17.1)** `deficit_identity` z = 1 + a + t + e; **(17.5)–(17.6)** `factor_one_budget` (N−P)^{1+a+e} ≤ B; `deficient_iff_rowDef` (manuscript's "no private certificate" ↔ `Deficient`) |
| `WilliamsonMurIIBridge` | **exact bridge**: at P = largest prime < N, `BadFamily P N ↔ ¬ Goldbach(N)`; `first_failure_rank_chain`; **`goldbach_of_walls`**: Wall I + Wall II above P₀ + ranks 5 ≤ P < P₀ ⇒ Goldbach for all even N ≥ 8 |
| `WilliamsonSmallRanks` | **`badFamily_height_le_budget`**: every bad family of prime rank P ≥ 3 has N ≤ P + `deficitBudget P 1`; `exists_deficient_dvd_budget`; **`goldbach_of_walls_prev`**: the small-rank hypothesis only needs to exclude configurations with `PreviousRankConditions` and N ≤ P + `deficitBudget P 1`; certificate checker (`primeB_iff`, `mem_divsF`, `checkCert_sound`, `rank_clear_rows`) with proved completeness of the candidate enumeration |
| `WilliamsonWallI` | forced structure of the one-deficit branch (`wallI_absent_empty`, `wallI_odd_multiple`, `wallI_unique_deficient`); reduction `wallIAt_of_absent` (Wall I ⟸ prime absence); `goldbach_usual_of_goldbachAt` (N ≥ 8 ⇒ usual statement for N ≥ 4). **`WallIAt` itself is not proved**; see [`docs/closure-status.md`](docs/closure-status.md) |
| `WilliamsonWallII` | **joint height bound** for any set D of k deficient rows: (N−P)^k ≤ `deficitBudget P 1` · ((P−3)/2)^{k(k−1)/2} (`deficit_pairwise_height_bound'`); `wallII_height_ceiling_sharp`: (N−P)² ≤ `deficitBudget P 1`·(P−3)/2 (previously `deficitBudget P 2` = square of `deficitBudget P 1`); `height_of_absent_count`; `wallII_excluded_region`; exact differences: `deficient_pair_prod_dvd` ((N−i)(N−j) ∣ B₁·gcd(B₁, odd part of \|i−j\|)), `deficient_prod_dvd_exact` (k rows), `deficient_many_prime_factors`. **`WallIIAt` itself is not proved**; `scripts/wall_ii_low_height_pairs.py` shows the deficient-row constraints are satisfiable throughout P^{5/3} ≤ N ≤ P². |
| `WilliamsonDual` | dual form: for 2P ≤ N, `BadFamily P N ↔` no prime r ≥ P has `N mod r` a prime index; `¬ BadFamily P N ↔ ∃ ℓ r m, ℓ + m·r = N` (ℓ ≤ P, r ≥ P primes) |
| `WilliamsonSmoothRows` | below P²: a row has at most one prime factor ≥ P (`large_prime_factor_unique`); #rows with a prime factor ≥ P = Σ_{P≤r≤N} n_N(r) (`card_good_rows_eq_sum`); a bad family has no such row |
| `WilliamsonSmallRanksData` | **`small_ranks_clear`**: no bad family of prime rank 5 ≤ P < 74 satisfies `PreviousRankConditions` (59,773 candidate heights, each killed by a kernel-checked witness; `decide +kernel`, kernel-checked); **`goldbach_of_walls_74`**: `WallIAt 74 → WallIIAt 74 → ∀ N ≥ 8 even, GoldbachAt N` |

`deficitBudget P k = ∏_{r<P prime} r^{E(r)}`, with
`E(r) = Σ_{a≥1, 2r^a ≤ P−3} min(k, ⌊(P−3)/(2r^a)⌋ + 1)`.

**Definition fix.** `BadFamily 3 4` holds (4 − 3 = 1), so the original
`FirstFailure` was unsatisfiable for every P ≥ 5 (proved: `not_firstFailure_unguarded`).
`FirstFailure` now quantifies over heights N ≥ 6.

### Open

| Item | Status |
|---|---|
| `WallIIAt P₀` (≥ 2 deficient lines) | ❓ open |
| `WallIAt P₀` (exactly 1 deficient line) | ❓ open |

By `goldbach_of_walls_74`, proving `WallIAt 74` and `WallIIAt 74` would prove Goldbach for even N ≥ 8; the small ranks below 74
are now discharged **in Lean**. A larger certified threshold P₀ only weakens the walls
required. The walls themselves remain open; they are hypotheses, not axioms.
The k-line bound leaves, for two deficient lines, the window
3p+3 ≤ N ≤ P + √`deficitBudget P 2` ≈ P + e^{P/2}; it becomes polynomial in P
only when the number of deficient lines is a positive proportion of all lines.

### Finite evidence

- **Lean (certified):** ranks 5 ≤ P < 74, see `WilliamsonSmallRanksData` (generated by `scripts/gen_small_rank_certificates.py`).
- **Python (not a Lean proof):** `scripts/check_small_ranks.py`: no bad family at any rank 5 ≤ P ≤ 271
  (65,054,447 candidates, 0 survivors; every candidate killed by a prime q ≤ 12.55 P).

The earlier route (Williamson certificate cover) is kept in `archive/`, not built.

### Analytic write-ups (not formalized in Lean, not independently verified)

| Document | Content | Status |
|---|---|---|
| [`docs/hypothesis-T.md`](docs/hypothesis-T.md) | χ-twisted Prop. 16.3 (Lemma S, Type I/II); joint sieve on (q, ℓ); Selberg level including the √d loss; budget log B ≤ C₀P(1+log K) | **written, self-audited proof**, from published results only (van der Corput, MRSTT Lemma 4.1, Vaaler, Selberg, Brun–Titchmarsh). Audit log at the top. |
| [`docs/theorem-W-dependencies.md`](docs/theorem-W-dependencies.md) | reconstruction of [CC] Th. 15.1 (Lemmas 14.2–14.4, Prop. 14.5, Lemmas 15.2–15.4) and Prop. 17.13 / (17.47); final assembly of **Theorem W: N < P^959 for P ≥ P\*** | **written, self-audited**; no remaining internal dependency on [CC]; P\* effective, not computed (astronomical). **Not independently verified.** |
| [`docs/prop-16-2-chi-top-range.md`](docs/prop-16-2-chi-top-range.md) | **Proposition 16.2χ** (twisted reciprocal-phase sums over primes, d ≤ X^{1/10}, \|Y\| ≤ X², self-contained proof: Vaughan, Kusmin–Landau, van der Corput) and **Theorem B**: Σ_{P/𝒯<q≤P} log q·n_N(q) = o(P) uniformly in N ∈ [P^{5/3}, P^{2−ε}]; Ω ⟺ Ω_𝒯 | written, self-audited proofs; Lean for the algebraic steps |
| [`docs/switched-sieve.md`](docs/switched-sieve.md) | **Theorem S** (unconditional): Σ_{P^θ₀<q≤P} log q·n_N(q) ≤ (8+o(1))P[1/(1+θ₀−K) − 1/(2−K)] by divisor switching and the 2-dimensional Selberg sieve; **Corollary EH** (conditional): Elliott–Halberstam at level θ(K) < 1 (0.99087 at K = 5/3) excludes the band P^{5/3} ≤ N ≤ P^{2−ε}; assessment of Chebotarev / trace-function / automorphic reformulations | written proof, not independently verified; **conditional** exclusion only |
| [`docs/distribution-profile.md`](docs/distribution-profile.md) | **Lemma T** (trivial bound Σ_large ≤ (K−½+o(1))P is exactly the threshold), **Proposition PF** (scale-dependent level λ(θ) ⇒ Σ_large ≤ (2∫dθ/λ + o(1))P; signed one-sided Selberg error suffices), admissible profiles (gain ≥ 0.45–0.65 over the trivial level needed), available profiles (11.6, worse than trivial) | research note; no new distribution estimate; Ω open |
| [`docs/residual-region.md`](docs/residual-region.md) | residual region: injectivity / near-injectivity (Lean), mass bounds R3/R5/R6 with corrected scope, R4 barrier (X ≥ P^{5/3}), **L1 powersmooth rows** (Lean ingredients), **Theorem A**: below P² a family forces 𝓜(N) ≥ K × average, Corollary B (conditional exclusion), Proposition C: exclusion of 5/3 ≤ K < 2 ⟸ dual level of distribution λ > 2/(2K−1) (audited), **Lemma E** (family ⟺ 𝓜 maximal), **R7** log B ≥ (K−1)P, **multiplicative rigidity** (Lean), **Theorem LS** (≤ 7.3·P log²P families with N ≤ P², exceptional set), failed routes, **Lemma Ω**; top range (P/2,P]: parity lemma (Lean), geometric bound (log 2/2)P, necessary condition Σ_{√P<q≤P/2} ≥ (K−0.847)P, why Ω_{1/2} is harder than Ω | research note; **no pointwise exclusion**; the single missing estimate is Lemma Ω |
| [`docs/joint-sieve-SQ.md`](docs/joint-sieve-SQ.md) | initial setup of the joint sieve, source checks | historical note; `hypothesis-T.md` takes precedence |

**What is proved in Lean** (Mathlib v4.36.0, no `sorry`, standard axioms only): exactly the statements in the table
above (`Goldbach/*.lean`), including (17.1), (17.4), (17.6) and a ≥ G. **Nothing** from `docs/` is formalized.

**Not proved:** Wall I, Wall II, the emptiness of the residual region, Williamson, Goldbach. Theorem W
(polynomial height) does **not** close Wall II: the region P < N ≤ P^{K₀} remains.

## Source manuscript and its finite checks (not duplicated here)

The Lean development follows I. O. Bado, *A Closure Chain Toward Williamson's Conjecture* (110 pages, DOI 10.13140/RG.2.2.34840.97281),
referred to as [CC] in `docs/`. Its submission package contains the LaTeX source, thirteen finite verification programs
(`code/run_checks.py`), their JSON reports (`results/`: `check_summary.json`, `wall_ii_budget_checks.json`, `structural_checks.json`,
`prime_power_rigidity_checks.json`, `valuation_extension_checks.json`, `threshold_checks.json`, the three `mur_i_*.json` audits, …) and a
`MANIFEST.sha256`. Those reports check finite identities, constants and examples of the manuscript; they are **not** re-proved or
copied in this repository, and they are not Lean proofs. What this repository adds is listed in the tables above.

## Layout

```
Goldbach/WilliamsonMurII.lean            Mur II core
Goldbach/WilliamsonMurIIExtensions.lean  arithmetic extensions
Goldbach/WilliamsonMurIIKLines.lean      simultaneous k-line bound
Goldbach/WilliamsonMurIIBridge.lean      exact bridge to Goldbach
Goldbach/WilliamsonMurIIClosure.lean     link with manuscript §17 (z ≥ 1+a ≥ 1+G)
Goldbach/WilliamsonMurIIRatio.lean       exact identities (17.1), (17.4), (17.6)
Goldbach/ReciprocalPhase.lean            algebraic steps of Prop. 16.2χ and Theorem B (phase shift, phase difference, sawtooth count, odd class mod 2e)
Goldbach/WilliamsonWallI.lean            one-deficit branch: structure, reduction to prime absence
Goldbach/WilliamsonWallII.lean           joint pairwise-gcd height bound for deficient rows
Goldbach/WilliamsonSmallRanks.lean       finite height bound, sharper bridge, certificate checker
Goldbach/WilliamsonSmallRanksData.lean   generated certificates, small_ranks_clear, goldbach_of_walls_74
Goldbach/WilliamsonResidual.lean         injectivity, near-injectivity, fiber counting, row uniqueness, powersmooth ⇒ lcm, multiplicative rigidity, parity lemma for q > (P−3)/2
docs/joint-sieve-SQ.md                   joint-sieve analysis, sources, sqrt(d) accounting
docs/hypothesis-T.md                     proof of χ-twisted Prop. 16.3, sieve level, Theorem W (N ≤ P^K0)
scripts/check_small_ranks.py             finite check of small ranks (Python)
scripts/gen_small_rank_certificates.py   generator of the Lean certificates
archive/                                 previous route (not built)
```

## Build locally

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
lake exe cache get      # download prebuilt Mathlib
lake build
```

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.

## Author

Idriss Olivier Bado — ORCID [0009-0001-2097-545X](https://orcid.org/0009-0001-2097-545X)
