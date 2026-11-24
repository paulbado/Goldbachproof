# Goldbach — Williamson certificate reduction (Lean 4 + Mathlib)

[![Build & verify](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml/badge.svg)](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml)

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

By `goldbach_of_walls`, proving both with an explicit P₀ is a proof of Goldbach.
The k-line bound leaves, for two deficient lines, the window
3p+3 ≤ N ≤ P + √`deficitBudget P 2` ≈ P + e^{P/2}; it becomes polynomial in P
only when the number of deficient lines is a positive proportion of all lines.

### Finite evidence (Python, not a Lean proof)

`scripts/check_small_ranks.py`: no bad family at any rank 5 ≤ P ≤ 271
(65,054,447 candidates, 0 survivors; every candidate killed by a prime q ≤ 12.55 P).

The earlier route (Williamson certificate cover) is kept in `archive/`, not built.

### Analytic write-ups (not formalized, not refereed)

- [`docs/hypothesis-T.md`](docs/hypothesis-T.md): proof of the χ-twisted Proposition 16.3 (Lemma S on shifted
  reciprocal phases, Type I/II), sieve remainder bound, Selberg level including the √d loss, and
  Theorem W: every restricted-support family with P ≥ P₀ satisfies N ≤ P^{K₀}. Dependencies and points
  to check are listed in §0 and §11 of that file. **Wall II is not closed.**
- [`docs/joint-sieve-SQ.md`](docs/joint-sieve-SQ.md): setup of the joint sieve and source checks.

## Layout

```
Goldbach/WilliamsonMurII.lean            Mur II core
Goldbach/WilliamsonMurIIExtensions.lean  arithmetic extensions
Goldbach/WilliamsonMurIIKLines.lean      simultaneous k-line bound
Goldbach/WilliamsonMurIIBridge.lean      exact bridge to Goldbach
Goldbach/WilliamsonMurIIClosure.lean     link with manuscript §17 (z ≥ 1+a ≥ 1+G)
Goldbach/WilliamsonMurIIRatio.lean       exact identities (17.1), (17.4), (17.6)
docs/joint-sieve-SQ.md                   joint-sieve analysis, sources, sqrt(d) accounting
docs/hypothesis-T.md                     proof of χ-twisted Prop. 16.3, sieve level, Theorem W (N ≤ P^K0)
scripts/check_small_ranks.py             finite check of small ranks
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
