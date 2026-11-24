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

## Layout

```
Goldbach/WilliamsonMurII.lean            Mur II core
Goldbach/WilliamsonMurIIExtensions.lean  arithmetic extensions
Goldbach/WilliamsonMurIIKLines.lean      simultaneous k-line bound
Goldbach/WilliamsonMurIIBridge.lean      exact bridge to Goldbach
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
