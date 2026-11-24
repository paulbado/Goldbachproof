# Goldbach — Williamson certificate reduction (Lean 4 + Mathlib)

[![Build & verify](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml/badge.svg)](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml)

Formal (Lean 4 / Mathlib) and computational material for a certificate-based
attack on first failing endpoints of Goldbach-type decompositions.

## Status — read this first

This repository does **not** prove the Goldbach conjecture. The current
strategy is **Mur II (arithmetic route)**, in `Goldbach/WilliamsonMurII.lean`.

| Item | Status |
|---|---|
| `dvd_difference` | ✅ proved in Lean |
| `shared_power` (no private prime power ⇒ every prime power is shared) | ✅ proved in Lean |
| `deficient_certificate` | ✅ proved in Lean |
| `joint_certificate` (two deficient lines, common `N`) | ✅ proved in Lean |
| `combine_walls` (Wall I + Wall II ⇒ no bad family) | ✅ proved in Lean (logical assembly only) |
| `WallIIAt P₀` — exclude bad families with multiple deficits | ❓ **open** — stated as a `Prop` |
| `WallIAt P₀` — complementary branch | ❓ **open** — must be connected to the old Wall I via private-owner counting |
| `PreviousRankConditions` derived from a first failure | ⏳ proved in the manuscript, not formalized |

All proved theorems depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); CI rejects `sorry`, `axiom`
declarations and any dependency on `sorryAx`.

The earlier route (Williamson certificate cover, finite check up to `P ≤ 151`)
is kept in `archive/` for reference and is not built.

## Layout

```
Goldbach/WilliamsonMurII.lean  current strategy (Mur II)
archive/                       previous route + its Python check (not built)
.github/workflows/lean.yml     CI: build + no-sorry + axiom check
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
