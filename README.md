# Goldbach — Williamson certificate reduction (Lean 4 + Mathlib)

[![Build & verify](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml/badge.svg)](https://github.com/idrissbado/Golbach-Conjecture/actions/workflows/lean.yml)

Formal (Lean 4 / Mathlib) and computational material for a certificate-based
attack on first failing endpoints of Goldbach-type decompositions.

## Status — read this first

This repository does **not** prove the Goldbach conjecture.

| Item | Status |
|---|---|
| `exists_nonprivate` (pigeonhole step) | ✅ proved in Lean |
| `dvd_index_difference` | ✅ proved in Lean |
| `polynomial_of_linear` (linear cover ⇒ polynomial cover) | ✅ proved in Lean |
| `excludes_line` | ✅ proved in Lean |
| `UniformCertificateExclusion` | ❓ **open** — stated as a `Prop`, not proved |
| `LinearCertificateExclusion` | ❓ **open** — supported only by finite experiments |
| Finite cover for primes `5 ≤ P ≤ 151`, `C = 13` | ✅ computed: 229153 admissible lines, 0 uncovered (Lean `#eval` and Python agree) |
| Completeness of the divisor enumeration vs `DifferenceCertificate` | ⏳ not yet formalized |

All proved theorems depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); CI rejects `sorry` and new `axiom`s.

## Layout

```
Goldbach/WilliamsonWall.lean   definitions, lemmas, executable checker
scripts/CheckRangeStats.lean   Lean replay of the finite computation
scripts/verify_williamson.py   independent Python check
.github/workflows/lean.yml     CI: build + no-sorry + both checks
```

## Build locally

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
lake exe cache get      # download prebuilt Mathlib
lake build
lake env lean scripts/CheckRangeStats.lean   # expect (229153, 0)
python3 scripts/verify_williamson.py
```

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.

## Author

Idriss Olivier Bado — ORCID [0009-0001-2097-545X](https://orcid.org/0009-0001-2097-545X)
