# Closure status (2026-11-25)

**Neither wall is proved. `goldbach_final` does not exist. Goldbach is not proved.**

| Statement | Status |
|---|---|
| `small_ranks_clear` (ranks 5 ≤ P < 74) | proved in Lean (kernel-checked) |
| `goldbach_of_walls_74 : WallIAt 74 → WallIIAt 74 → …` | proved in Lean (conditional on both walls) |
| `goldbach_usual_of_goldbachAt` (N ≥ 8 odd-prime form ⇒ usual form N ≥ 4) | proved in Lean |
| `WallIAt 74` | **open** |
| `WallIIAt 74` | **open** |
| `goldbach_final` | **not obtained** |

## Wall I

Exact Lean statement:

```lean
def WallIAt (P₀ : ℕ) : Prop :=
  ∀ P p N : ℕ, P₀ ≤ P → 5 ≤ P → Nat.Prime P →
    PreviousRankConditions p P N → BadFamily P N → ¬ MultipleDeficits P N → False
```

Proved in Lean (`Goldbach/WilliamsonWallI.lean`), for a bad family of prime rank `P ≥ 3` with `¬ MultipleDeficits`:

- `wallI_absent_empty`: no prime of `[3, P)` is absent;
- `wallI_every_prime_divides`, `wallI_odd_multiple`: every odd prime `q < P` divides a complement, so `[N − P, N]` contains an odd multiple of `q`;
- `wallI_unique_deficient`: one deficient row `ℓ₀` with `N − ℓ₀ ∣ deficitBudget P 1`; every other row has a private prime power;
- `wallIAt_of_absent`: **Wall I at `P₀` ⟸ every first-failure bad family of rank `P ≥ P₀` misses a prime of `[3, P)`.**

Smallest missing lemma (Wall I): *prime absence for every prime rank `P ≥ 74`*.

- [CC] §16 proves prime absence only for `P ≥ P_I`, with `P_I` effective but not computed (the quadratic-range transition uses
  `⌈exp(36000)⌉`). So the manuscript gives at best `WallIAt P_I`, not `WallIAt 74`.
- The range `74 ≤ P < P_I` cannot be reached by the certified enumeration: its cost grows like `deficitBudget P 1 ≈ e^{P/2}`.
- The obstacle is **analytic with an effectivity gap**, not algebraic.

Why the structural constraints alone give no contradiction: "every odd prime `q < P` divides some `N − ℓ_q`" and "each non-deficient row
has a private prime power" are congruence conditions on `N` modulo pairwise coprime moduli; by the Chinese remainder theorem they are
simultaneously satisfiable for every `P`. The contradiction must come from restricted support (all prime factors `< P`) together with
the size of `N`, which is exactly what the analytic argument uses.

## Wall II

Exact Lean statement: as `WallIAt` with `MultipleDeficits P N` in place of its negation.

- Proved in Lean: `deficit_height_bound` (`(N − P)^{#D} ≤ deficitBudget P #D` for every deficient set `D`), `one_add_absent_le_deficient`
  (`z ≥ 1 + a`), `geomAbs_subset_absent`, `height_of_geomAbs`, the identities (17.1), (17.4), (17.6).
- Written, not formalized, valid only for `P ≥ P_*` (not computed): Theorem W, `N < P^{950}`.
- Open even for large `P`: the residual region `P < N < P^{950}`. In the band `P^{5/3} ≤ N ≤ P^{2−ε}` the missing estimate is Lemma Ω
  (`docs/distribution-profile.md`); no existing theorem provides it pointwise, and the available distribution estimates are weaker than
  the trivial bound. Other bands have no reduction at all.
- The obstacle is **analytic** (a level-of-distribution statement beyond Bombieri–Vinogradov for a fixed large residue), plus the same
  effectivity gap below `P_*`.

### Wall II, joint constraints on the deficient rows (new, 2026-11-25; `Goldbach/WilliamsonWallII.lean`)

Let `i ≠ j` be deficient rows and `B₁ = deficitBudget P 1`.
- Each complement divides `B₁` (`deficient_dvd_budget`), so `lcm(N−i, N−j) ∣ B₁`.
- `gcd(N−i, N−j)` is odd and divides `|i−j|`, so it is `≤ (P−3)/2` (`compl_gcd_le`).
- Hence `(N−P)² ≤ (N−i)(N−j) = gcd·lcm ≤ B₁·(P−3)/2` (`wallII_height_ceiling_sharp`).
  The earlier ceiling was `(N−P)² ≤ deficitBudget P 2 = B₁²`.

For a set `D` of `k` deficient rows, `∏(N−i) ∣ lcm·T` with `T ≤ ((P−3)/2)^{k(k−1)/2}` (`prod_dvd_lcm_mul`), which gives
`deficit_pairwise_height_bound'`:

```lean
(N - P) ^ #D ≤ deficitBudget P 1 * ((P - 3) / 2) ^ (#D * (#D - 1) / 2)
```

and, by `z ≥ 1 + a`, the same for every `k ≤ 1 + #absentSet` (`height_of_absent_count`).

**Is the joint constraint stronger than the individual ones?** Yes for few rows, no for many. Values of `log(N−P)/log P` allowed by
the old k-line budget → by the joint bound:

| P | k=2 | k=3 | k=5 | k=10 | k=20 | k=50 |
|---|---|---|---|---|---|---|
| 199 | 17.8 → 9.3 | 15.0 → 6.8 | 11.1 → 5.3 | 6.7 → 5.7 | 3.9 → 9.1 | 1.7 → 21.6 |
| 1009 | 73.4 → 37.2 | 61.0 → 25.4 | 45.0 → 16.5 | 27.8 → 11.4 | 16.4 → 12.2 | 7.7 → 23.5 |
| 10007 | 542.6 → 271.8 | 452.1 → 181.8 | 334.9 → 110.4 | 207.7 → 58.4 | 123.3 → 35.9 | 59.3 → 33.5 |

The joint bound wins roughly for `k ≲ √P`; the best of the two is the available constraint.

**Region newly excluded (Lean: `wallII_excluded_region`).** No bad family with two deficient rows has
`(N−P)² > B₁·(P−3)/2`. Compared with the previous ceiling `N − P ≤ B₁`, the heights with
`√(B₁(P−3)/2) < N − P ≤ B₁` are now excluded for Wall II. This is an upper height bound (about `e^{P/4}` instead of `e^{P/2}`);
it does **not** prove emptiness below it.

**What the first-failure conditions add.** The previous prime `p` divides a complement `N − j₀` with `j₀ ≤ p`, and `p` is then a private
certificate of row `j₀` (`previous_prime_has_private_owner`), so `j₀` is not deficient and `p ∤ N − i` for every deficient `i`. Since
`2p > P − 3`, `p` is not a factor of `B₁` anyway: the congruence gives no further restriction on the deficient pair. I found no
contradiction from `PreviousRankConditions` combined with the divisor structure.

**What remains for Wall II.** All heights `3p + 3 ≤ N` with `(N−P)^k ≤ min(deficitBudget P k, B₁((P−3)/2)^{k(k−1)/2})` for every `k ≤ z`.
In particular the whole region `N ≤ P + √(B₁(P−3)/2)` with exactly two deficient rows is untouched.

## Remaining proof obligations## Remaining proof obligations

1. `WallIAt 74` — equivalently (by `wallIAt_of_absent`) prime absence for all prime ranks `P ≥ 74` in the one-deficit branch.
2. `WallIIAt 74`.

With both, `goldbach_of_walls_74` and `goldbach_usual_of_goldbachAt` give the usual statement; nothing else is missing in Lean.
