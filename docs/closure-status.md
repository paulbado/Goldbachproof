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

## Remaining proof obligations

1. `WallIAt 74` — equivalently (by `wallIAt_of_absent`) prime absence for all prime ranks `P ≥ 74` in the one-deficit branch.
2. `WallIIAt 74`.

With both, `goldbach_of_walls_74` and `goldbach_usual_of_goldbachAt` give the usual statement; nothing else is missing in Lean.
