# Joint sieve on the incidences (q, ℓ) — analysis note

Status (updated 2026-11-24): **historical analysis note.** Hypothesis T now has a **written,
self-audited proof** in [`hypothesis-T.md`](hypothesis-T.md) (Prop. 16.3χ), **not independently
verified**. The corrected sieve (partition, remainders, level) and Theorem W are in that file;
**in case of discrepancy, `hypothesis-T.md` is authoritative.** The parameters below
(`δ = 1/5`, `P^{4/5} ≤ Q`, Type II via (16.15)) were corrected there. Theorem W remains conditional
on [CC] Th. 15.1 and (17.47). No lock is declared closed; Wall II remains open.

Reference: I. O. Bado, *A Closure Chain Toward Williamson's Conjecture*,
§16–17 (DOI 10.13140/RG.2.2.34840.97281).

## Setting

Restricted-support family, `P^4 < N < P^{14 log log P}` (Th. 17.14), `K := log N / log P`.
For a dyadic scale `Q < q ≤ 2Q`, put `X := P/Q` and

    S_Q(N) = Σ_{Q<q≤2Q, q prime} Σ_{ℓ ≤ P prime, q | N-ℓ} log q.

Since `(n(q)-1)_+ ≤ n(q)`, the exponent-one part of `log B` on that scale is `≤ S_Q`.
Expected size: `S_Q ≈ (log 2)·π(P) ≍ P/log P`.

## Change of variables

`ℓ = N - bq`, `b` odd (N even, ℓ, q odd), `b ∈ I_q = [(N-P)/q, (N-3)/q]`, `|I_q| ≈ X`.
So `S_Q = Σ_q log q · #{b ∈ I_q odd : N - bq prime}`.

Sieve the multiset `{N - bq}` (weights `log q`) by odd primes `p ≤ D`.
For odd squarefree `d ≤ D² < Q` (so `q ∤ d`):

    d | N - bq  ⟺  b ≡ N q̄ (mod d);  with b odd: one class β_{q,d} mod 2d.

Hence `A_d = X_tot/d + R_d`, `X_tot = Σ_q log q (P-3)/(2q) ≍ P`, with `ω(p) = 1` for every odd `p`
(also when `p | N`: the condition becomes `p | b`). Linear sieve, dimension 1.
Small primes `ℓ ≤ D` (removed by the sieve) contribute `≤ π(D)·2K log P = o(P/log P)`.

## Level with trivial remainders = Brun–Titchmarsh

Each `I_q` has only `≈ X` points, so per `q` the remainder is `O(1)` and `|R_d| ≤ Σ_q log q ≍ Q`.
Selberg's condition `Σ_{d≤D²} τ₃(d)|R_d| ≪ P/log P` forces `D² ≈ X/L^c`, giving

    S_Q ≤ (2 + o(1)) X_tot / log D ≍ P / log X,

exactly Brun–Titchmarsh. **Without cancellation over q, the joint sieve gains nothing.**

## Remainders through reciprocal sums

`#{b ∈ [α,β], b ≡ β_{q,d} (2d)} = (β-α)/(2d) + ψ((α-β_{q,d})/2d) - ψ((β-β_{q,d})/2d)`, `α = (N-P)/q`.
Vaaler's polynomial (length `H`) gives an error `≪ Q/H` plus sums

    Σ_q log q · e(h(N-P)/(2dq)) · g_h(q),   g_h(q) = e(-h β_{q,d}/(2d)),

where `g_h` depends only on `q mod d` and `|g_h| = 1` on reduced classes. Expanding `g_h` in Dirichlet
characters mod `d` and using Parseval, `Σ_χ |ĝ_h(χ)| ≤ φ(d)^{1/2}`. Therefore

    |R_d| ≪ Q/H + (log H) · d^{1/2} · max_{χ mod d} |Σ_{Q<q≤2Q} χ(q) log q · e(Y/q)|,   Y = h(N-P)/(2d).

Here `|Y| ≥ N/(4D²) ≥ Q²/64`: the **large-height range of Prop. 16.3**.

## Hypothesis T (statement; written proof: `hypothesis-T.md` §1–§6)

Uniformly for `d ≤ Q^{1/5}`, `χ mod d`, `|Y| ≥ Q²/64`:

    |Σ_{Q<q≤2Q} χ(q) log q · e(Y/q)| ≪ Q · ℰ,
    ℰ = L^5 ( Q^{-1/310} + exp(-c (log Q)^3 / (250 (log 2|Y|)^2)) ).

This is Prop. 16.3 twisted by a character of small modulus. The expected proof follows §16.3–16.6:
Vaughan's identity is compatible with completely multiplicative `χ`. Type I sums split `n ≡ c (d)` into
shifted reciprocal phases `(Y/(md))/(k + c/d)` on intervals of length `Z/d ≥ Z^{1/2}`. Type II sums
lose `χ` after Cauchy–Schwarz up to the coprimality `(n,d) = 1`, which is removed by Möbius over
`e | d`. **Missing point:** checking that the Vinogradov input (16.13) holds for shifted phases
`a/(k+s)` on intervals of length `≥ Z^{1/2}`, with the same constants. It depends only on the
derivatives, but the source [5] has to be checked as stated.

### Sources checked (2026-11-24)

* **(16.13)** = Green–Harper, *Inverse questions for the large sieve*, GAFA 24 (2014),
  Prop. 4.3 (arXiv:1311.6176), via Iwaniec–Kowalski Th. 8.25: for `x > Y^5`,
  `Σ_{Y≤n≤2Y} e(x/n) ≪ Y exp(-c log³Y / log²x)`. Integers `n`, fixed range `[Y,2Y]`,
  no shift.
* **Shifted phases** are covered by Matomäki–Radziwiłł–Shao–Tao–Teräväinen,
  *Singmaster's conjecture in the interior of Pascal's triangle*, Lemma 4.1
  (arXiv:2106.03335): any interval `I ⊂ [X,2X]`, any phase with
  `α^{-r³} F ≤ t^r |f^{(r)}(t)|/r! ≤ α^{r³} F` for `1 ≤ r ≤ 10⌈log F/log X⌉+1`, `F ≥ X⁴`;
  bound `αX exp(-2^{-18} log³X / log²F)`.
  For `f_s(t) = a/(t+s)`, `0 ≤ s < 1`, `t ∈ [X,2X]`:
  `t^r |f_s^{(r)}(t)|/r! = (|a|/(t+s))·(t/(t+s))^r ∈ [F/(3e), F]` with `F = |a|/X`
  (because `(t/(t+s))^r ≥ e^{-r/X}` and `r ≪ K ≪ X`). So **`α = 3e` works for every `r ≥ 1`,
  uniformly in `s`.** (The smallness condition of Lemma 4.1 is to be reread on the
  published version; outside it the bound is trivial anyway.)
* For `Z^{1/4} ≤ F ≤ Z^4` (relevant when `N` is close to `P^4`), Lemma 16.4 (derivatives of
  order 2–6) applies to `f_s` without change: it depends only on `|f^{(k)}|`.

### On the `√d` loss (objection raised in review)

The objection: `|R_d| ≪ √d·Q·ℰ` and `√d` can reach `Q^{1/10}`, so `Q^{1/10}ℰ` need not
tend to 0. **That is not the constraint actually used.** The sieve only involves
`d ≤ D²`, and the level is fixed **after** the `√d` loss:

    Σ_{d≤D²} τ₃(d)·√d·Q·ℰ ≍ D³ (log D)² Q ℰ ≤ P/L  ⟺  D³ ≤ X ℰ^{-1} L^{-4}.

So `√d·ℰ ≤ D·ℰ ≤ (X/ℰ)^{1/3}·ℰ = X^{1/3}ℰ^{2/3}`, which never has to be small. The range
`d ≤ Q^{1/5}` of Hypothesis T is only an admissibility condition (`D² ≤ (X/ℰ)^{2/3} ≤ P^{0.14}
≤ Q^{1/5}`), not the level. The gain comes from `log D = (log X + log ℰ^{-1})/3 - O(log L)`,
with the `√d` loss already accounted for. A sharper bound (Weil, Kloosterman) would only change
the constant `1/3`.

### What remains to prove for Hypothesis T

The complete Vaughan bookkeeping with `χ`: Type I sums split into `d` shifted progressions
of length `Q/(md) ≫ Q^{7/15}`; Type II sums with the coprimality `(n,d)=1` removed by Möbius;
endpoints; uniformity in `d ≤ Q^{1/5}`. **Since written in `hypothesis-T.md`** (with `d ≤ X^{1/4}`,
Type II via Lemma S at `s = 0`, coprimality removed by Cauchy–Schwarz). Not independently verified.

## Level and gain under Hypothesis T

Choose `H = D² L⁴`. Then `Σ_{d≤D²} τ₃(d)|R_d| ≪ P/L` as soon as `D³ ≤ X ℰ^{-1} L^{-4}`.
For `Q ≥ P^{1-δ}` with `δ = 1/5`: `D² ≤ P^{0.14} ≤ Q^{1/5}` ✓. Moreover
`log(1/ℰ) ≥ c₁ log P / K² - 5 log log P` (since `log Q ≥ 0.8 log P` and `log|Y| ≤ (1+o(1)) K log P`).

    S_Q ≪ P / (log X + c₁ log P / K²)        (P^{4/5} ≤ Q ≤ P/2).

Dyadic sum over `X = 2^j`, `1 ≤ j ≤ δ log₂ P`:

    Σ_j P/(j log 2 + c₁ log P/K²) ≪ P log(1 + δK²/c₁) ≪ P (1 + log K).

Primes `q ≤ P^{4/5}`: Brun–Titchmarsh gives `2P log(1/δ) + O(P)` (integral of Prop. 17.9).
Higher powers: `H₂ = o(P)` (Prop. 17.10). Hence, **under T**:

    log B ≤ C₀ P (1 + log K).

## Consequence (conditional)

(17.6) and (17.47): `log B ≥ (1 + a + e) log A ≥ (c_g - o(1)) K P`. Therefore

    c_g K ≤ C₀ (1 + log K) + o(1)  ⟹  K ≤ K₀ (absolute, effective):

**under Hypothesis T, every restricted-support family satisfies `N ≤ P^{K₀}` for `P ≥ P₀`.**
This replaces `14 log log P` by an absolute constant. The quadratic and polynomial range
`P^{3/2} < N ≤ P^{K₀}` stays open; Wall II is **not** closed.

## Unconditional gain

None. With the untwisted estimates of §16 alone, the remainders `R_d` cannot be controlled
beyond the trivial level, and the joint sieve reproduces Brun–Titchmarsh.
