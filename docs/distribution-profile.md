# Scale-dependent sieve levels for Lemma Ω

Status: **research note.** Proved here:
- Lemma T, the trivial pointwise bound;
- Proposition PF, an implication: a scale-dependent level profile gives an integrated sieve bound;
- the numerical analysis of admissible profiles.

**No new distribution estimate is proved.** Lemma Ω and Wall II remain **open**.

**Scope of the sufficient conditions (audit correction 2026-11-25).**
- Ω, $\Omega_{\mathcal T}$, Proposition PF and the profile conditions concern **only** the band $P^{5/3} \le N \le P^{2-\epsilon}$ with $\epsilon > 0$ fixed.
- Even a proof of Ω on that band would **not** close the walls. Still open outside it:
  - the neighbourhood of $P^2$;
  - the range $P^{2-\epsilon} < N < P^{950}$. Theorem W only gives the upper bound $N < P^{959}$ (or $P^{950}$), with an effective but uncomputed threshold.
    It proves no absence of families below it.
  - the bands $K < 5/3$, which [CC] treats by exceptional-set arguments only;
  - the connection to `WallIAt P₀` / `WallIIAt P₀` for one common, explicit $P_0$.
- The BV input is ineffective, so the threshold $P_0$ in the exclusion statements is ineffective.

Notation as in `residual-region.md` §7 and `prop-16-2-chi-top-range.md`: $L = \log P$, $K = \log N/\log P$, $n_N(q) = \#\{\ell \in I : q \mid N-\ell\}$,
and
$$\Sigma_{\mathrm{large}}(N) = \sum_{\sqrt P<q\le P,\ q\ \mathrm{prime}}\log q\;n_N(q).$$
Lemma Ω asks for $\Sigma_{\mathrm{large}}(N) \le (K - \frac12 - \eta)P$ for every even $N$ with $P^{5/3} \le N \le P^{2-\epsilon}$.

---

## 1. Lemma T — the trivial bound is exactly the threshold (proved)

> **Lemma T.** For $P \ge P_0$ (ineffective) and every even $N$ with $P^{5/3} \le N \le P^2$:
> $$\mathcal M_{\le\sqrt P}(N) := \sum_{d\le\sqrt P}\Lambda(d)n_N(d) \ge \Bigl(\frac12 - O\Bigl(\frac{\log L}L\Bigr)\Bigr)P,\qquad \Sigma_{\mathrm{large}}(N) \le \Bigl(K - \frac12 + O\Bigl(\frac{\log L}L\Bigr)\Bigr)P.$$

*Proof.*
- **Upper bound for the whole mass.** $\mathcal M(N) = \sum_\ell\log\gcd(N-\ell, L_P) \le \sum_\ell\log(N-\ell) \le (\pi(P)-1)\log N \le KP(1 + 2/L)$
  (Rosser–Schoenfeld). Also $\Sigma_{\mathrm{large}} \le \mathcal M - \mathcal M_{\le D_0}$, where $D_0 = \sqrt P/L^B$.
- **Lower bound for small moduli.** For $(d, N) = 1$, $n_N(d) \ge \pi(P; d, N) - 1$ (the $-1$ removes $\ell = 2$). Bombieri–Vinogradov with $\max_a$ gives
  $$\mathcal M_{\le D_0} \ge \pi(P)\sum_{d\le D_0,\ (d,N)=1}\frac{\Lambda(d)}{\varphi(d)} - O(P/L^A) - O(\sqrt P).$$
- **The excluded moduli.** $\sum_{d\le D_0}\Lambda(d)/\varphi(d) = \log D_0 + O(1)$. The moduli with $(d, N) > 1$ remove
  $\sum_{p\mid N}\log p\,\frac p{(p-1)^2} \le 4\sum_{p\mid N}\frac{\log p}p \le 4\log\log N + O(1) = O(\log L)$.
- **Conclusion.** $\mathcal M_{\le D_0} \ge \frac PL(\frac L2 - O(\log L)) = (\frac12 - O(\frac{\log L}L))P$. $\square$

**Consequences.**
- **Ω is exactly the statement that $\Sigma_{\mathrm{large}}$ beats its trivial bound by $\eta P$.** By Lemma E of `residual-region.md`, this is equivalent to
  $H_{\mathrm{big}}(N) + H_{\mathrm{pow}}(N) \ge (\eta - o(1))P$.
- **Correction of earlier notes.** The Brun–Titchmarsh bound $\mathcal M(N) \le 2P\log L + O(P)$ ("Ω-BT") is **weaker than the trivial bound** and
  carries no information. `residual-region.md` §7.9(v), §7.11 and §7.12(b) have been corrected.
- **Test for any sieve route.** It must produce a constant **below $K - \frac12 \in [7/6, 3/2)$**, not merely a finite one.

---

## 2. Proposition PF — the integrated sieve bound (proved implication)

**Blocks.** Let $X_i = 2P(3/4)^i$ and $\mathcal J_i = (X_{i+1}, X_i)\cap(\sqrt P, P]$, with $\theta_i = \log X_i/L$; consecutive $\theta_i$ differ by
$\log\frac43/L$.
- Let $\mathcal A_i$ be the multiset $\{N - bq : q \in \mathcal J_i \text{ prime},\ b \text{ odd},\ N - bq \in [3, P]\}$, with weight $\log q$.
- Its smooth size is $\mathcal X_i = \sum_{q\in\mathcal J_i}\log q\,\frac{P-3}{2q}$.
- Its remainders are $r_e(i) := \mathcal A_{i,e} - \mathcal X_i/e$ for odd squarefree $e$, with $\mathcal A_{i,e}$ the weight of the elements divisible by $e$.
  This is the dual sequence of `hypothesis-T.md` §7.

**Three hypotheses at level $P^{\lambda}$, from strongest to weakest.**
- **(S$_\lambda$) Absolute (Selberg).** $\sum_{e<P^{\lambda},\ e\mid\Pi}\tau_3(e)\,|r_e(i)| \le P/L^3$.
- **(WF$_\lambda$) Well-factorable (linear sieve).** For every factorisation $D_1D_2 = P^\lambda$ and all coefficients $|\alpha_{d_1}|, |\beta_{d_2}| \le 1$
  supported on divisors of $\Pi(z)$:
  $\bigl|\sum_{d_1<D_1,\,d_2<D_2,\ (d_1,d_2)=1}\alpha_{d_1}\beta_{d_2}r_{d_1d_2}(i)\bigr| \le P/L^3$.
  *(Audit correction 2026-11-25: $r_e$ is defined only for odd squarefree $e$. The sum is therefore restricted to coprime pairs of odd
  squarefree divisors of $\Pi(z)$, so that $d_1d_2$ is again odd and squarefree. This is the support of the linear-sieve remainder, and on it
  (S) ⟹ (WF) holds as stated.)*
- **(SG) Signed aggregate (Selberg).** With $\lambda_d(i)$ the optimal Selberg weights at sifting limit $D_i = P^{\lambda(\theta_i)/2}$ and
  $\rho_e(i) = \sum_{[d_1,d_2]=e}\lambda_{d_1}(i)\lambda_{d_2}(i)$:
  $$\sum_i\sum_e\rho_e(i)\,r_e(i) \le \eta_0P\qquad\text{(one-sided, summed over all blocks).}$$

**Implications.**
- (S) ⟹ (SG), since $|\rho_e| \le \tau_3(e)$ (because $|\lambda_d| \le 1$).
- (S) ⟹ (WF): each squarefree $e$ arises as a coprime product $d_1d_2$ at most $\tau(e) \le \tau_3(e)$ times.
- (SG) is the **exact** error term of Selberg's method. For any real $\lambda_d$ with $\lambda_1 = 1$,
  $$S(\mathcal A_i, D_i) \le \sum_aw_a\Bigl(\sum_{d\mid a}\lambda_d\Bigr)^2 = \mathcal X_i\sum\lambda_{d_1}\lambda_{d_2}g([d_1, d_2]) + \sum_e\rho_e r_e(i),$$
  and the optimal choice makes the first term $\mathcal X_i/G(D_i)$.
- So **only a one-sided bound on the signed, block-aggregated error is needed**. This is the weakest sieve-type hypothesis; it replaces the
  absolute bounds legitimately.

> **Proposition PF.** Let $J \subseteq [5/3, 2-\epsilon]$, $\mathcal T > 1$ fixed, and $\lambda : [\frac12, 1] \to (0, 1]$ continuous. Suppose that, uniformly in
> $P \ge P_0$ and in even $N$ with $K \in J$, one of the following holds:
> - every block $\mathcal J_i$ with $X_i \le P/\mathcal T$ satisfies (S$_{\lambda(\theta_i)}$);
> - or every such block satisfies (WF$_{\lambda(\theta_i)}$);
> - or (SG) holds with $\eta_0 = o(1)$.
>
> Then for these $N$:
> $$\Sigma_{\mathrm{large}}(N) \le \Bigl(2\int_{1/2}^{1}\frac{d\theta}{\lambda(\theta)} + o(1)\Bigr)P.$$
> If moreover $2\int_{1/2}^1d\theta/\lambda(\theta) \le K - \frac12 - \eta$ for every $K \in J$, then **no restricted-support family has $K \in J$** for
> $P$ large.

*Proof.*
- **Top blocks.** The blocks with $X_i > P/\mathcal T$ number $O(\log\mathcal T)$ and contribute $o(P)$ by Theorem B (`prop-16-2-chi-top-range.md`).
  This is the contribution eliminated by Theorem B. In $\theta$ it is an interval of length $\log\mathcal T/L \to 0$, so for a continuous positive $\lambda$
  it changes the integral by $o(1)$. It matters only for profiles that degenerate at scale $1/L$ near $\theta = 1$ (for example a fixed sieve level),
  and those are exactly what Theorem B controls.
- **Block bound (Selberg form).** Every prime $\ell \ge D_i$ in a counted row is coprime to $\Pi(D_i)$. So
  $$\sum_{q\in\mathcal J_i}\log q\,n(q) \le S(\mathcal A_i, D_i) + \sum_{\ell<D_i}\ \sum_{q\in\mathcal J_i,\ q\mid N-\ell}\log q.$$
  Selberg gives $S \le \mathcal X_i/G(D_i) + (\text{error})$, with $g(e) = 1/e$ on odd primes.
  - $G(D) \ge \frac12\log D$: see `prop-16-2-chi-top-range.md` B.3; also $G(D) = \frac12\log D + O(1)$, so this constant is sharp for the method.
  - With $\log D_i = \lambda_iL/2$ this gives $\mathcal X_i/G(D_i) \le 4\mathcal X_i/(\lambda_iL)$.
- **Linear-sieve form.** The upper-bound linear sieve with well-factorable remainder (Iwaniec, *Acta Arith.* 37 (1980); Friedlander–Iwaniec,
  *Opera de Cribro*, Ch. 12) gives $S(\mathcal A_i, z) \le \mathcal X_iV(z)(F(s) + \epsilon) + (\text{WF remainders})$, with $s = \log D/\log z \le 3$.
  - Here $V(z) \sim 2e^{-\gamma}/\log z$ (odd primes) and $F(s) = 2e^\gamma/s$, so $\mathcal X_iV(z)F(s) \sim 4\mathcal X_i/\log D$: the same main term at level $D = P^{\lambda_i}$.
  - Take $z = D^{1/3}$.
  - *External input:* the exact form of Iwaniec's remainder (finitely many bilinear forms, coefficients bounded by 1, any factorisation of
    the level, a loss of $\epsilon$ in the main term) is quoted and was not re-derived here. It is used only in this conditional statement.
- **Main term.** By Mertens with Rosser–Schoenfeld's explicit error, $\mathcal X_i \le \frac P2(\log\frac43 + O(1/L))$, uniformly for $X_i \ge \sqrt P$.
  Partial end blocks are smaller. So each block contributes
  $$\le \frac{2P\log\frac43}{\lambda(\theta_i)L}\Bigl(1 + O\Bigl(\frac1L\Bigr)\Bigr) + \frac P{L^3}.$$
- **Summation.** $\sum_i\frac{\log(4/3)}L\cdot\frac1{\lambda(\theta_i)}$ is a Riemann sum with mesh $\log\frac43/L$ for the continuous function $1/\lambda$
  on $[\frac12, 1]$. It converges to $\int_{1/2}^1d\theta/\lambda$, uniformly in $N$ because $\lambda$ does not depend on $N$. The $O(1/L)$ factors and the
  $\le 2L$ error terms $P/L^3$ sum to $o(P)$.
- **Small primes.** In total $\le \sum_{\ell<P^{1/2}}\log(N-\ell) \le P^{1/2}KL = o(P)$, since $D_i \le P^{1/2}$ (Selberg) or $z \le P^{1/3}$ (linear sieve).
- **Exclusion.** Combine with BV ($\mathcal M_{\le\sqrt P} \le (\frac12 + o(1))P$) and prime powers ($o(P)$). This gives
  $\mathcal M(N) \le (K - \eta + o(1))P$, contradicting Theorem A. $\square$

**Remarks.**
- **Check against earlier results.**
  - A uniform profile $\lambda \equiv \lambda_0$ gives $P/\lambda_0$, recovering Proposition C ($\lambda_0 > 2/(2K-1)$).
  - $\lambda \equiv 1$ gives $1\cdot P$, the parity limit of upper-bound sieves.
  - Since $K - \frac12 \ge 7/6 > 1$, parity does not forbid an admissible profile.
- **Levels above 1 are useless.** For $e > P$, $\mathcal A_e = 0$ and $r_e = -\mathcal X/e$, so $\sum_{e<P^\lambda}\tau_3|r_e| \gg \mathcal X$ once $\lambda > 1$.
  Hence profiles take values in $(0, 1]$.

---

## 3. Admissible profiles

A profile is admissible for $K$ when $\mathcal C(\lambda) := 2\int_{1/2}^1d\theta/\lambda(\theta) < K - \frac12$.
- There is no smallest admissible profile: the admissible set is defined by a single integral constraint.
- The trivial level $\lambda_{\mathrm{triv}}(\theta) = 1 - \theta - o(1)$ is always available. It comes from $|r_e| \le \theta_{\mathcal J}$ per $e$, and it is the
  Brun–Titchmarsh level. Since $\int^1d\theta/(1-\theta) = \infty$, some gain above it is required near $\theta = 1$, and in fact on a substantial range.
- Computed with `scripts/distribution_profile.py` (numerical integration):

| $K$ | target $K - \frac12$ | uniform $\lambda_0 >$ | additive gain $c$: $\lambda = \min(1, 1 - \theta + c)$, need $c >$ | threshold: trivial on $[\frac12, \theta_1]$, $\lambda = 1$ on $[\theta_1, 1]$, need $\theta_1 <$ |
|---|---|---|---|---|
| 5/3 | 1.167 | 0.857 | 0.645 | 0.572 |
| 1.8 | 1.300 | 0.769 | 0.547 | 0.617 |
| 1.9 | 1.400 | 0.714 | 0.493 | 0.646 |
| 2 | 1.500 | 0.667 | 0.448 | 0.672 |

**Reading (scope corrected 2026-11-25).** The thresholds in the table are attached to the three **families** of profiles studied. They are
not necessary conditions for an arbitrary admissible profile.
- *Constant gain family.* An admissible profile of the form $\min(1, 1-\theta+c)$ needs $c$ at least the tabulated value.
- *Threshold family.* A profile that is trivial on $[\frac12, \theta_1]$ and equal to $1$ above needs $\theta_1$ below the tabulated value.
- *Level 1 is not necessary in general.* For example, $\lambda \equiv 0.9$ gives $\mathcal C = 10/9 < 7/6$ without ever reaching level 1. (This
  says nothing about whether such a profile is available.)
- *What is true for every profile.* Admissibility is the single integral condition $2\int d\theta/\lambda < K - \frac12$. Since
  $2\int_{1/2}^1d\theta = 1$, any admissible profile must exceed $2/(2K-1)$ on a set of positive measure.
- No profile close to what is known is admissible (§4).

---

## 4. What the available estimates give

| Source | Profile obtained | $\mathcal C(\lambda)$ | Status |
|---|---|---|---|
| Trivial (per-$q$ counting) | $1 - \theta$ | $\infty$ | proved |
| Theorem B | fixed level on the top $O(\log\mathcal T)$ blocks | top range $o(P)$ | proved |
| Prop. 16.2χ + Parseval, scales $\theta > K/2$ | $\max\bigl(1-\theta,\ \frac{31}{47}(1 - \theta + \frac\theta{248})\bigr)$ | **11.59** (for $K \le 1.97$) | computation (below); not a theorem |
| Prop. 16.3χ, scales $\theta \le K/2$ | gain $\approx c_*\theta^3/(K+1)^2 \approx 10^{-9}$ | — | negligible |
| Hypothetical large sieve over $\chi \bmod e$, averaged over $e$, combined with the Prop. 16.2χ profile | $\max\bigl(1-\theta,\ \min(2(1-\theta), \theta/2),\ \frac{31}{47}(1 - \theta + \frac\theta{248})\bigr)$ | $\approx 7.37$ | **not proved** |
| Required | — | $< K - \frac12 \le 1.5$ | open |

*(Audit correction: the large-sieve row previously displayed only the first two terms of the maximum. That profile equals $2(1-\theta)$ near
$\theta = 1$, so its integral diverges. The value $7.37$ is that of the three-term maximum computed in `scripts/distribution_profile.py`.)*

**The Prop. 16.2χ computation.** This is the method of `hypothesis-T.md` §7–8 with Prop. 16.2χ in place of 16.3χ.
- At a block $X = P^\theta$, Vaaler with $H = D^2L^5$ (coefficients $\ll 1/|h|$, total $\ll\log H$), the character expansion with
  $\sum_\chi|\hat G(\chi)| \le \sqrt e$, and Prop. 16.2χ ($|Y| \le X^2$ requires $\theta > K/2$) give
  $\sum_{e<D^2}\tau_3(e)|r_e| \ll L^7XD^{3+1/31}X^{-1/248} + X/L^3$.
- Requiring $\ll P/L^3$ gives $D^{3+1/31} = P^{1-\theta+\theta/248}L^{-10}$, i.e. $\lambda = \frac{31}{47}(1 - \theta + \frac\theta{248})$. This beats $1 - \theta$ only for
  $\theta > 0.99225$.
- **The resulting bound, $\Sigma_{\mathrm{large}} \le (11.59 + o(1))P$, is worse than the trivial bound $(K - \frac12 + o(1))P$.** It is therefore not
  claimed as a theorem: it would be a true but empty statement.

**Why the large-sieve improvement is not proved.**
- $G_h$ is an additive character of $N\bar q \bmod e$. Its multiplicative Fourier coefficients are Gauss sums: $|\hat G(\chi)| \asymp e^{-1/2}$ for
  primitive $\chi$ when $(N, e) = 1$.
- Averaging over $e$ with the multiplicative large sieve would gain $\sqrt E$ per dyadic range of $e$, giving level about $2(1-\theta)$ where $D^4 \le X$.
- This needs, first, control of imprimitive characters: their multiplicity is $\asymp Q/e'$ for small conductor $e'$, and their Gauss sums depend on
  $\gcd(N, e)$.
- It needs, second, uniformity over all $N$.
- Neither is done here. **Even if done, $\mathcal C \approx 7.37$ is still worse than trivial.**

**Dispersion / bilinear forms.**
- The minimal requirement (SG) is a one-sided bound for a signed sum. Expanding $r_e$ by Vaaler leaves the signed bilinear sums
  $$\mathcal K_\pm(X, h) := \sum_{e<P^\lambda}\rho_e\sum_{q\in(3X/4,X)}\log q\;e\Bigl(\mp\frac{h\,\bar 2\,N\bar q}e \pm \frac{h(N - c_\pm)}{2eq}\Bigr),\qquad c_+ = 3,\ c_- = P,\ 1 \le h \le H.$$
- Derivation of the phase.
  - $\beta = \beta_q(e)$ is the odd class with $\beta \equiv N\bar q \pmod e$ (Lean `odd_class_mod_two_mul`).
  - With $\bar 2 := (e+1)/2$, we have $\beta(1 - 2\bar 2) = -e\beta$, hence $\frac\beta{2e} \equiv \frac{\bar 2\beta}e - \frac\beta2 \equiv \frac{\bar 2N\bar q}e - \frac12 \pmod 1$.
  - So $e(\mp h\beta/(2e)) = (-1)^he(\mp h\bar 2N\bar q/e)$, and the sign $(-1)^h$ is absorbed.
  - **Support of $\rho_e$ (audit correction).** $\rho_e(i) \ne 0$ only for $e = [d_1, d_2]$ with $d_j \mid \Pi(D_i)$, $d_j < D_i$. Every prime factor of
    $e$ is therefore $< D_i \le \sqrt P < q$ for $q$ in the block, so $q \nmid e$ and $\bar q \bmod e$ is well defined on the whole support (even when $e > q$).
- **The Vaaler remainder is not absolute-free (audit correction 2026-11-25).**
  - Write $\psi = \psi_H + R_H$. Vaaler's majorant (Graham–Kolesnik, Th. A.6) gives
    $|R_H(x)| \le \Delta_H(x) := \frac1{2H+2}\sum_{|h|\le H}\bigl(1 - \frac{|h|}{H+1}\bigr)e(hx)$.
  - The truncation error in $\sum_e\rho_er_e$ is therefore at most
    $\sum_e|\rho_e|\sum_q\log q\,\Delta_H(x_{e,q})$. Its $h = 0$ term, $\frac{\theta_{\mathcal J}}{2H+2}\sum_e|\rho_e|$, is controlled by $H \ge P^\lambda L^5$.
  - Its terms $h \ne 0$ are sums $\mathcal K^{|\cdot|}_\pm(X, h)$, defined like $\mathcal K_\pm$ but with the **nonnegative weights $|\rho_e|$** in place of
    $\rho_e$. They must be controlled as well. The signed structure of $\rho_e$ is **not** available for them.
  - The integer points ($x_{e,q} \in \mathbb Z$, which forces $q \mid N-3$ or $q \mid N-P$, so at most two primes per block) cost
    $\le 2L\sum_{e<P^\lambda}|\rho_e| \le 2L^3P^\lambda$ per block. This is negligible for $\lambda < 1$.
  - PF stated directly under the exact hypothesis (SG) is unaffected; only the reduction of (SG) to Kloosterman-type sums needs the extra term.
- These are **incomplete Kloosterman sums over primes, with a reciprocal phase of height $hN/e \ge P^{K-\lambda}$, averaged over $e$ with Selberg
  (or well-factorable) weights**.
- A dispersion argument would need these sums for $e$ up to $P^{\lambda(\theta)}$. Within the constant-gain family this means
  $\lambda(\theta) \ge 1 - \theta + 0.45$; for other profiles the requirement is only the integral condition. No estimate is obtained here.

**Direct estimate of the total incidence.** Lemma T is the direct estimate. Beating it by $\eta P$ is Ω itself (Lemma E: at least $\eta P$ of the
rows' mass lies in prime factors $\ge P$).

---

## 5. The surviving obstruction (exact form)

> **Problem Ω-profile (open).** Find $\epsilon, \eta > 0$, $\mathcal T > 1$ and a continuous $\lambda : [\frac12, 1] \to (0, 1]$ with
> $2\int_{1/2}^1d\theta/\lambda(\theta) \le K - \frac12 - \eta$ on a band $J \subseteq [5/3, 2-\epsilon]$, such that, uniformly in even $N$ with $K \in J$, the
> one-sided aggregated Selberg error (SG) is $\le o(P)$.
>
> Sufficient (corrected): for every block $X = P^\theta \in [\sqrt P, P/\mathcal T]$, with $H = P^{\lambda(\theta)}L^5$ and $e < P^{\lambda(\theta)}$,
> both $\sum_{1\le h\le H}|h|^{-1}|\mathcal K_\pm(X, h)| \le P/L^4$ (signed weights $\rho_e$) and
> $\frac1H\sum_{1\le h\le H}|\mathcal K^{|\cdot|}_\pm(X, h)| \le P/L^4$ (weights $|\rho_e|$, from Vaaler's majorant).

**Quantitative gap.**
- The required gain over the trivial level is at least $0.448$ (as $K \to 2$) to $0.645$ (at $K = 5/3$) **at every scale** in the additive-gain family.
- The proved gain is $\frac{31}{47}\cdot\frac\theta{248} \approx 0.0027$, and only on $\theta > 0.992$ (Prop. 16.2χ). Elsewhere it is about $10^{-9}$ (Prop. 16.3χ).
- **No unconditional distribution estimate in this note improves on the trivial bound of Lemma T.**

**Classification.**
- **Proven pointwise results:** Lemma T, Theorem B, Theorem A, Lemma E.
- **Proven implications:** Proposition PF, and through it Proposition C.
- **Sufficient conditions, all open:** Ω, $\Omega_{\mathcal T}$, (S$_\lambda$)/(WF$_\lambda$)/(SG) with an admissible profile.
- **Exclusions proved in $5/3 \le K < 2$:** none.
- **Wall II:** open.
