# Proposition 16.2χ and the top-range theorem

Status: **research note with written, self-audited proofs.** The two new unconditional results are:
- **Proposition 16.2χ**: reciprocal-phase sums over primes twisted by a Dirichlet character, in the regime $|Y| \le X^2$.
- **Theorem B**: pointwise in $N$, the prime moduli $q \in (P/\mathcal T, P]$ carry $o(P)$ of the mass $\sum_q\log q\,n_N(q)$.

The algebraic identities used are verified in Lean (`Goldbach/ReciprocalPhase.lean`). The analytic steps are not formalized.

**Not proved:** Lemma Ω (equivalently Lemma $\Omega_{\mathcal T}$, §8), Wall II, Williamson, Goldbach.

Notation: $e(x) = e^{2\pi ix}$, $\Lambda$ von Mangoldt, $\tau$ divisor function, $\psi(y) = y - \lfloor y\rfloor - \frac12$, $\|x\|$ distance to $\mathbb Z$.
For a family: $I = \mathbb P\cap[3, P]$, $n_N(q) = \#\{\ell \in I : q \mid N - \ell\}$, $K = \log N/\log P$.

---

## 0. External inputs (published, not reproved)

| Input | Statement used |
|---|---|
| [KL] Kusmin–Landau (Graham–Kolesnik Th. 2.1) | if $g'$ is monotone on an interval $J$ and $\|g'(x)\| \ge \lambda > 0$ on $J$, then $\bigl|\sum_{k\in J}e(g(k))\bigr| \le \cot(\pi\lambda/2) \le 2/(\pi\lambda)$ |
| [vdC] $k$-th derivative test, $k \ge 2$ (Titchmarsh Th. 5.9 for $k = 2$, Th. 5.13 for $k \ge 3$; Graham–Kolesnik Th. 2.8 states a variant with all derivatives $\asymp FZ^{-r}$, which also holds here) | if $\lambda \le |g^{(k)}| \le B\lambda$ on $J$, $|J| \le Z$: $\sum_{k\in J}e(g(k)) \ll_{k,B} Z\lambda^{1/(2^k-2)} + Z^{1-2^{2-k}}\lambda^{-1/(2^k-2)}$ |
| [V] Vaughan's identity (Davenport, *Multiplicative Number Theory*, Ch. 24) | below |
| [S] Selberg's upper-bound sieve (Halberstam–Richert Th. 3.2) | for weights $w \ge 0$, $\mathcal A_e = g(e)\mathcal X + r_e$, $g$ multiplicative with $0 \le g(p) < 1$: $S(\mathcal A, D) \le \mathcal X/G(D) + \sum_{e<D^2,\,e\mid\Pi(D)}3^{\omega(e)}|r_e|$ |
| [Va] Vaaler | for weights $w_j \ge 0$ with sum $W$ and $H \ge 1$: $\bigl|\sum_jw_j\psi^*(x_j)\bigr| \le \frac{W}{2H+2} + \sum_{1\le|h|\le H}\bigl|\sum_jw_je(hx_j)\bigr|$ |
| [RS] Rosser–Schoenfeld; Mertens | $\theta(x) \le 1.02x$ ($x$ large), $\psi(x) - \theta(x) \le 1.43\sqrt x$, $\sum_{x<p\le cx}\frac{\log p}p = \log c + o(1)$ |
| $\tau^2$ mean value | $\sum_{k\le x}\tau(k)^2 \le x(1+\log x)^3$ |

In [Va], $\psi^* = \psi$ off $\mathbb Z$ and $\psi^* = 0$ on $\mathbb Z$. **No result of [CC] is used in this note**, not even its Prop. 16.2. The case
$d = 1$ of Proposition 16.2χ is an independent proof of a bound of the same shape.

---

## 1. Lemma R (shifted reciprocal sums over integers)

> **Lemma R.** There are absolute constants $Z_0$, $C_R$ such that the following holds. Let $Z \ge Z_0$, $0 \le s < 1$, $A \ne 0$ real with
> $F := |A|/Z \le Z^4$, and let $J \subseteq [Z, 2Z]$ be an interval. Then
> $$\Bigl|\sum_{k\in J}e\Bigl(\frac{A}{k+s}\Bigr)\Bigr| \le \frac{4Z}{F} + C_RZ^{61/62}.$$

Put $g(x) = A/(x+s)$. Then $g^{(j)}(x) = (-1)^jj!A(x+s)^{-j-1}$, so every derivative has constant sign on $J$.

**Low frequency: $F \le Z/2$ (Kusmin–Landau).**
- For $x \in [Z, 2Z]$: $|g'(x)| \in \bigl[\frac{|A|}{(2Z+1)^2}, \frac{|A|}{Z^2}\bigr] \subseteq \bigl[\frac F{5Z}, \frac FZ\bigr]$ (for $Z \ge 5$).
- Since $F/Z \le \frac12$, we have $\|g'\| = |g'| \ge \lambda := F/(5Z)$, and $g'$ is monotone.
- [KL] gives $\le 2/(\pi\lambda) = 10Z/(\pi F) < 4Z/F$.
- This is the polylogarithmic regime, where Lemma S of `hypothesis-T.md` (which needs $F \ge Z^{1/2}$) does not apply.

**High frequency: $F > Z/2$ (van der Corput).**
- Then $F \ge Z^{1/2}$ (for $Z \ge 4$). Let $\alpha = \log F/\log Z \in [1/2, 4]$ and $k = \lfloor\alpha\rfloor + 2 \in \{2, \dots, 6\}$.
- On $J$: $\lambda_k \le |g^{(k)}| \le 3^{k+1}\lambda_k$, with $\lambda_k = k!|A|(2Z+1)^{-k-1} \asymp_k Z^{\alpha-k}$, and $\alpha - k \in [-2, -1)$.
- [vdC] gives $Z^{e_1} + Z^{e_2}$, where:
  - $e_1 = 1 + \frac{\alpha-k}{2^k-2} \le 1 - \frac1{2^k-2} \le 1 - \frac1{62}$;
  - $e_2 = 1 - 2^{2-k} + \frac{k-\alpha}{2^k-2}$.

| $k$ | range of $\alpha$ | bound for $e_2$ | value |
|---|---|---|---|
| 2 | $[\frac12, 1)$ | $0 + \frac32\cdot\frac12$ | $0.75$ |
| 3 | $[1, 2)$ | $1 - \frac12 + \frac26$ | $0.834$ |
| 4 | $[2, 3)$ | $1 - \frac14 + \frac2{14}$ | $0.893$ |
| 5 | $[3, 4)$ | $1 - \frac18 + \frac2{30}$ | $0.942$ |
| 6 | $\{4\}$ | $1 - \frac1{16} + \frac2{62}$ | $0.970$ |

All of these are $\le 61/62 = 0.9839$. The implied constants depend only on $k \le 6$ and $B = 3^{k+1}$, so they are absolute.
(This is the computation of range (i) of Lemma S in `hypothesis-T.md`, redone here.) $\square$

The bound is uniform in $s \in [0, 1)$, in $J$, and in the sign of $A$.

---

## 2. Statement

> **Proposition 16.2χ.** There are absolute effective constants $X_0$, $C$ such that, for $X \ge X_0$, every integer $1 \le d \le X^{1/10}$,
> every Dirichlet character $\chi \bmod d$ (principal included), every interval $I \subseteq (3X/4, X)$, and every real $Y$ with
> $0 < |Y| \le X^2$, writing $L = \log X$ and $\rho = |Y|/X$:
> $$\Bigl|\sum_{n\in I}\Lambda(n)\chi(n)e(Y/n)\Bigr| \le C\,X\bigl(L^4\rho^{-1/2} + d^{1/62}L^4X^{-1/248}\bigr).$$
> In particular, for each fixed $d$ the sum is $\le C\,X(\log X)^{-12}$ uniformly in $\chi \bmod d$, in $I$, and in $Y$ with
> $(\log X)^{32} \le |Y|/X \le X$.

The case $d = 1$ is the untwisted proposition.

---

## 3. Vaughan's decomposition

Take $U = V = X^{1/5}$ and $f(n) = \mathbf 1_I(n)\chi(n)e(Y/n)$. By [V] (checked numerically; see §10),
$\sum_{n\le X}\Lambda(n)f(n) = S_1 + S_2 + S_3 + S_4$, where:
- $S_1 = \sum_{n\le U}\Lambda(n)f(n) = 0$, because $I \subseteq (3X/4, X)$ and $U < 3X/4$;
- $S_2 = -\sum_{t\le UV}c_t\sum_rf(rt)$ with $c_t = \sum_{md=t,\,m\le U,\,d\le V}\Lambda(m)\mu(d)$, so $|c_t| \le \sum_{m\mid t}\Lambda(m) = \log t$;
- $S_3 = \sum_{v\le V}\mu(v)\sum_hf(hv)\log h$;
- $S_4 = -\sum_{m>U}\sum_{k>V}\Lambda(m)\bigl(\sum_{v\mid k,\,v\le V}\mu(v)\bigr)f(mk)$.

Since $\chi$ is completely multiplicative, $f(rt) = \chi(t)\chi(r)\mathbf 1_I(rt)e(Y/(rt))$, and similarly for the other products.

---

## 4. Type I sums ($S_2$, $S_3$)

**Setup.**
- Fix $t \le UV = X^{2/5}$. Only $r$ with $(r, d) = 1$ contribute; write $r = dk + a$ with $0 \le a < d$ and $(a, d) = 1$. Then $\chi(r) = \chi(a)$ is
  constant on each class.
- $rt \in I$ means $k \in J_{t,a}$, an interval contained in $\bigl[\frac{3X}{4td} - 1, \frac X{td}\bigr] \subseteq [Z_t, 2Z_t]$ with $Z_t := \frac X{2td}$.
  This uses $\frac X{4td} \ge 1$, which holds because $td \le X^{1/2}$.
- By Lean `phase_residue_shift`, $\frac Y{t(dk+a)} = \frac{A_t}{k + a/d}$ with $A_t = \frac Y{td}$ and shift $s = a/d \in [0, 1)$.
  The normalized phase is $F = |A_t|/Z_t = 2\rho$, **independent of $t$ and $a$**.
- Hypotheses of Lemma R: $F = 2\rho \le 2X \le (X^{1/2}/2)^4 \le Z_t^4$, and $Z_t \ge X^{1/2}/2 \ge Z_0$. So for every subinterval $J' \subseteq J_{t,a}$:
  $$\Bigl|\sum_{k\in J'}e\Bigl(\frac{A_t}{k+a/d}\Bigr)\Bigr| \le \frac{2Z_t}\rho + C_RZ_t^{61/62}.$$

**$S_2$.** With $\varphi(d) \le d$ classes:
$$|S_2| \le \sum_{t\le UV}\log t\,\varphi(d)\Bigl(\frac X{td\rho} + C_R\Bigl(\frac X{2td}\Bigr)^{61/62}\Bigr) \le \frac{2L^2X}\rho + 62\,C_R\,L\,d^{1/62}X^{61/62}(UV)^{1/62}.$$
Here $X^{61/62}(UV)^{1/62} = X^{1-3/310}$.

**$S_3$.** The weight $\log(dk+a)$ is monotone and $\le L$ on $J_{t,a}$. Abel summation multiplies the maximal partial sum by $\le 2L$, and
Lemma R holds for every subinterval. Hence $|S_3| \le 2L\cdot(\text{the bound for } S_2)$.

**Total:** $|S_2| + |S_3| \le C\bigl(L^3X/\rho + L^2d^{1/62}X^{1-3/310}\bigr)$.

The modulus $d$ enters only through $\varphi(d)\,d^{-61/62} \le d^{1/62}$, and through $d \le X^{1/10}$, which guarantees $F \le Z_t^4$ and $Z_t \ge Z_0$.

---

## 5. Type II sums ($S_4$)

**Setup.**
- Put $a_m = \Lambda(m)\chi(m)$ and $\beta_k = \chi(k)\sum_{v\mid k,\,v\le V}\mu(v)$, so $|a_m| \le \Lambda(m) \le L$ and $|\beta_k| \le \tau(k)$.
  **The character sits only in these coefficients.**
- Since $mk \in I$ and $k > V$, we have $m < X/V$. Cut $m \in (U, X/V)$ into at most $2L$ dyadic blocks $(M, 2M]$, and put $K := X/M$.
  For $m \in (M, 2M]$, $mk \in I$ forces $k \in (3K/8, K)$.
- Let $S_M$ be the block sum. Then $\sum_{k<K}|\beta_k|^2 \le \sum_{k<K}\tau(k)^2 \le KL^3$, and $\sum_{M<m\le2M}|a_m|^2 \le L\psi(2M) \le 3ML$.

**Case (α): $M \le X^{1/2}$, so $K \ge X^{1/2}$. Cauchy–Schwarz over $k$.**
$$|S_M|^2 \le \Bigl(\sum_k|\beta_k|^2\Bigr)\sum_k\Bigl|\sum_ma_m\mathbf 1_I(mk)e\Bigl(\frac Y{mk}\Bigr)\Bigr|^2 = \Bigl(\sum_k|\beta_k|^2\Bigr)\sum_{m,m'}a_m\overline{a_{m'}}\sum_{k\in J(m,m')}e\Bigl(\frac Y{mk} - \frac Y{m'k}\Bigr).$$
- **The character is removed from the correlation.** In the first factor $|\beta_k|^2 = |\chi(k)|^2|\sum\mu|^2 \le \tau(k)^2$, so $\chi$ only lowers it.
  The inner sum over $k$ carries **no character**: $\chi(m)\overline{\chi(m')}$ is part of the coefficient $a_m\overline{a_{m'}}$, of modulus $\le L^2$.
- $J(m, m') = \{k > V : mk \in I,\ m'k \in I\}$ is an interval in $(3K/8, K)$.
- By Lean `phase_difference`, the phase is $B/k$ with $B = Y(m'-m)/(mm')$.

Let $\Delta = |m - m'|$.
- **$\Delta = 0$:** the inner sum is $\le K$.
- **$\Delta \ge 1$:** split $J$ at $3K/4$ and apply Lemma R with $Z = 3K/8$ and $Z = 3K/4$.
  - Since $mm' \in (M^2, 4M^2]$ and $KM = X$, $F = |B|/Z \in [\rho\Delta/(3M),\ 8\rho\Delta/(3M)]$.
  - Moreover $F \le 8\rho/3 \le 3X \le (3K/8)^4$ (as $K \ge X^{1/2}$).
  - The inner sum is $\le 18KM/(\rho\Delta) + 2C_RK^{61/62}$.

Summing over the $\le M$ values of $m$ and $1 \le |\Delta| < M$:
$$\sum_{m,m'}|a_ma_{m'}|\,|\cdots| \le L^2\Bigl[X + \frac{36LXM}\rho + 4C_RM^2K^{61/62}\Bigr],$$
$$|S_M|^2 \le L^5X^2\Bigl[\frac1M + \frac{36L}\rho + 4C_RK^{-1/62}\Bigr].$$
With $M > U = X^{1/5}$ and $K \ge X^{1/2}$ (so $K^{-1/62} \le X^{-1/124}$): $|S_M| \le CL^3X\bigl(X^{-1/10} + \rho^{-1/2} + X^{-1/248}\bigr)$.

**Case (β): $M > X^{1/2}$, so $K < X^{1/2}$. Cauchy–Schwarz over $m$.**
$$|S_M|^2 \le \Bigl(\sum_m|a_m|^2\Bigr)\sum_{k,k'}\beta_k\overline{\beta_{k'}}\sum_{m\in J'(k,k')}e\Bigl(\frac Y{mk} - \frac Y{mk'}\Bigr).$$
- **The character is removed from the correlation.** $|a_m|^2 \le \Lambda(m)^2$, and the inner sum over $m \in J'(k,k') \subseteq (M, 2M]$ carries
  no character. The phase is $B'/m$ with $B' = Y(k'-k)/(kk')$.
- For $\Delta = |k - k'| \ge 1$: since $kk' \in (9K^2/64, K^2)$, $F = |B'|/M \in [\rho\Delta/K,\ 7.2\rho\Delta/K]$, and $F \le 7.2X \le M^4$.
  Lemma R with $Z = M$ gives $\le 4MK/(\rho\Delta) + C_RM^{61/62}$.
- Using $|\beta_k\beta_{k'}| \le \frac12(|\beta_k|^2 + |\beta_{k'}|^2)$:
$$|S_M|^2 \le 3ML\bigl[MKL^3 + 16L^4MK^2/\rho + 2C_RL^3K^2M^{61/62}\bigr] = 3L^4X^2\Bigl[\frac1K + \frac{16L}\rho + 2C_RM^{-1/62}\Bigr].$$
- The block is nonempty only if $K > V = X^{1/5}$. With $M^{-1/62} \le X^{-1/124}$: $|S_M| \le CL^{5/2}X\bigl(X^{-1/10} + L^{1/2}\rho^{-1/2} + X^{-1/248}\bigr)$.

**Total over $\le 2L$ blocks:** $|S_4| \le CL^4X\bigl(\rho^{-1/2} + X^{-1/248}\bigr)$.

---

## 6. Conclusion of Proposition 16.2χ

Adding §4 and §5, and using $L^3/\rho \le L^4\rho^{-1/2}$ for $\rho \ge 1$ and $L^2X^{-3/310} \le L^4X^{-1/248}$:
$$|S| \le C\,X\bigl(L^4\rho^{-1/2} + d^{1/62}L^4X^{-1/248}\bigr).$$
For $\rho < 1$ the bound exceeds the trivial $|S| \le \psi(X) \le 1.04X$ once $C \ge 2$. $\square$

**Uniformity audit.**
- **$Y$:** enters only through $\rho$ (both signs; Lemma R is sign-free) and through $|Y| \le X^2$. That is used only to have $F \le Z^4$.
  For $|Y| > X^2$, Prop. 16.3χ of `hypothesis-T.md` takes over.
- **$I$:** every inner sum is over a subinterval, and Lemma R is uniform in subintervals.
- **$\chi$:** enters only through $|\chi| \le 1$ in the coefficients, and through constancy on residue classes in Type I.
- **$d$:** enters only through the factor $d^{1/62}$ and the range $d \le X^{1/10}$.
- **Constants:** absolute and effective.
- **Lemma S:** not used beyond its range (i) computation, which is redone in Lemma R. The polylogarithmic regime $F \le Z/2$ is handled by Kusmin–Landau.

---

## 7. Theorem B (top range)

> **Theorem B.** For every fixed $\mathcal T > 1$ and $\epsilon \in (0, 1/3)$:
> $$\lim_{P\to\infty}\ \sup_{\substack{N\ \mathrm{even}\\ P^{5/3}\le N\le P^{2-\epsilon}}}\ \frac1P\sum_{\substack{P/\mathcal T<q\le P\\ q\ \mathrm{prime}}}(\log q)\,n_N(q) = 0.$$
> No restricted-support hypothesis is made: the statement holds for every even $N$ in the range.

**Parameters.** Fix $\mathcal T > 1$, $\epsilon$, an integer $D \ge 3$ (sifting limit) and an integer $H \ge 1$ (Fourier truncation).
Let $P \to \infty$; all $o(\cdot)$ below are as $P \to \infty$ with $\mathcal T, \epsilon, D, H$ fixed, uniformly in $N$. Put $L = \log P$,
$\mathcal Q = \mathbb P\cap(P/\mathcal T, P]$, and $\Pi(D) = \prod_{2<p<D}p$. For $P$ large, every $q \in \mathcal Q$ is odd and $q > D^2$.

**B.1 Dual sequence.**
- For $q \in \mathcal Q$, $q \mid N - \ell$ with $\ell \in [3, P]$ means $\ell = N - bq$. Here $b$ is odd ($N$ even, $\ell$, $q$ odd), and
  $b \in I_q := [\alpha_q, \alpha'_q]$ with $\alpha_q = \frac{N-P}q$, $\alpha'_q = \frac{N-3}q$.
- Let $\mathcal A$ be the multiset $\{N - bq : q \in \mathcal Q,\ b \in I_q \text{ odd}\} \subseteq [3, P]$, with weight $\log q$, and let
  $S(\mathcal A, D)$ be the weight of its elements coprime to $\Pi(D)$.
- Every prime $\ell \ge D$ is coprime to $\Pi(D)$. Each $N - \ell$ with $\ell < D$ has at most $\log N/\log(P/\mathcal T) \le 3$ prime factors in $\mathcal Q$.
  So the **small-prime correction** is
$$\Sigma(N) := \sum_{q\in\mathcal Q}\log q\,n_N(q) \le S(\mathcal A, D) + 3DL.\qquad(\mathrm B.1)$$

**B.2 Local densities; noncoprime residues.**
- Let $e \mid \Pi(D)$ with $e < D^2$. Then $e$ is odd and squarefree, and $(q, e) = 1$ because $q > D^2 > e$. This holds **whatever $\gcd(N, e)$ is**.
- So $e \mid N - bq \iff b \equiv N\bar q \pmod e$, a single class. Combined with "$b$ odd", it is a single class $\beta_q \bmod 2e$
  (Lean `odd_class_mod_two_mul`). The class depends only on $q \bmod e$.
- By the exact count (7.1) of `hypothesis-T.md` with $m = 2e$ (its core identity $\lfloor y\rfloor - \lceil x\rceil + 1 = (y - x) - \psi(y) - \psi(-x)$ is
  Lean `floor_sub_ceil_eq`):
$$\mathcal A_e = \frac{\mathcal X}e + r_e,\qquad \mathcal X = \sum_{q\in\mathcal Q}\log q\,\frac{P-3}{2q},\qquad r_e = -\sum_{q\in\mathcal Q}\log q\bigl[\psi(x'_q) + \psi(x_q)\bigr],$$
  with $x'_q = \frac{\alpha'_q-\beta_q}{2e}$ and $x_q = \frac{\beta_q-\alpha_q}{2e}$. The case $e = 1$ (the pure rounding term) is included.
- So $g(e) = 1/e$, and Mertens gives $\mathcal X = \frac P2(\log\mathcal T + o(1))$.

**B.3 Selberg.** By [S], $S(\mathcal A, D) \le \mathcal X/G(D) + \sum_{e<D^2,\,e\mid\Pi(D)}3^{\omega(e)}|r_e|$, with
$$G(D) = \sum_{\substack{e<D\\ e\ \mathrm{odd,\ squarefree}}}\frac1{\varphi(e)} = \sum_{\substack{n\ \mathrm{odd}\\ \mathrm{rad}(n)<D}}\frac1n \ge \sum_{\substack{n<D\\ n\ \mathrm{odd}}}\frac1n \ge \frac12\sum_{n<D}\frac1n \ge \frac12\log D.$$
The middle inequality holds because $\frac1{2k-1} > \frac1{2k}$. Also $\sum_{e<D^2}3^{\omega(e)} \le \sum_{e<D^2}\tau_3(e) \le D^2(1+2\log D)^2$.

**B.4 Rounding terms (Vaaler).**
- **Integer points.** $x'_q \in \mathbb Z$ forces $\alpha'_q \in \mathbb Z$, i.e. $q \mid N - 3$. Likewise $x_q \in \mathbb Z$ forces $q \mid N - P$.
  At most $3 + 3$ such $q$, so $\psi \ne \psi^*$ costs $\le 6L$.
- **Vaaler.** By [Va], with $\theta_{\mathcal Q} = \sum_{q\in\mathcal Q}\log q \le 1.02P$:
$$|r_e| \le \frac{1.02P}{H+1} + \sum_\pm\sum_{1\le|h|\le H}|T^\pm_h(e)| + 6L,\qquad T^+_h(e) = \sum_{q\in\mathcal Q}\log q\,G_h(q)\,e\Bigl(\frac{h(N-3)}{2eq}\Bigr),$$
  with $G_h(q) = e(-h\beta_q/(2e))$. $T^-_h$ is the same with $-h(N-P)$ in place of $h(N-3)$ and with $G_{-h}$ in place of $G_h$ (audit
correction; it still has modulus 1 and depends only on $q \bmod e$). *Notation warning:* in §7 the letter $e$ denotes both the sieve modulus and
the function $e(x) = e^{2\pi ix}$.

**B.5 Character expansion (fixed modulus).**
- $G_h$ is a function on $(\mathbb Z/e)^\times$ of modulus 1. So $G_h = \sum_{\chi\bmod e}\hat G_h(\chi)\chi$ with $|\hat G_h(\chi)| \le 1$.
- Hence $|T^\pm_h(e)| \le \sum_{\chi\bmod e}\bigl|\sum_{q\in\mathcal Q}\chi(q)\log q\,e(Y/q)\bigr|$, with $Y = \pm h(N-3)/(2e)$ or $\mp h(N-P)/(2e)$.
- Replacing primes by $\Lambda$ costs $\le 1.43\sqrt P$.

**B.6 Applying Proposition 16.2χ.**
- Let $X_i = 2P(3/4)^i$. The intervals $(X_{i+1}, X_i)$, $0 \le i \le i_0(\mathcal T) = O(\log\mathcal T)$, together with the $O(\log\mathcal T)$ endpoints
  (cost $O(L\log\mathcal T)$), cover $(P/\mathcal T, P]$. Each $I_i = (P/\mathcal T, P]\cap(X_{i+1}, X_i)$ lies in $(3X_i/4, X_i)$, and $X_i \in (P/\mathcal T, 2P]$.
- Hypotheses:
  - $d = e < D^2 \le X_i^{1/10}$.
  - $|Y| \le HN/(2e) \le HP^{2-\epsilon} \le (P/\mathcal T)^2 < X_i^2$ for $P$ large; **this is where $N \le P^{2-\epsilon}$ is used**.
  - $\rho = |Y|/X_i \ge \frac{N-P}{4eP} \ge P^{2/3}/(5e)$.
- Proposition 16.2χ gives, for each of the finitely many $(e, \chi, h, \pm, i)$:
  $$\Bigl|\sum_{n\in I_i}\Lambda(n)\chi(n)e(Y/n)\Bigr| \le C\,2P\bigl((\log 2P)^4\sqrt{5e}\,P^{-1/3} + e^{1/62}(\log 2P)^4(P/\mathcal T)^{-1/248}\bigr) = o(P).$$
- Hence $\sum_\pm\sum_{1\le|h|\le H}|T^\pm_h(e)| = o(P)$ for each $e < D^2$, uniformly in $N$.

**B.7 Assembly and order of limits.** By (B.1)–(B.6):
$$\Sigma(N) \le \frac{\frac P2(\log\mathcal T + o(1))}{\frac12\log D} + D^2(1+2\log D)^2\Bigl(\frac{1.02P}{H+1} + o(P)\Bigr) + 3DL.$$
Since the left side depends on neither $D$ nor $H$, the limits can be taken in this order:
1. Fix $\mathcal T$, $D$, $H$ and let $P \to \infty$:
   $$\limsup_{P\to\infty}\ \sup_N\frac{\Sigma(N)}P \le \frac{\log\mathcal T}{\log D} + \frac{1.02\,D^2(1+2\log D)^2}{H+1}.$$
2. Take $H = D^3$ (for each fixed $D$, still before $P \to \infty$): the bound is $\frac{\log\mathcal T}{\log D} + \frac{1.02(1+2\log D)^2}D$.
3. Let $D \to \infty$: the $\limsup$ is $0$. $\square$

**Checklist.**
- (i) The **rounding terms** are the $r_e$, including $e = 1$; they are controlled by B.4–B.6.
- (ii) The **case $d = 1$** is Proposition 16.2χ with $\chi$ trivial (the untwisted proposition).
- (iii) **Noncoprime residues:** $(q, e) = 1$ always, since $q > D^2$; $\gcd(N, e) > 1$ needs no special treatment (B.2).
- (iv) The **small-prime correction** is (B.1).
- (v) The **integer points** cost $6L$.
- (vi) **Prime powers** cost $1.43\sqrt P$.
- (vii) **No dependence on [CC]** and none on Lemma 17.12.

---

## 8. Consequences for Lemma Ω

**Corollary B1 (slowly growing top range).** There is a function $\mathcal T(P) \to \infty$ such that
$\sup_N\frac1P\sum_{P/\mathcal T(P)<q\le P}\log q\,n_N(q) \to 0$, with $N$ ranging as in Theorem B.

*Proof.* $\delta(\mathcal T, P) := \sup_N\frac1P\sum_{(P/\mathcal T,P]}$ is nondecreasing in $\mathcal T$. Choose $P_1 < P_2 < \cdots$ with $\delta(j, P) \le 1/j$ for
$P \ge P_j$, and set $\mathcal T(P) = j$ on $[P_j, P_{j+1})$. $\square$

**Corollary B2 (improved necessary condition).** Every restricted-support family with $5/3 \le K \le 2-\epsilon$ and $P \ge P_0(\epsilon)$
satisfies, for every fixed $\mathcal T$ (and for $\mathcal T = \mathcal T(P)$):
$$\sum_{\sqrt P<q\le P/\mathcal T}\log q\,n_N(q) \ge \Bigl(K - \frac12 - o(1)\Bigr)P.$$

*Proof.* Combine:
- Theorem A of `residual-region.md`: $\mathcal M(N) \ge (K - o(1))P$;
- BV for $d \le \sqrt P$: $\le (\frac12 + o(1))P$ pointwise;
- prime powers: $o(P)$;
- Theorem B: $o(P)$ on $(P/\mathcal T, P]$. $\square$

This **supersedes** Corollary G of `residual-region.md` §7.12, whose constant $K - 0.847$ came from the lossy geometric bound
$\frac{\log2}2P$ for $(P/2, P]$. That bound is now replaced by $o(P)$. The parity obstruction noted there for "$\Omega_{1/2}$" disappears.

**Reduced missing estimate.**

> **Lemma $\Omega_{\mathcal T}$ (open).** There exist $\epsilon \in (0, 1/3)$, $\eta > 0$, $\mathcal T > 1$ and $P_0$ such that for every $P \ge P_0$ and every
> even $N$ with $P^{5/3} \le N \le P^{2-\epsilon}$:
> $$\sum_{\sqrt P<q\le P/\mathcal T,\ q\ \mathrm{prime}}\log q\;n_N(q) \le \Bigl(K - \frac12 - \eta\Bigr)P.$$

Given Theorem B, **$\Omega_{\mathcal T}$ is equivalent to Lemma Ω**, for any fixed $\mathcal T$:
- Ω implies $\Omega_{\mathcal T}$ trivially;
- conversely, $\Omega_{\mathcal T}$ plus Theorem B gives Ω with $\eta/2$.

Either one, with BV and Theorem A, **excludes the band** (Corollary B2). Neither is proved.

**What exactly remains.**
- Theorem B handles $O(\log\mathcal T)$ blocks $(3X/4, X)$ with a **fixed** sieve level. Each block then costs
  $\approx P\log\frac43/\log D$, against its true size $\approx P\log\frac43/L$. That is acceptable only because the number of blocks is bounded.
- On $(\sqrt P, P/\mathcal T]$ there are $\asymp L$ blocks. To reach $\Omega_{\mathcal T}$, each block $X \in [\sqrt P, P/\mathcal T]$ needs a sieve level
  $D^2 = P^\lambda$ with $\lambda > 2/(2K-1) \in (2/3, 6/7]$. Concretely:
  $$\sum_{e<P^\lambda,\ e\mid\Pi}\tau_3(e)\,|r_e(X)| = o(P/L)\quad\text{uniformly in } X \in [\sqrt P, P/\mathcal T] \text{ and in } N.\qquad(\mathrm{LD}_\lambda)$$
- Through B.4–B.5 this requires bounds for $\sum_{\chi\bmod e}|\sum_{q\in(3X/4,X)}\Lambda(q)\chi(q)e(Y/q)|$, with moduli $e$ up to $P^\lambda$.
- Proposition 16.2χ allows $e \le X^{1/10}$ with saving $X^{-1/248}$. With the $\varphi(e)$ (or, via Parseval, $\sqrt e$) loss of the character expansion,
  that supports only a level of order $X^{c}$ with $c$ about $10^{-3}$ (rough estimate; not written out). This is far below $2/3$.
- Brun–Titchmarsh gives $2P\log\frac L{2\log\mathcal T}$ on this range, which diverges. Even the **trivial** bound is better: by Lemma E and BV,
  $\Sigma_{\mathrm{large}}(N) \le (K - \frac12 + o(1))P$ for every $N$ (`distribution-profile.md`, Lemma T). Ω asks to beat this by $\eta P$.

**The single remaining quantitative obstruction is therefore $(\mathrm{LD}_\lambda)$ on the blocks $X \in [\sqrt P, P/\mathcal T]$, with $\lambda > 2/(2K-1)$.**

*Remark (not claimed).* Running §7 with a level $D = P^{c}$ that grows like a small power of $P$, using Proposition 16.2χ where
$|Y| \le X^2$ and Prop. 16.3χ where $|Y| \ge X^2/64$, should give $\sum_{\sqrt P<q\le P}\log q\,n_N(q) \le C_0P$ with an absolute but
enormous $C_0$. That would be asymptotically stronger than $2P\log L$, but irrelevant for exclusion. I have not written this out.

---

## 9. Lean (`Goldbach/ReciprocalPhase.lean`, standard axioms only)

| Lean name | Statement | Used in |
|---|---|---|
| `phase_residue_shift` | $\frac Y{t(dk+r)} = \frac{Y/(td)}{k + r/d}$ | §4 |
| `phase_difference` | $\frac Y{mk} - \frac Y{m'k} = \frac{Y(m'-m)/(mm')}k$ | §5 |
| `floor_sub_ceil_eq` | $\lfloor y\rfloor - \lceil x\rceil + 1 = (y-x) - \psi(y) - \psi(-x)$ | B.2 |
| `odd_class_mod_two_mul` | for odd $e$: "$b$ odd $\wedge$ $b \equiv c \pmod e$" $\iff b \equiv \beta \pmod{2e}$ | B.2 |

Also used: `WilliamsonResidual.large_prime_unique_row` ($n_N(q) \le 1$ for $q > (P-3)/2$; context only).

---

## 10. Checks performed

- **Vaughan's identity** in the form of §3 was verified numerically: $N = 3000$, $U = 7$, $V = 11$, random complex $f$, error $10^{-12}$.
- **Numerical sizes** for $X = 2\cdot10^6$, $\chi$ the nontrivial character mod 3, $\rho \in \{40, 400, 4000, 2\cdot10^5\}$:
  $|S_\chi|/X \in [0.0003, 0.002]$. This is consistent with the proposition; it is not evidence for the rate.
- **Exponent table of Lemma R:** recomputed by hand (§1).
- **Self-audit of the Type II exponents:**
  - (α): $X^2K^{-1/62}$ with $K \ge X^{1/2}$ gives $X^{-1/124}$ in $|S_M|^2$, hence $X^{-1/248}$ in $|S_M|$.
  - (β): the same with $M \ge X^{1/2}$.
  - The diagonal terms need $M \ge X^{1/5}$ in (α) and $K > X^{1/5}$ in (β); both hold.

**Audit by a separate agent (2026-11-25).**
- *Procedure.* A separate model instance, which had not seen the derivation, re-derived every step of §1–§7 from the text and from
  `hypothesis-T.md` §2, §7–8.
- *Verdict.* No gap in Lemma R, Proposition 16.2χ or Theorem B.
- *Slips found and corrected:*
  - the van der Corput citation (Graham–Kolesnik Th. 2.8 has a different form; Titchmarsh 5.9/5.13 has the quoted one);
  - $T^-_h$ carries $G_{-h}$, not $G_h$.
- *Constants loose in the safe direction:* at most $1$ prime factor of $N - \ell$ in $\mathcal Q$ (not $3$); integer points $3L$ (not $6L$);
  Type II constants $11.25$ (not $18$).
- *Side observation of the audit:* Theorem B only needs $N \ge P(\log P)^{9}$ from below.
- *Status.* This is **not** an independent human verification.

**Not yet done:** a human reading; Lean formalization of the analytic inequalities.
