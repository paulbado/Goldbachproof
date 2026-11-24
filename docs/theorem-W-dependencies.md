# Reconstructing the internal dependencies of Theorem W: [CC] Th. 15.1 and Prop. 17.13 / (17.47)

Reference: I. O. Bado, *A Closure Chain Toward Williamson's Conjecture* (2026), cited [CC].
This file follows the audit `hypothesis-T.md` (commit `cd79c2e`). **Status: written,
self-audited reconstruction, not independently verified.** Theorem W is not used anywhere
in this file (no circularity).

Notation ([CC] §14): $P \ge 5$ prime, $N > P$ even, $I = \mathbb P\cap[3,P]$, $S = \mathbb P\cap[3,P)$,
$M_\ell = N - \ell$, $A = N - P$, $u = \log P$, $w = 1 + \log u$. A restricted-support family:
every $M_\ell$ is composite with all its prime factors in $S$.
$B = \prod_\ell M_\ell/\mathrm{lcm}_\ell M_\ell$, $n(t) = \#\{\ell \in I : t \mid M_\ell\}$.

## External results used (published, not reproved)

| Code | Statement |
|---|---|
| **[BT]** Montgomery–Vaughan (1973) | $\pi(x;k,a) \le 2x/(\varphi(k)\log(x/k))$ for $(a,k)=1$, $1 \le k < x$ |
| **[RS]** Rosser–Schoenfeld (1962) | $\pi(x) > x/\log x$ ($x \ge 17$), $\pi(x) < 1.25506\,x/\log x$ ($x > 1$), $\theta(x) < 1.01624x$, $\sum_{p\le x}\log p/p < \log x$ |
| **[PNT]** explicit PNT | $x(1 - 1/\log x) < \theta(x) < x(1 + 1/(2\log x))$ for $x \ge 41$ (Rosser–Schoenfeld 1962, Th. 4). Only $|\theta(x)-x| < x/\log x$ is used. *(Correction: an earlier version cited a Dusart constant that I have not verified; it is not needed.)* |
| **[Mat]** Matveev, in the form of Bugeaud–Mignotte–Siksek (2006) Th. 9 | for $\gamma_j \in \mathbb Q_{>0}$, $b_j \in \mathbb Z$, $\Lambda = \prod\gamma_j^{b_j} - 1 \ne 0$: $\log|\Lambda| > -1.4\cdot30^{n+3}n^{4.5}(1+\log B)A_1\cdots A_n$, with $B \ge \max|b_j|$, $A_j \ge \max\{h(\gamma_j), |\log\gamma_j|, 0.16\}$ |
| **[vdC]** van der Corput, $k$-th derivative test | (13.3) of [CC] |
| **[MRSTT]** Lemma 4.1 | see `hypothesis-T.md` §2 |
| **[BS]** Beurling–Selberg minorant (Vaaler 1985) | for an interval $J \subset \mathbb R/\mathbb Z$ of length $\lambda$ and $K \ge 1$, there is a trigonometric polynomial $m$ of degree $\le K$ with $m \le \mathbf 1_J$, $\hat m(0) = \lambda - \frac1{K+1}$, $|\hat m(h)| \le 1$ |

Verified in Lean (`Goldbach/WilliamsonMurIIRatio.lean`): the identity $z = 1 + a + t + e$ (17.1),
hence $z - 1 = \nu + \varepsilon$ with $\nu = a + t$; and (17.4), (17.6). In `WilliamsonMurIIClosure.lean`:
$a \ge G$ (17.32).

---

# Part A — Theorem 15.1

> **Theorem 15.1.** There is an effective $P_1$ such that every restricted-support family with $P \ge P_1$
> satisfies $\log N \le 32000\,u\,w$.

## A.1 Lemma 14.2: $\log B \le 100P(1+\log\log P)$ for $P \ge 5$

*(14.4).* For a prime $q$, let $E_q = \max_\ell v_q(M_\ell)$ and $T_q = \sum_\ell v_q(M_\ell)$. Then
$n(q^a) \ge 1 \iff a \le E_q$, and $\sum_{a\ge1}n(q^a) = T_q$. Hence
$v_q(B) = T_q - E_q = \sum_{a\ge1}(n(q^a)-1)_+$. ✓

*Support of the terms.* If $n(q^a) \ge 2$, two distinct odd indices satisfy $\ell \equiv \ell' \pmod{q^a}$; so $q$ is odd
(the complements are odd) and $2q^a \mid \ell - \ell' \ne 0$, which forces $q^a \le (P-3)/2 =: y$. If $q \mid N$, then
$\ell \equiv 0 \pmod q$ forces $\ell = q$, so $n(q^a) \le 1$. ✓

*[BT].* For $q \nmid N$ and $q^a \le y < P$: $n(q^a) \le \pi(P;q^a,N) \le 2P/(\varphi(q^a)\log(P/q^a))$. ✓

- *$a \ge 2$:* $\log(P/q^a) \ge \log 2$, and $\sum_{a\ge2}\log q/\varphi(q^a) = \log q/(q-1)^2$. Moreover
  $\sum_{q\ge3}\log q/(q-1)^2 < 0.54$ (computed; [CC] says $< 2$). Contribution $\le 4P/\log 2$. ✓
- *$a = 1$:* use the blocks $(P/2^{j+1}, P/2^j]$, $1 \le j \le J = \lfloor u/\log 2\rfloor$. Write $t = P/2^j$. For $q > t/2$, $q \ge 3$:
  $q - 1 \ge 2q/3 > t/3$. With $\theta(t) \le 4t$ (crude, and true by [RS]) and $\log(P/q) \ge j\log 2$, the block contributes
  $\le 2P\cdot\frac{3}{t}\cdot4t/(j\log2) = 24P/(j\log2)$. ✓
- *Total:* $\le \frac{24P}{\log2}(1+\log J) + \frac{4P}{\log 2} \le 100P(1+\log\log P)$. Checked numerically for $P \in \{5, 7, 11, 100, 10^6, 10^{100}\}$
  (e.g. $64.4 \le 147.6$ at $P=5$). The left-hand side is $\le 34.7(1.37+\log\log P)+5.8$ for every $P \ge 5$. ✓

## A.2 Lemma 15.2: $\prod_{\ell\in D}M_\ell \mid B^2$, hence $z\log A \le 200Pw$

Fix $r$, $e_\ell = v_r(M_\ell)$, $E = \max e_\ell$, $T = \sum e_\ell$, so $v_r(B^2) = 2(T - E)$.
- If $E = 0$: trivial.
- If the maximum $E > 0$ is attained at a single row $\ell^*$, then $r$ is a private certificate of $\ell^*$, so $\ell^* \notin D$ and
  $\sum_{\ell\in D}e_\ell \le T - E \le 2(T-E)$.
- If it is attained at $\ge 2$ rows, then $T \ge 2E$, so $\sum_D e_\ell \le T \le 2(T-E)$.

Since $M_\ell \ge A$: $z\log A \le 2\log B \le 200Pw$ (A.1). ✓

## A.3 Lemma 15.3: $\prod_{q\in\mathcal T}C_q \mid B^2$

$\mathcal T$ = the primes $q \in (P/2, P)$ with a private owner $\ell_q$ such that $c_{\ell_q} = 1$; $b_q = v_q(M_{\ell_q})$, $C_q = M_{\ell_q}/q^{b_q}$.
The rows $\ell_q$ are distinct, because each owns exactly one certificate. Fix $r$; we bound
$\sum_{q\in\mathcal T}v_r(C_q)$, where $v_r(C_q) = v_r(M_{\ell_q})$ if $q \ne r$ and $v_r(C_r) = 0$.
- *Unique maximum of $r$ at $\ell^*$, with $\ell^* = \ell_q$ selected:* $r$ is a certificate of $\ell^*$ and
  $c_{\ell^*} = 1$, so $r = q$ and that row contributes $v_r(C_r) = 0$. The other rows contribute $\le T - E$.
- *Unique maximum at $\ell^*$ not selected:* $\le T - E$.
- *Shared maximum:* $\le T \le 2(T - E)$.

Hence $\sum_{q\in\mathcal T}\log C_q \le 2\log B \le 200Pw$. ✓

## A.4 Lemma 15.4: $|\mathcal T| \ge R(P) - 2(z-1)$

$R(P) = \#\mathbb P\cap(P/2,P)$. Each prime of $S$ is absent, tied, or private (a partition), so at most $\nu = a + t$
large primes have no private owner. On the rows with $c_\ell \ge 2$ there are $\sum c_\ell \le \sum 2(c_\ell-1) = 2\varepsilon$ certificates.
Therefore $|\mathcal T| \ge R - \nu - 2\varepsilon \ge R - 2(\nu+\varepsilon) = R - 2(z-1)$, using (17.1) (Lean). ✓

*(14.9) without "effective PNT":* by [RS], $R(P) \ge \pi(P) - 1 - \pi(P/2) \ge \frac{P}{u} - 1.25506\frac{P/2}{u - \log 2} - 1 \ge \frac{P}{4u}$
for $P \ge P'$ (explicit). ✓

## A.5 Lemma 14.3 (three logarithms)

*Hypotheses:* $A > P^2$; two representations $M_{\ell_q} = C_qq^{b_q}$ and $M_{\ell_r} = C_rr^{b_r}$ with $q \ne r$ prime, $\ell_q \ne \ell_r$,
$1 \le C \le e^H$, $H \ge 1$. Put $L := \log A$.

$\Lambda := q^{b_q}r^{-b_r}(C_q/C_r) - 1 = (\ell_r - \ell_q)/M_{\ell_r}$, which is $\ne 0$ and satisfies $|\Lambda| < P/A$.
Apply [Mat] with $n \le 3$ and $(\gamma, b) = (q, b_q), (r, -b_r), (C_q/C_r, 1)$; the third factor is omitted if $C_q = C_r$.
Heights: $A_1 = A_2 = u$, and $A_3 = H$ (since $h(C_q/C_r) \le \log\max(C_q, C_r) \le H$, $|\log(C_q/C_r)| \le H$, and $H \ge 1 > 0.16$).
Constant: $1.4\cdot30^6\cdot3^{4.5} = 1.43\cdot10^{11} < 10^{12}$ (computed). Exponents:
$q^{b} < N \le 2A$ gives $b \le (L+\log2)/(u-\log2) \le 2L$. So
$\log(P/A) = u - L > -10^{12}u^2H(1+\log 2L)$, and since $L > 2u$, $L \le E(1+\log 2L)$ with $E = 2\cdot10^{12}u^2H$.

*Lemma: $t \le E(1+\log 2t)$, $E \ge 1$, $t > 1$ ⟹ $t \le 4E\log 4E$.* The function $\varphi(t) = t/(1+\log 2t)$ is increasing for
$t > 1/2$. With $x = \log 4E \ge \log 4$: $\varphi(4E\log4E) \ge E \iff 4x \ge 1+\log8+(x-\log4)+\log x \iff 3x - \log x \ge 1+\log2$,
which holds from $x = \log 4$ on (value $3.83 > 1.69$), and $3x - \log x$ is increasing there. ✓

Hence $L \le F := 4E\log4E$, and every representation $N = Cq^b + \ell$ with $q > P/2$ has
$b \le B_H := (F+\log2)/(u-\log2)$. For $H = \alpha uw$: $E \asymp_\alpha u^3w$, $F \ll_\alpha u^3w^2$, $B_H \ll_\alpha u^2w^2$. ✓

## A.6 Lemma 14.4 (integral divided difference): checked line by line

*Hypotheses:* $P \ge 64$, $H \ge 1$, $B \ge 1$, $k \ge 1$, $h = P^{1/(2(k+1))}$, $k \ge 4H/\log P$, $2(B+k) \le P^{1/8}$, $P^{k/8} \ge 2$,
$2k+2 \le b \le B$.
*Claim:* an interval of length $h$ contains at most $k$ integers $q \in (P/2, P]$ with $N = Cq^b + \ell$,
$C \in \mathbb Z \cap [1, e^H]$, $0 < \ell \le P$.

Suppose there are $q_0 < \dots < q_k$. Let $f(x) = N/x^b$. Then $f(q_i) = C_i + \eta_i$ with
$\eta_i = \ell_i/q_i^b \in (0, \eta]$, $\eta := P(2/P)^b < 1$.

1. *Range of $f$.* $f$ is decreasing, so on $[q_0, q_k]$: $1 \le C_k \le f \le C_0 + \eta \le 2e^H$. ✓
2. *Derivative.* $|f^{(k)}(x)|/k! = \binom{b+k-1}{k}f(x)x^{-k}$. Lower bound: $\ge 1\cdot1\cdot P^{-k}$. Upper bound:
   $\binom{b+k-1}{k} \le (B+k)^k$ and $x > P/2$ give $\le 2e^H(2(B+k)/P)^k \le 2e^HP^{-7k/8} \le 2P^{-5k/8} \le P^{-k/2}$,
   because $e^H \le P^{k/4}$ and $P^{k/8} \ge 2$. ✓
3. *Mean value for divided differences* ($f \in C^k$): $D_kf = f^{(k)}(\xi)/k!$, so $P^{-k} \le |D_kf| \le P^{-k/2}$. ✓
4. *Fractional part.* $\prod_{j\ne i}|q_i-q_j| \ge i!(k-i)!$, so $|D_k\eta| \le \eta\sum_i\frac{1}{i!(k-i)!} = \eta\frac{2^k}{k!}$.
   Since $b \mapsto 2^bP^{1-b}$ is decreasing ($P > 2$), the worst case is $b = 2k+2$:
   $P^k\eta 2^k/k! \le 2^{3k+2}P^{-k-1} = \frac4P(8/P)^k \le \frac{1}{16}\cdot\frac18 < \frac14$. ✓
5. *Bounds on $D_kC$.* By linearity $D_kC = D_kf - D_k\eta$, so $\frac34P^{-k} \le |D_kC| \le P^{-k/2} + \frac14P^{-k} < 2P^{-k/2}$.
   In particular $D_kC \ne 0$. ✓
6. *Integrality.* Each $\prod_{j\ne i}(q_i - q_j)$ divides $V = \prod_{i<j}(q_j - q_i)$ up to sign, so $VD_kC \in \mathbb Z\setminus\{0\}$ and
   $|D_kC| \ge V^{-1} \ge h^{-k(k+1)/2} = P^{-k/4}$. ✓
7. *Contradiction.* $P^{-k/4} \le |D_kC| < 2P^{-k/2}$ would require $P^{k/4} < 2$, impossible since $P \ge 64$. $\square$

*Remark:* intervals of length $\lfloor h\rfloor \le h$ are allowed.

## A.7 Proposition 14.5 and the dichotomy

**Prop. 14.5** ($H = \alpha uw$, at least $\beta P/u$ distinct primes $q \in (P/2,P)$ with $N = C_qq^{b_q} + \ell_q$,
$1 \le C_q \le e^H$, $b_q \ge 1$, distinct $\ell_q \in [3,P]$; conclusion $\log N \le 10H$ for $P \ge P(\alpha,\beta)$):
- *If $A \le P^2$:* $\log N \le 2u + 1 \le 10H$.
- *Otherwise:* A.5 gives $b_q \le B_H \ll u^2w^2$. Put $k = \lceil4H/u\rceil \le 4\alpha w + 1$ and $h = \lfloor P^{1/(2(k+1))}\rfloor$, so
  $\log h = u/(2(k+1)) + O(1) \gg_\alpha u/w$. The hypotheses of A.6 hold for $P \ge P(\alpha)$ (polylogarithmic
  conditions in $P$).
- *Counting.* For each $b \in [2k+2, B_H]$, cut $(P/2, P]$ into at most $1 + P/h$ half-open intervals of length $\le h$;
  A.6 gives at most $k(1+P/h)$ primes with $b_q = b$. In total
  $\le B_Hk(1+P/h) \ll_\alpha u^2w^3P\exp(-c_\alpha u/w) = o(P/u)$, since $\exp(-cu/\log u)$ beats every power of $u$.
  This is $< \beta P/u$ for $P \ge P(\alpha,\beta)$, so some $q$ has $b_q \le 2k+1$.
- *Conclusion.* $N \le e^HP^{2k+1} + P$, so $\log N \le H + (2k+1)u + \log2 \le 9H + 3u + \log 2 \le 10H$ for $\alpha \ge 4$. ✓

**Proof of Th. 15.1.** $P \ge \max(P', P(3200, 1/16))$.
- *If $z \ge P/(16u)$:* A.2 gives $\log A \le 3200uw$, so $\log N \le \max(\log 2A, \log 2P) \le 3200uw + \log 2$.
- *If $z < P/(16u)$:* A.4 gives $|\mathcal T| > \frac{P}{4u} - \frac{P}{8u} = \frac{P}{8u}$. With $H = 3200uw$, A.3 gives
  $\#\{q \in \mathcal T : \log C_q > H\} < 200Pw/H = P/(16u)$. So more than $P/(16u)$ primes satisfy the hypotheses of
  Prop. 14.5 ($C_q \in \mathbb Z$, $1 \le C_q \le e^H$, $b_q \ge 1$ because $q$ divides its owner, distinct owners), and
  $\log N \le 10H = 32000uw$. $\square$

**Verdict A.** Th. 15.1 is **reconstructed** from [BT], [RS], [Mat] and (17.1) (Lean). Every threshold is effective
(Matveev is explicit), but none is computed. **No gap was found.**

---

# Part B — Proposition 17.13 and (17.47)

> **Proposition B.** There is an effective $P_2$ such that for $P \ge P_2$ and every restricted-support
> family with $N > P^{3/2}$:
> $$G(N,P) := \#\{q \in \mathbb P\cap(P/2,P) : [A, A+P]\ \text{contains no odd multiple of}\ q\} \ge \frac{3P}{20\log P}.$$

## B.1 Lemma 17.11 (geometric criterion)

Let $P/2 < q < P$ and $A/(2q) = m + v$, $m \in \mathbb Z$, $v \in [0,1)$. The odd multiples $q(2j+1) \ge A$ are exactly those with
$j \ge m + v - \frac12$.
- If $v \le \frac12$: $j = m$ gives $q(2m+1) = A + q(1-2v) \in [A, A+q] \subset [A, A+P]$. Not counted.
- If $v > \frac12$: the first one is $q(2m+3) = A + q(3-2v)$. It lies in $[A, A+P]$ iff $v \ge \frac32 - \frac{P}{2q}$.

So $q$ is counted $\iff \frac12 < v < \frac32 - \frac{P}{2q}$; this interval is nonempty and contained in $(\frac12, 1)$ for $P/2 < q < P$. ✓

## B.2 Lemma 17.12 (cancellation), in the range needed

*Claim.* Fix $h \in \mathbb Z\setminus\{0\}$ and $0 < c < d \le 1$. Uniformly over the families with $N > P^{3/2}$ and
$\log N \le 32000u w$ (A), we have $\Sigma := \sum_{cP<q<dP,\ q\ \text{prime}}\log q\,e(hA/(2q)) = o(P)$, effectively.

*Proof.*
- *Reduction to $\Lambda$.* Replacing the primes by $\Lambda$ costs $O(\sqrt P\log^2P)$.
- *Blocks.* Fix $\eta \in (0, c)$ and cut the prefix $(0, dP)$ into blocks $(3X/4, X)$ with $X = d P(3/4)^i$ for
  $0 \le i \le i_0(\eta, d)$ (a finite number), plus a remainder of length $\le \eta P$, which costs $\le \theta(\eta P) + O(\sqrt P\log^2P) \le 1.02\eta P$ by [RS].
  Same for $(0, cP)$; subtract. Endpoints cost $O(\log P)$.
- *A block with $X \asymp P$.* $Y = hA/2$ and $T = |Y|/X \ge (P^{3/2}/2)/(2P) = P^{1/2}/4 \ge (\log X)^{32}$.
  - *If $T \le X$:* **Prop. 16.2** of [CC] gives $|S(X,Y)|/X \ll (\log X)^{-3} + X^{-1/248}L_X^5 = o(1)$.
  - *If $T > X$:* then $|Y| \ge X^2 \ge X^2/64$, and **Prop. 16.3χ** (`hypothesis-T.md`, $\chi$ trivial) gives
    $|S|/X \ll L_X^5\bigl(X^{-1/310} + \exp(-c_*(\log X)^3/\Omega^2)\bigr)$, with
    $\Omega \le \log(|h|N) \le 32000u w + \log|h|$. Since $\log X = u + O(1)$, the exponential is
    $\exp(-c\,u/w^2) = o(u^{-5})$. ✓
- *Effectivity.* Choose $\eta$, then $P$. $\square$

*Audit of Prop. 16.2* (I redid the proof in [CC] §16.4, with van der Corput $k=2$ (16.5) and Lemma 16.4):
- Case $T \le X^{1/3}$: the correlation $\sqrt{Th/L} + M\sqrt{L/(Th)}$, summed with (16.9),
  $\sum_{h<2L}\sqrt h \ll L^{3/2}$ and $\sum h^{-1/2} \ll L^{1/2}$, gives
  $|\mathcal S|^2 \ll (ML)^2L_X^6(L^{-1} + \sqrt T/M + T^{-1/2})$; with $M \gg X^{1/2}$, $\sqrt T/M \le X^{-1/3}$. Type I (16.11) ✓.
- Case $T > X^{1/3}$: off-diagonal terms with $h > LX^{-1/24}$ have
  $F \in [X^{7/24}/4, 11X] \subset [M^{1/4}, M^4]$ ✓; Lemma 16.4; Type I with $F = 2T \in [Z^{1/4}, Z^4]$ ✓.

No gap found. Prop. 16.2 uses only [vdC] and Vaughan's identity.

## B.3 Weighted equidistribution and the constant $3/20$

Put $x_q = q/P$ and $v_q = \{A/(2q)\}$. By B.1, $G = \#\{q : (x_q, v_q) \in \mathcal G\}$ with
$\mathcal G = \{\frac12 < x < 1,\ \frac12 < v < \frac12 + \phi(x)\}$, $\phi(x) = 1 - \frac1{2x}$ increasing, and
$\mathrm{area}(\mathcal G) = \int_{1/2}^1\phi = \frac{1-\log2}{2} = c_g = 0.153426\ldots$

*Explicit inner staircase.* $x_i = \frac12 + \frac{i}{2n}$, $n = 200$, rectangles
$R_i = (x_i, x_{i+1}) \times (\frac12, \frac12 + \phi(x_i)) \subset \mathcal G$ (since $\phi$ is increasing). Total area $= 0.1528006$
(computed; deficit $\le 1/(4n)$).

*Minorant.* For each $i$, take [BS] with $K = 1000$ for $J_i = (\frac12, \frac12 + \phi(x_i))$: $m_i \le \mathbf 1_{J_i}$, $\hat m_i(0) = \phi(x_i) - \frac1{1001}$,
$|\hat m_i(h)| \le 1$. Since $\log q > 0$ and $e(hv_q) = e(hA/(2q))$,
$$W := \sum_{q:(x_q,v_q)\in\mathcal G}\log q \ge \sum_i\sum_{x_iP<q<x_{i+1}P}\log q\,m_i(v_q) = \sum_i\hat m_i(0)\,\Theta_i + \sum_i\sum_{0<|h|\le K}\hat m_i(h)\,\Sigma_{i,h},$$
with $\Theta_i = \sum_{x_iP<q<x_{i+1}P}\log q = \frac{P}{2n} + O(P/\log P)$ ([PNT]) and $|\Sigma_{i,h}| \le \delta P$ (B.2, for
the $n\cdot2K = 400{,}000$ fixed pairs $(i,h)$).

Hence $W \ge \bigl(0.1528006 - \frac{1/2}{1001}\bigr)P - n(1+2K\delta)\,O(P/\log P) - 2nK\delta P \ge 0.15230P - 0.002P$
as soon as $\delta \le 2\cdot10^{-9}$ and $P$ is large enough (effective). So $W \ge 0.1503P$.

*Conclusion.* $\log q < \log P$ gives $G \ge W/\log P \ge 0.1503\,P/\log P > \frac{3}{20}\,\frac{P}{\log P}$. $\square$

**Verdict B.** (17.47) is **reconstructed** for $N > P^{3/2}$, from Th. 15.1 (Part A), Prop. 16.2 (audited),
Prop. 16.3χ (`hypothesis-T.md`), [PNT], [RS] and [BS]. The margin $c_g - 3/20 = 0.0034$ is enough with
$n = 200$, $K = 1000$. **No gap was found.** The rectangle and minorant construction is explicit, so the $o(1)$ of [CC]
is replaced by explicit choices.

---

# Part C — Final assembly of Theorem W

Chain (no use of Theorem W):
1. **Th. 15.1** (Part A) ⟹ $K := \log N/\log P \le 32000(1+\log\log P)$ for $P \ge P_1$.
2. **(17.47)** (Part B) ⟹ $G \ge 3P/(20\log P)$ for $N > P^{3/2}$, $P \ge P_2$.
3. **Lean:** $a \ge G$ and $(N-P)^{1+a+e} \le B$; so $\log B \ge \frac{3}{20}KP - P$ for $N > P^4$.
4. **`hypothesis-T.md` §7–9** (using 1.): $\log B \le P\bigl(10.6 + \frac{3}{\log2}\log(1+\frac{4K^2}{5c_2})\bigr)$ for $4 < K$, $P \ge P_0$.
5. Combining: $\frac3{20}K \le 11.6 + \frac{3}{\log 2}\log(1+\frac{4K^2}{5c_2})$, $c_2 = 2^{-18}\cdot0.032\cdot0.512\cdot0.64 = 4.0\cdot10^{-8}$.

**Numerical recheck (independent).** Let $g(K) := 0.15K - 11.6 - \frac{3}{\log2}\log(1 + 0.8K^2/c_2)$; for $K \ge 4$,
$K^2/c_2 > 400$, so the max is that term.
- $g$ is **convex** on $[4,\infty)$: $g'' > 0$, because $-\log(1 + aK^2)$ has second derivative $2a(aK^2-1)/(1+aK^2)^2 > 0$
  once $aK^2 > 1$.
- So $\max_{[4,958]}g = \max(g(4), g(958))$, with $g(4) = -95.8 < 0$ and $g(958) = -0.084 < 0$ (computed).
- $g$ is increasing beyond $K \approx 58$, because $g'(K) \approx 0.15 - \frac{6}{K\log2}$, and $g(959) = +0.057 > 0$.

Hence the inequality of point 5 ($g(K) \le 0$) forces $K < K_r$, where $K_r \in (958, 959)$ is the zero of $g$. **So $K_0 = 959$**
($N < P^{959}$). (Correction: a first version claimed monotonicity from $K = 30$ on; that is
false, $g$ decreases up to $\approx 58$; the argument above uses convexity instead.)

> **Theorem W.** There is an effective $P_* = \max(P_0, P_1, P_2)$ such that every restricted-support family with
> $P \ge P_*$ satisfies $N \le P^{959}$.
>
> **Status:** written and self-audited proof, **without any unverified internal dependency on [CC]**. It rests
> only on the published results listed at the top (and in `hypothesis-T.md` §0) and on the Lean identities.
> **Not independently verified.** $P_*$ is not computed and is astronomical ($\log P_* \gtrsim 2.3\cdot10^{23}$, plus the
> thresholds of Part A, which come from Matveev's constant $10^{12}$).

**What is not proved.** The emptiness of the residual region $P < N \le P^{959}$ (Wall II), Williamson, Goldbach.


---

# Part D — Adversarial verification (2026-11-24)

Each point was re-derived, not copied from the previous audits.

**D.1 Hypotheses of the external theorems**
- *Selberg with real weights.* HR Th. 3.2 is stated for sequences; the proof only uses
  $\sum_a w_a\mathbf 1_{(a,\Pi)=1} \le \sum_a w_a(\sum_{d\mid(a,\Pi),\,d<D}\lambda_d)^2$ ($\lambda_1 = 1$), which is linear in $w_a \ge 0$,
  and Selberg's optimal weights satisfy $|\lambda_d| \le 1$ (HR Lemma 3.4). It holds for the weights $\log q$. ✓
- *$G(D) \ge \frac12(\log D - 1)$.* Every odd $n < D$ is $n = dm$ with $d = \mathrm{rad}(n)$ odd squarefree, $d < D$, and the primes of $m$
  dividing $d$. Hence $\sum_{d<D,\ d\ \text{odd}}\mu^2(d)/\varphi(d) = \sum_d\frac{\mu^2(d)}{d}\prod_{p\mid d}(1-\frac1p)^{-1} \ge \sum_{n<D\ \text{odd}}\frac1n \ge \frac12\sum_{n<D}\frac1n$. ✓
- *Matveev–BMS Th. 9:* $\alpha_j$ positive reals in a number field of degree $D$ (here $\mathbb Q$, $D = 1$, factor $D^2(1+\log D) = 1$),
  $b_j \in \mathbb Z$, $\Lambda \ne 0$, $A_j \ge \max\{Dh, |\log\alpha_j|, 0.16\}$, $B \ge \max|b_j|$. All checked in A.5, including the
  omitted factor $C_q/C_r = 1$ ($n = 2$: smaller constant). ✓
- *[MRSTT] 4.1:* rechecked from the downloaded text: $F \ge X^4$, $I \subset [X, 2X]$, (4.2) for $1 \le r \le 10\lceil\log F/\log X\rceil+1$, (4.3).
  Lemma S checks them for $\alpha = 3e$. ✓
- *Brun–Titchmarsh (MV):* modulus $q^a \le (P-3)/2 < P = x$, residue coprime ($q \nmid N$). ✓
- *Vaaler:* valid for every real $x$ with $\psi^*$; the passage $\psi \to \psi^*$ is in `hypothesis-T.md` §7.4. ✓
- *Beurling–Selberg:* $m \le \mathbf 1_J$ pointwise, $\deg m \le K$, $\hat m(0) = |J| - 1/(K+1)$, $|\hat m(h)| \le |J| + 1/(K+1) \le 1$. ✓
- *van der Corput (13.3):* the constant depends on $(k, B)$, with $k \le 6$ and $B \le 3^7$. ✓

**D.2 Asymptotic thresholds (order of magnitude, computed)**

| Step | Condition | Threshold |
|---|---|---|
| A.4 ($R \ge P/4u$) | Rosser–Schoenfeld | moderate |
| A.7, Prop. 14.5 ($\alpha = 3200$, $\beta = 1/16$) | $B_Hk(1+P/h) < P/(16u)$ | $\log P \gtrsim 6.6\cdot10^7$ |
| B.2–B.3 | $L^5e^{-c_*L^3/\Omega^2} \le 2\cdot10^{-9}$, $\Omega \le 32000L(1+\log L)$ | $\log P \gtrsim 6.5\cdot10^{21}$ |
| `hypothesis-T.md` §8 | $\Lambda_K \ge 40\log L$ for $K \le 32000(1+\log L)$ | $\log P \gtrsim 2.3\cdot10^{23}$ |
| `hypothesis-T.md` §9.3 | $10/L \le 0.0597$ | $\log P \ge 168$ |

Every condition compares explicit functions of $P$ with constants that are either explicit or come from published
theorems with effective constants. **$P_* = \exp(O(10^{23}))$ up to the implied constants of van der Corput/MRSTT.**

**D.3 Points checked for circularity**
- Th. 15.1 (Part A) uses neither (17.47) nor Theorem W.
- (17.47) (Part B) uses Th. 15.1 and Prop. 16.3χ; Prop. 16.3χ uses no height bound.
- Theorem W uses Th. 15.1 (bound on $K$), (17.47), the sieve, and Lean. **No cycle.** ✓

**D.4 Points where an argument could break, examined**
- *Prop. 16.3χ, Type I, $k$-range:* $k \le (X/a - \rho)/d \le 2Z$ ✓; lower end $> Z - 1$ ✓.
- *$|Y| \ge X^2/64$ in the sieve:* $N/(4D^2) \ge P^{3.8}$ ✓ (requires $N > P^4$, the only region where the improved sieve is used).
- *For $P^{3/2} < N \le P^4$:* Theorem W is trivial ($K \le 4$). ✓
- *Lemma 14.4:* "interval of length $h$" ⟹ $q_k - q_0 \le h$ ⟹ $V \le h^{k(k+1)/2}$ ✓; the floor $\lfloor h\rfloor$ in Prop. 14.5 is harmless ✓.
- *Definitions:* [CC] families (composite complements) are Lean `BadFamily` families (non-prime complements), so the Lean
  results apply to them. ✓

**Verdict D.** No gap found. Theorem W **survives the adversarial verification**, with the dependencies listed
(published results + Lean). **This is still not an independent verification by a third party.**
