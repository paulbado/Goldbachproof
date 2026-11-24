# Residual region $P^{5/3} < N < P^{959}$: repetition mass, injectivity, and a barrier

Status: **research note.** The lemmas marked "proved" have a written, self-audited proof; R2, R2′, R2″ and the ingredients of L1 also have a Lean proof.
**No pointwise exclusion is obtained.** Wall II, Williamson and Goldbach are **not** proved.

Context: Theorem W (`theorem-W-dependencies.md`) gives $N < P^{959}$ for every restricted-support family
with $P \ge P_*$. [CC] §17.13 gives *exceptional-set* bounds (in $N$) in the bands $P^{3/2} < N \le P^{2-\epsilon}$, and
§19 isolates a fixed-$N$ problem in the band $3/2 \le K \le 5/3$. Here $K := \log N/\log P$, $L := \log P$.

Notation: $M_\ell = N - \ell$ ($\ell \in I = \mathbb P\cap[3,P]$), $S = \mathbb P\cap[3,P)$, $E_q = \max_\ell v_q(M_\ell)$,
$B = \prod M_\ell/\mathrm{lcm}\,M_\ell$, $\mathcal L := \mathbb P\cap(P/2, P)$, $R = |\mathcal L|$,
$a_L$ = the number of primes of $\mathcal L$ absent from every complement, $m = R - a_L$.

---

## 1. Pointwise vs exceptional

- **Pointwise** (for *every* $N$ of a family): Th. 15.1, (17.47), Theorem W, Prop. 16.3χ (uniform in $N$), and the
  lemmas R1–R3 below.
- **Exceptional set** (for all $N$ outside a set of small cardinality): [CC] Th. 17.16. An exceptional-set bound
  **does not exclude** a given $N$. It becomes pointwise only if the exceptional set has fewer than one element,
  which [CC] does not claim.

In the region $K \le 959$, Prop. 16.3χ gives **power** savings that are uniform in $N$:
$\exp(-c_*(\log X)^3/\Omega^2) \le P^{-c_*(4/5)^3/(K+1)^2}$ at scales $X \ge P^{4/5}$. These savings are pointwise.

---

## 2. R1 — exact mass identity (proved, elementary)

For a restricted-support family, $\mathrm{lcm}\,M_\ell = \prod_{q\in S}q^{E_q}$, hence
$$\log B = \sum_{\ell\in I}\log M_\ell - \sum_{q\in S}E_q\log q.\qquad(\mathrm{R1})$$
Put $\delta_q := \log N - E_q\log q$. Then $\delta_q > 0$, because $q^{E_q} \le \max M_\ell < N$. Since $|I| = |S| + 1$,
$\log M_\ell \ge \log A$ and $|S|\log(N/A) \le 2P^2/N$:
$$\log B \ge \log A - \frac{2P^2}{N} + \sum_{q\in S}\delta_q.\qquad(\mathrm{R1}')$$

---

## 3. R2 — cofactor injectivity above $P^2$ (proved; **Lean**: `WilliamsonResidual.cofactor_injective`)

> **Lemma R2.** Let $P \ge 3$, $N \ge P^2$, $q, q' < P$, $b \ge 1$, $C \ge 1$. If $Cq^b$ and $Cq'^b$ both lie in
> $[N-P, N-3]$, then $q = q'$.

*Proof.* Suppose $q' < q$ and put $t = Cq^{b-1}$.
- **Lower bound on $t$:** $qt \ge N - P \ge P(P-1)$ and $q \le P-1$ give $t \ge P$.
- **Gap:** $Cq'^b \le q't \le (q-1)t$, so $Cq^b - Cq'^b \ge t \ge P$.
- **Contradiction:** both numbers lie in an interval of length $P - 3$. $\square$

*Consequence.* For $N \ge P^2$, each present prime $q \in \mathcal L$ divides exactly one row $\ell_q$ (since $2q > P - 3$).
Write $M_{\ell_q} = C_qq^{b_q}$ with $q \nmid C_q$. The map $q \mapsto (b_q, C_q)$ is **injective** on the present primes of $\mathcal L$,
and $b_q \le \beta := \lfloor\log N/\log(P/2)\rfloor \le K + 1$ for $P \ge P'$.

---

## 4. R3 — necessary repetition mass (proved; new)

> **Lemma R3.** For every restricted-support family with $N \ge P^2$ and $P \ge P_3$ (effective):
> $$\log B \ge a_L(K-1)L + R\,(L - 3\log L) - \frac PL - \beta L - 2.$$
> In particular:
> - **(i)** $\log B \ge \bigl(\frac12 - O(\frac{\log L}{L})\bigr)P$, without any analytic input beyond Rosser–Schoenfeld;
> - **(ii)** with (17.47) ($a_L \ge G \ge \frac{3P}{20L}$): $\log B \ge \bigl(0.15K + 0.35 - O(\frac{\log L}{L})\bigr)P$.

*Proof.*
1. **Large primes.** By (R1′), keeping only $q \in \mathcal L$ (every $\delta_q > 0$):
   $\log B \ge \log A - 2 + \sum_{q\in\mathcal L}\delta_q$.
   - absent $q$: $\delta_q = \log N = KL$;
   - present $q$: $\delta_q = \log(N/M_{\ell_q}) + \log C_q \ge \log C_q$.
2. **Present primes ($m$ of them).** By R2, the pairs $(b_q, C_q)$ are distinct with $b_q \le \beta$, so each integer value of
   $C$ is taken at most $\beta$ times. Hence, with $n = \lfloor m/\beta\rfloor$ and $\sum_{c\le n}\log c \ge n\log n - n + 1$,
   $$\sum_{\text{present}}\log C_q \ge \beta\sum_{c\le n}\log c \ge (m-\beta)(\log n - 1).$$
3. **Two cases.**
   - If $m \ge P/L^2$: $\log n \ge L - 2\log L - \log\beta - 2 \ge L - 3\log L + 1$, since $\beta \le K+2 \le L$ for
     $P \ge P_3$ (Theorem W, or Th. 15.1: $K \ll \log L$). So $\sum\log C_q \ge (m-\beta)(L - 3\log L)$.
   - If $m < P/L^2$: then $a_L \ge R - P/L^2$, and $a_LKL \ge a_L(K-1)L + RL - P/L$.
4. **In both cases,** using $a_L + m = R$:
   $\log B \ge a_L KL + m(L - 3\log L) - \beta L - P/L - 2 \ge a_L(K-1)L + R(L - 3\log L) - P/L - \beta L - 2$.
5. **Size of $R$.** Rosser–Schoenfeld Th. 4 ($x(1 - 1/\log x) < \theta(x) < x(1 + 1/(2\log x))$) gives
   $RL \ge \theta(P) - \theta(P/2) \ge P/2 - 1.3P/L$.
6. **Conclusion.** (i) uses $a_L \ge 0$ and $K \ge 1$; (ii) uses $a_L \ge 0.15P/L$. $\square$

*Comparison.* [CC] (17.46) gives $T_{1/10} \ge P/100$ (repeated prime bases, $N > P^{3/2}$). R3(i) gives the total mass
$\log B \ge (1/2 - o(1))P$ as soon as $N \ge P^2$, through a different route: injectivity of the cofactors, not sieving.

**Corollary R3′ (improved height constant).** In the proof of Theorem W, replace the lower bound $\frac3{20}KP - P$ with
R3(ii) $\bigl(0.15K + 0.35 - O(\log L/L)\bigr)P$. The inequality
$0.15K + 0.34 \le 10.6 + \frac{3}{\log2}\log(1 + 0.8K^2/c_2)$ fails for $K \ge 950$ (computed; the same convexity argument as in
`theorem-W-dependencies.md` Part C). So **$N < P^{950}$** for $P \ge \max(P_*, P_3)$. A modest gain, but rigorous.

---

## 4bis. R2′ — near-injectivity below quadratic height (proved; **Lean**: `near_injective`, `card_small_cofactor`)

> **Lemma R2′.** Let $3 \le P \le N$, $q' < q \le P$, $b \ge 1$, $C \ge 1$. If $Cq^b \in [N-P, N-3]$ and $Cq'^b \ge N - P$, then
> $$(q - q')(N - P) \le P(P-3).$$

*Proof.* Put $t = Cq^{b-1}$. Then $Cq'^b \le q't$, so $(q - q')t \le Cq^b - Cq'^b \le P - 3$. Multiplying by $q \le P$ and using
$qt = Cq^b \ge N - P$ gives $(q - q')(N-P) \le (q-q')qt \le P(P-3)$. $\square$
(Neither $q > P/2$ nor $N \ge P^2$ is needed. For $N \ge P^2$ we get $q - q' < 1$, which is R2.)

> **Corollary R2″ (small cofactors).** Let $\Delta := \lfloor P(P-3)/(N-P)\rfloor$. The present primes $q \in \mathcal L$ with
> $C_q \le P^\theta$ number at most $\beta\lfloor P^\theta\rfloor(1 + \Delta)$. **Lean** (`card_small_cofactor`): $\#Q \le (\Delta + 1)\beta C_{\max}$.

*Proof.* Group by the fiber $(b_q, C_q) \in [1,\beta] \times [1, \lfloor P^\theta\rfloor]$. In a fiber, R2′ gives
$\max - \min \le \Delta$, so at most $\Delta + 1$ integers (`card_le_of_gaps`). $\square$

*Uniformity.* For $P^{5/3} \le N \le P^{950}$ and $P$ large: $N - P \ge N/2$ gives $\Delta \le 2P^{2-K} \le 2P^{1/3}$, and
$\beta \le \log N/\log(P/2) \le 951$. So
$$\#\{q \in \mathcal L\ \text{present}: C_q \le P^\theta\} \le 951\,P^\theta(1 + 2P^{1/3}) \le 2853\,P^{\theta+1/3},$$
which is **$o(P/\log P)$ uniformly** in $N$ as soon as $\theta < 2/3$ is fixed. (For $N \ge P^2$, R2 alone gives $\le \beta P^\theta$ for every $\theta < 1$.)

## 4ter. R5 — reinforced repetition mass for $5/3 \le K < 3$ (proved; new)

> **Lemma R5.** Fix $\epsilon \in (0, 1)$. For $P \ge P(\epsilon)$ (effective) and every restricted-support family with
> $5/3 \le K \le 3 - \epsilon$:
> $$\log B \ge \Bigl(\frac{K-1}{2} + 0.15\Bigr)P - 1.3(K-1)\frac{P}{L} - 361\,P^{\max(1/3,\,K-2)}L.$$
> In particular, **uniformly for $5/3 \le K \le 2$: $\log B \ge \bigl(\frac{K-1}{2} + 0.15 - O(1/L)\bigr)P$.**

*Proof (multiplicity counting).*
1. **(R1′).** $\log B \ge \log A - E_1 + \sum_{q\in\mathcal L}\delta_q$, with $E_1 = |S|\log(N/A) \le \pi(P)\cdot2P/N \le 2.6P^{2-K}/L \le 2.6P^{1/3}/L$ (absorbed in the term $P^{\max(1/3,K-2)}L$; *correction: a first version wrote $\le 3$, which is false for $K < 2$*).
2. **Split $\mathcal L$:** absent ($a_L$), present with $E_q = 1$, present with $E_q \ge 2$ ($m_2$).
   - Absent: $\delta_q = KL$.
   - $E_q = 1$: $\delta_q = \log N - \log q > (K-1)L$ (since $q < P$). **No cofactor argument is needed here.**
   - $E_q \ge 2$: $\delta_q > 0$.
3. **Bound on $m_2$.** $C_q < N/(P/2)^{b} = 2^bP^{K-b}$, so for $b = 2$ there are at most $4P^{K-2}$ values of $C$,
   and for $3 \le b \le \beta \le 4$, at most $2^b$ values (since $K < 3$). By R2″ with $\Delta \le 2P^{2-K}$:
   $m_2 \le (1 + 2P^{2-K})(4P^{K-2} + 56) \le 180\,P^{\max(K-2,\,2-K)} \le 180\,P^{\max(1/3,\,K-2)}$.
4. **Summation.** $\sum_{\mathcal L}\delta_q \ge a_LKL + (R - a_L - m_2)(K-1)L = a_LL + R(K-1)L - m_2(K-1)L$.
5. **Inputs.**
   - $a_L \ge G \ge 0.15P/L$ (17.47; `theorem-W-dependencies.md` Part B; $N > P^{3/2}$).
   - $RL \ge \sum_{q\in\mathcal L}\log q \ge \theta(P) - \theta(P/2) - L \ge P/2 - 1.3P/L$ (Rosser–Schoenfeld Th. 4).
   - $\log A \ge 0$.
6. **Uniformity.** For $K \le 3 - \epsilon$, $P^{K-2}L = o(P/L)$ uniformly, and the constants do not depend on $K$. $\square$

**Comparison with R3(ii)** ($0.15K + 0.35$): R5 is better as soon as $K > 2$ (the difference is $0.35K - 0.7$). It coincides
with R3(ii) at $K = 2$. On $[5/3, 2)$ R5 is weaker than R3(ii), whose proof needs $N \ge P^2$ (R2); R5 holds for every
$K \ge 5/3$. **On $[5/3, 2)$, R5 is the only valid mass bound beyond $\frac3{20}KP - P$.** At $K = 5/3$ it gives $0.483P$.

**What is new, and what follows immediately from R2.**
- The small-cofactor count for $N \ge P^2$ (old (O2) candidate): an **immediate consequence of R2**.
- R2′ (below $P^2$): **new**, a quantitative extension of R2's proof.
- R2″: an immediate consequence of R2′ (counting by fibers).
- R5: **new**. The key step is elementary ($E_q = 1 \Rightarrow \delta_q > (K-1)L$); R2′ only controls the exceptional
  primes ($E_q \ge 2$).

## 5. R4 — barrier for budget arguments (proved)

> **Lemma R4.** For $P$ large and every $X \ge P^{5/3}$ (indeed $X \ge PL^2$ suffices), averaging over the even $N \in (X, 2X]$ (with no restricted-support
> hypothesis; $B(N) = \prod_\ell M_\ell/\mathrm{lcm}$ and $v_q(B) = \sum_a(n(q^a)-1)_+$ hold for every $N$):
> $$\mathbb E_N\log B(N) \ge \Bigl(1 - \frac{3\log L}{L}\Bigr)P.$$
> Hence any bound $\log B(N) \le U(P)$ valid **for all** even $N$ in such a range satisfies $U(P) \ge (1 - o(1))P$.

*Proof.* Let $q \le Q_1 := P/L^2$ be an odd prime. As $N = 2n$ runs over $(X, 2X]$, each class $\ell \bmod q$ receives
$X/(2q) + O(1)$ values of $N$, so $\mathbb E\,n_N(q) \ge (\pi(P)-1)(1/q - 2/X) \ge (\pi(P)-1)/q - 2P/X$. *Extension (correction): the proof only uses $X \ge P^2$ in this error term; for $X \ge P^{5/3}$, $\sum_{q\le Q_1}\log q\cdot 2P/X \le 2.1\,PQ_1/X = o(P)$. So R4 holds for every $X \ge P^{5/3}$.* Since $v_q(B) \ge (n(q)-1)_+ \ge n(q) - 1$,
$$\mathbb E\log B \ge \sum_{3\le q\le Q_1}\log q\Bigl(\frac{\pi(P)-1}{q} - 1 - \frac2P\Bigr) \ge (\pi(P)-1)(\log Q_1 - 2) - 1.03Q_1,$$
by Rosser–Schoenfeld ($\sum_{p\le x}\log p/p > \log x - 1.34$, minus $\frac{\log 2}2$ for $p = 2$; $\theta(x) < 1.01624x$). With
$\pi(P) \ge P/L$, this is $\ge P(1 - (2\log L + 2)/L) - O(P/L^2)$. $\square$

**Barrier corollary (scope corrected).** R4 says only this: a bound $\log B(N) \le U(P)$ proved **for every** even $N$ in
the range (the sieve bound of `hypothesis-T.md` is of this type) satisfies $U \ge (1 - o(1))P$. So comparing such a $U$
with the **currently established** structural lower bounds, namely
$\max\bigl(\frac3{20}K - 1,\ 0.15K + 0.35\ (K \ge 2),\ \frac{K-1}{2} + 0.15\ (K < 3)\bigr)P$, can only produce a contradiction if that
maximum exceeds $P$, i.e. **$K > 2.7$** (via R5; before R5 the threshold was $4.26$–$4.33$).

**R4 does not rule out:**
- **(a)** stronger structural lower bounds (more absent primes, finer counting of $\delta_q$);
- **(b)** upper bounds that use the restricted support itself (so not valid for every $N$);
- **(c)** arguments of another type.

It only shows that **for $5/3 < K \le 2.7$, any successful budget argument must improve the structural lower bound
above $P$, or use the restricted support in the upper bound.**

---

## 6. R6 — sawtooth mass bound for $K \ge 2$ (proved), and the corrected scope of (O1)

> **Lemma R6.** Fix $\epsilon > 0$. For $P \ge P(\epsilon)$ and every restricted-support family with $2 \le K < 950$ and
> $\{K\} \le 1 - \epsilon$ (where $n = \lfloor K\rfloor$):
> $$\log B \ge \bigl(0.15(n-1) + \tfrac{1+\{K\}}{2}\bigr)P - O(P/L) - 2^{n+1}P^{1-\epsilon}L.$$

*Proof.* $N \ge P^2$, so $\Delta = 0$ (R2: injectivity). For present $q \in \mathcal L$ with $b = E_q$, $C_q < 2^bP^{K-b}$.
- $b \ge n+1$: impossible, since $2^{n+1}P^{\{K\}-1} \le 2^{951}P^{-\epsilon} < 1$.
- $b = n$: at most $2^nP^{\{K\}}$ primes (distinct $C$).
- $b \le n-1$: $\delta_q \ge KL - (n-1)L = (1+\{K\})L$.

Absent primes: $\delta_q = KL$. As in R5,
$\sum_{\mathcal L}\delta_q \ge a_L(n-1)L + R(1+\{K\})L - 2^{n+1}P^{\{K\}}L$, with $a_LL \ge 0.15P$, $RL \ge P/2 - 1.3P/L$, $E_1 \le 3$. $\square$

For $n = 2$ this is R5; when $\{K\} \to 0$ it coincides with R3(ii); and it is always $\ge$ R3(ii) (by $0.35\{K\}$).

**Corrected scope of the structural lower bounds** ($\log B \ge \lambda(K)P - o(P)$):

| Range of $K$ | $\lambda(K)$ | Source |
|---|---|---|
| $[5/3, 2)$ | $\frac{K-1}{2} + 0.15$ | R5 |
| $[2, 950)$, $\{K\} \le 1-\epsilon$ | $0.15(\lfloor K\rfloor - 1) + \frac{1+\{K\}}2$ | R6 (contains R5 on $[2, 3-\epsilon]$) |
| $[2, 950)$, $\{K\} > 1-\epsilon$ | $0.15K + 0.35$ | R3(ii) |

**(O1), corrected.** A universal bound (R4: $U \ge (1-o(1))P$) can contradict $\lambda(K)$ only where $\lambda(K) > 1$, i.e. outside
$$\mathcal Z_{\mathrm{blocked}} = [5/3,\ 2.7]\ \cup\ (3-\epsilon,\ 3.4]\ \cup\ (4-\epsilon,\ 4.1].$$
**Outside $\mathcal Z_{\mathrm{blocked}}$ (and $K < 950$), the obstruction is the constant:** we would need a universal $U \le (\lambda(K) - \eta)P$,
which is within a factor $\lambda(K)$ of the average order ($\approx P$, R4), whereas the sieve of `hypothesis-T.md` gives $C_0(1+\log K)P$ with
$C_0 \approx 10$. Closing it requires an asymptotic for $S_Q(N)$ (an EH-type statement for a fixed residue, at level $1-o(1)$).

---

## 7. Below $P^2$: powersmooth rows, an anomaly theorem, and an exact reduction

Throughout this section $5/3 \le K \le 2 - \epsilon$. Put $L_P := \mathrm{lcm}(1,\dots,P)$ and
$$\mathcal M(N) := \sum_{d\le P}\Lambda(d)\,n_N(d) = \sum_{\ell\in I}\log\gcd(N-\ell, L_P).$$
(The identity holds because $\sum_{d\mid m,\ d\le P}\Lambda(d) = \sum_q\log q\min(v_q(m), \lfloor\log_qP\rfloor) = \log\gcd(m, L_P)$.)

### 7.1 L1 — the rows are powersmooth (proved; Lean: `high_power_unique_row`, `powersmooth_dvd_lcm`)

> **Lemma L1.** For a restricted-support family with $N - P > P^{3/2}$, at most $(2L+1)P^{K-1} + \sqrt{2P}$ rows $\ell$
> satisfy $N - \ell \nmid L_P$. Every other row divides $L_P$.

*Proof.*
- **Bad rows.** If $M_\ell \nmid L_P$, some $q^{v} \Vert M_\ell$ has $q^v > P$, with $q < P$ (restricted support), so $v \ge 2$
  (Lean `powersmooth_dvd_lcm`, contrapositive). Let $a$ be minimal with $q^a > P$: then $a \ge 2$, $q^a \le Pq < P^2$, $q^a \mid M_\ell$.
  By `high_power_unique_row`, $t = q^a$ divides only this row, so bad rows inject into such pairs $(q, a)$.
- **$a = 2$ ($q > \sqrt P$).** Write $M_\ell = kq^2$ with $1 \le k < N/P$. For fixed $k$, $q$ lies in an interval of length
  $\sqrt{N/k} - \sqrt{(N-P)/k} \le P/(2\sqrt{k(N-P)})$, so at most $1 + P/(2\sqrt{k(N-P)})$ values. Summing over $k < N/P$:
  $\le N/P + \frac{P}{2\sqrt{N-P}}\cdot2\sqrt{N/P} \le P^{K-1} + \sqrt{2P}$.
- **$a \ge 3$.** $M_\ell = kq^a$ with $k < N/P$. For fixed $(k, a)$, $q$ lies in an interval of length
  $\le P/(a k^{1/a}(N-P)^{1-1/a}) \le P/(N-P)^{2/3} < 1$, so at most one $q$. Moreover $a \le 1 + L/\log 2 \le 2L$.
  At most $2L\cdot P^{K-1}$. $\square$

**Consequence.** $H_{\mathrm{high}} := \sum_\ell\sum_{d\mid M_\ell,\ d>P}\Lambda(d) \le \#\{\text{bad rows}\}\cdot\log N \le ((2L+1)P^{K-1} + \sqrt{2P})KL = o(P)$,
uniformly for $K \le 2 - \epsilon$.

### 7.2 Anomaly theorem (proved)

> **Theorem A.** For every restricted-support family with $5/3 \le K \le 2 - \epsilon$ and $P \ge P(\epsilon)$:
> $$\mathcal M(N) \ge KP - O\bigl(KL^3P^{K-1} + KL\sqrt P + P/L\bigr) = (K - o(1))P.$$
> On the other hand, for every $X \ge P^{5/3}$, the average of $\mathcal M(N)$ over the even $N \in (X, 2X]$ is $P(1 + O(1/L))$.

*Proof.*
- **Lower bound.** $\sum_\ell\log M_\ell = \sum_\ell\sum_{d\mid M_\ell}\Lambda(d) = \mathcal M(N) + H_{\mathrm{high}}$ and $\sum_\ell\log M_\ell \ge |I|\log A \ge KP - O(P/L + KL)$
  (Rosser–Schoenfeld), so L1 gives the bound.
- **Average.** For odd $d \le P$, $\Pr_N(N \equiv \ell\ (d)) = 1/d + O(d/X)$ (for even $d$, $n(d) = 0$). Hence
  $\mathbb E\,\mathcal M = |I|\sum_{d\le P\ \text{odd}}\Lambda(d)/d + O(|I|P\log P/X) = \pi(P)(L + O(1)) + o(1) = P(1 + O(1/L))$ (Mertens). $\square$

**Reading.** A restricted-support family in $5/3 \le K < 2$ forces $\mathcal M(N)$ to be at least $K \ge 5/3$ times its average:
**every row, in mass, must divide $L_P$**, whereas a typical row shares only about $1/K$ of its mass with $L_P$. Numerical check
($P \in \{1009, 4001, 10007\}$, random $N \approx P^{1.7}, P^{1.9}$): $\mathcal M(N)/P \approx 0.87$–$0.96$, versus the $1.7$–$1.9$ required.

> **Corollary B (conditional exclusion, rigorous).** If, for an interval $J \subset [5/3, 2-\epsilon]$ and some $\eta > 0$, every even $N$
> with $\log N/\log P \in J$ satisfies $\mathcal M(N) \le (K - \eta)P$, then **no restricted-support family has its height in
> $J$**, for $P$ large.

### 7.3 Exact reduction to a level of distribution (derivation)

$\mathcal M = \mathcal M_{\le D_0} + \mathcal M_{>D_0}$, with $D_0 = \sqrt P/L^B$.

**Small moduli.** Bombieri–Vinogradov, applied with the max over residues (hence pointwise in $N$), gives
$\mathcal M_{\le D_0} \le \pi(P)\sum_{d\le D_0}\Lambda(d)/\varphi(d) + O(P/L^A) \le (\frac12 + O(\frac{\log L}{L}))P$.
(The BV constant is ineffective because of Siegel–Walfisz; this affects only the effectivity of the threshold.)

**Large moduli.** It suffices to show
$$\mathcal M_{>D_0} = \sum_{D_0<q\le P}\log q\,n(q) + o(P) \le (K - \tfrac12 - \eta)P\qquad(\ge (\tfrac76 - \eta)P),$$
whose average is $\frac12P$. **This is an upper bound within a factor $2K-1 \ge 7/3$ of the truth.** In particular, **parity is not the
obstruction**: Selberg's sieve loses a factor exactly $2/\lambda$ at level $D^2 = P^\lambda$.

> **Proposition C (sufficient condition; derivation, with the Selberg bookkeeping of `hypothesis-T.md` §8).** Suppose that for
> every dyadic $Q \in [D_0, P]$ and every even $N$ with $K \in J$, the dual sequence $\mathcal A_Q(N) = \{N - bq\}$ of
> `hypothesis-T.md` §7 satisfies
> $$\sum_{d<P^\lambda,\ d\mid\Pi}\tau_3(d)|r_d(Q,N)| \le P/L^3\qquad(\mathrm{LD}_\lambda)$$
> with $\lambda > 2/(2K-1)$ for all $K \in J$. Then the hypothesis of Corollary B holds, so $J$ is excluded.

*Derivation.* Selberg at level $D = P^{\lambda/2}$: $S_Q \le \mathcal X/G(D) + P/L^3$ with $\mathcal X \le \frac P2(\log 2 + O(1/L))$ and
$G(D) \ge \frac{\lambda L}{4}(1 - o(1))$, so $S_Q \le \frac{2\log 2}{\lambda}\frac PL(1+o(1))$. There are $\le \frac{L}{2\log2} + O(\log L)$ scales, so
$\mathcal M_{>D_0} \le \frac P\lambda(1 + o(1)) < (K - \frac12 - \eta)P$. $\square$

**Level required:** $\lambda > 6/7$ at $K = 5/3$, $\lambda > 2/3$ as $K \to 2$.
**Level proved** (`hypothesis-T.md`, Prop. 16.3χ + Parseval): $D^3 \approx X_Q\,P^{c_2/K^2}$, i.e. $\lambda \approx \frac23\bigl(\frac{\log X_Q}{L} + \frac{c_2}{K^2}\bigr) \le \frac13 + 10^{-8}$,
and $\to 10^{-8}$ for $Q$ close to $P$.

### 7.4 Why the missing step is difficult

For $d > X_Q$ (beyond the trivial level), $r_d$ detects whether the short interval $\mathcal I_q$ (length $\approx X_Q$) meets the class
$N\bar q \bmod d$. Controlling $\sum_d\tau_3|r_d|$ up to $d \approx P^{6/7}$ requires equidistribution of $N\bar q \bmod d$ as $q$ runs over
the primes $\sim Q$, **jointly** with the reciprocal phase $hN/(2dq)$ of height $\approx P^K/d$. That means sums of the form
$$\sum_{q\sim Q}\log q\;e\Bigl(\frac{a\bar q}{d} + \frac{Y}{dq}\Bigr),\qquad d \le P^{6/7},\ Q \in [\sqrt P, P],\ Y \approx P^K:$$
incomplete Kloosterman sums over primes twisted by a high-height reciprocal phase, with modulus up to $P^{6/7}$, possibly larger
than $Q$. The known bounds for Kloosterman sums over primes (Fouvry–Michel, Bourgain–Garaev, Irving type) require $Q$ to be large
compared with $d$ and do not treat the additional phase. Our method (characters + Parseval) loses $\sqrt d$ and caps the level at
$\approx X_Q^{2/3}$. **This is the exact missing estimate:** $(\mathrm{LD}_\lambda)$ with $\lambda > 2/(2K-1)$, uniformly for $Q \in [\sqrt P, P]$
and fixed $N$.

---

## 8. Summary (updated)

| Result | Status | New / consequence |
|---|---|---|
| R1 mass identity | proved | elementary |
| R2 injectivity ($N \ge P^2$) | proved, Lean | new |
| R2′ near-injectivity | proved, Lean | new (extends the proof of R2) |
| R2″ small cofactors | proved, Lean | immediate consequence of R2′ |
| R3, R3′ ($N < P^{950}$) | proved | new |
| R4 average barrier ($X \ge P^{5/3}$) | proved | new; scope: comparisons with the **current** structural bounds |
| R5 ($5/3 \le K < 3$), R6 ($K \ge 2$, $\{K\} \le 1-\epsilon$) | proved | new |
| L1 powersmooth rows ($K < 2$) | proved; Lean ingredients | new |
| Theorem A (anomaly $\mathcal M \ge K\cdot$average) | proved | new |
| Corollary B (conditional exclusion) | proved | — |
| Proposition C ($\mathrm{LD}_\lambda$, $\lambda > 2/(2K-1)$ ⟹ exclusion) | derivation | — |

**No pointwise exclusion is obtained.** The question is reduced, on $5/3 \le K < 2$, to a single level-of-distribution estimate for
the dual sequences, $(\mathrm{LD}_\lambda)$ with $\lambda > 6/7$ (resp. $2/3$), which **is not proved**. **Wall II remains open.**
