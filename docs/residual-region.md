# Residual region $P^{5/3} < N < P^{959}$: repetition mass, injectivity, and a barrier

Status: **research note.** The lemmas marked "proved" have a written, self-audited proof; R2, R2′, R2″, MR and the ingredients of L1 also have a Lean proof.
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
$X/(2q) + O(1)$ values of $N$, so $\mathbb E\,n_N(q) \ge (\pi(P)-1)(1/q - 2/X) \ge (\pi(P)-1)/q - 2P/X$
(using $\pi(P) - 1 \le P$). Since $v_q(B) \ge (n(q)-1)_+ \ge n(q) - 1$,
$$\mathbb E\log B \ge \sum_{3\le q\le Q_1}\log q\Bigl(\frac{\pi(P)-1}{q} - 1 - \frac{2P}{X}\Bigr) \ge (\pi(P)-1)(\log Q_1 - 2) - 1.03\,Q_1 - 2.1\,\frac{PQ_1}{X},$$
by Rosser–Schoenfeld ($\sum_{p\le x}\log p/p > \log x - 1.34$, minus $\frac{\log 2}2$ for $p = 2$; $\theta(x) < 1.01624x$,
so $\frac{2P}{X}\theta(Q_1) \le 2.1\,PQ_1/X$). The last term is $2.1\,P^2/(L^2X)$: it is $\le 2.1\,P^{1/3}/L^2$ for
$X \ge P^{5/3}$ and $\le 2.1\,P/L^4$ for $X \ge PL^2$, so $o(P/L)$ in both cases. (This is the only place where the size
of $X$ enters; earlier versions stated R4 for $X \ge P^2$ and wrote this error as $2/P$, which is its value at $X = P^2$
only.) With $\pi(P) \ge P/L$ and $\log Q_1 = L - 2\log L$, the right side is $\ge P(1 - (2\log L + 2)/L) - O(P/L^2)
\ge (1 - 3\log L/L)P$ for $P$ large. $\square$

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
- **Average.** For odd $d \le P$, $N = 2n$ with $n \in (X/2, X]$ and $2n \equiv \ell\ (d)$ is one class of $n$ mod $d$, so
  $\Pr_N(N \equiv \ell\ (d)) = 1/d + O(1/X)$, uniformly in $d \le P \le X$ (for even $d$, $n(d) = 0$). Hence
  $\mathbb E\,\mathcal M = |I|\sum_{d\le P\ \text{odd}}\Lambda(d)/d + O(|I|\psi(P)/X) = \pi(P)(L + O(1)) + O(P^2/(LX)) = P(1 + O(1/L))$
  (Mertens; $P^2/(LX) \le P^{1/3}/L$). *(Audit correction: an earlier version wrote the per-modulus error as $O(d/X)$ and
  the total as $o(1)$; summed over $d \le P$ that would give $O(P^3/(LX))$, which is not $o(P)$ at $X = P^{5/3}$. The error is
  $O(1/X)$ per modulus and the total is $O(P^{1/3}/L)$; the conclusion is unchanged.)* $\square$

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
**Level proved — scope corrected.** `hypothesis-T.md` §7–8 derives $D^3 \approx X_Q\,\mathcal E_Q^{-1}$ from Prop. 16.3χ + Parseval.
That derivation assumes $K > 4$ and $Q \le P/4$, which guarantee $|Y| = h(N-3)/(2d) \ge X^2/64$ for every $d < D^2$
($X = 2Q$). For $5/3 \le K < 2$ this condition reads $d \le 32hN/X^2$, so:
- **Scales $Q \le c\sqrt{N/d}$:** Prop. 16.3χ applies; the level is $\lambda \approx \frac23\bigl(\frac{\log X_Q}{L} + c(K)\bigr)$, with $c(K) \asymp c_*/K^2$
  tiny. These scales have $X_Q \ge P^{1-K/2}/c$.
- **Scales $Q > c\sqrt N$** (for $K < 2$ this includes every $Q \in (6P^{K/2}, P]$): Prop. 16.3χ does not apply even for $d = 1$.
  - *Update.* Proposition 16.2χ (`prop-16-2-chi-top-range.md`, proved) now covers the twisted sums for every $d \le X^{1/10}$ and
    $|Y| \le X^2$, with saving $X^{-1/248}$.
  - With the character-expansion loss, this supports at most a level of order $P^{c}$ with $c$ about $10^{-3}$. That is a rough estimate,
    not written out.
  - **No level anywhere near $2/(2K-1)$ is established at these scales.**

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

### 7.5 Audit of L1, Theorem A and Proposition C

**L1.** Checked line by line. Points worth recording:
- **Where each hypothesis enters.** The counting argument uses only $q < P$ and $N - P > P^{3/2}$. The bound $N - P > P^{3/2}$ is
  used in the case $a \ge 3$ only, through $(N-P)^{2/3} > P$. Restricted support is used **only** to say that the large prime power
  $q^v > P$ comes from a prime $q < P$. So the count of rows with an excess prime power holds **for every $N$** (Lemma E below).
- **Multiplicities.** A row with several excess prime powers is charged to one of them; that is an injection into pairs $(q, a)$,
  hence an upper bound. $H_{\mathrm{high}}$ charges a bad row its whole mass $\log M_\ell \le \log N$, which covers all of its prime powers.
- **Endpoints.** The $q$-intervals are closed, and a closed interval of length $\lambda$ contains at most $\lfloor\lambda\rfloor + 1$
  integers. Then $\sum_{k<N/P}k^{-1/2} \le 2\sqrt{N/P}$, and $\sqrt{PN/(N-P)} \le \sqrt{2P}$ for $N \ge 2P$. The bound $a \le 1 + L/\log 2 \le 2L$
  holds for $P \ge 8$. $\ell = P$ is allowed when $P$ is prime.
- **Uniformity.** The error is uniform in $K \in [5/3, 2-\epsilon]$: $KL^2P^{K-1} \le 2L^2P^{1-\epsilon}$.

**Theorem A.**
- **Lower bound.** Correct. It uses $\pi(P) - 1 \ge P/L - 1$ (Rosser–Schoenfeld, $P \ge 17$) and
  $\log(N-\ell) \ge \log N - 2P/N$. The stated error $O(KL^3P^{K-1})$ can be lowered to $O(KL^2P^{K-1})$; this is harmless.
- **Average.** Corrected: the error per modulus is $O(1/X)$, not $O(d/X)$ (see the proof above).
- **Prime powers.** They are included in $\Lambda$ on both sides; even moduli contribute $0$ because $N - \ell$ is odd.

**Proposition C.** The derivation is correct as a conditional statement. Its caveats are now explicit:
- **(a) Small moduli.** BV with $\max_a$ is pointwise in $N$. Moduli with $\gcd(d, N) > 1$ have $n(d) \le 1$, since
  $\ell \equiv N \equiv 0 \pmod q$ forces $\ell = q$; they contribute $O(\sqrt P)$. The window $D_0 < d \le \sqrt P$, which was omitted
  before, is handled by Brun–Titchmarsh: $\sum_{D_0<d\le\sqrt P}\Lambda(d)\,2P/(\varphi(d)\log(P/d)) = O(P\log L/L)$.
- **(b) Ineffectivity.** BV is ineffective (Siegel), so $P_0$ is ineffective. Replacing BV by Brun–Titchmarsh on $d \le \sqrt P$
  costs $2\log 2\cdot P \approx 1.39P$ instead of $P/2$. The requirement would become $1/\lambda < K - 1.39$, which forces $\lambda > 1$:
  **BV (or an effective substitute with constant $< K - 1$) is indispensable.**
- **(c) Prime powers.** For $q^j > D_0$ with $j \ge 2$, the contribution is $\ll P/\sqrt{D_0} + \sqrt P\,L = o(P)$.
- **(d) Moduli $d$ with $q \mid d$.** If $q \mid d$, an element $N - bq$ is $\equiv N \pmod q$, so it is divisible by $q$ only if $q \mid N$.
  Assigning the density $1/d$ anyway puts a discrepancy $O(\log q\,|I_q|/d)$ into $r_d$. Summed with $\tau_3$, it is
  $O(PL^5/Q) = O(\sqrt P\,L^5)$ for $Q \ge \sqrt P$. It is absorbed in $(\mathrm{LD}_\lambda)$.
- **(e) Small primes $\ell$.** The sieve discards the primes $\ell < D$ themselves. They are added back separately:
  $\sum_{\ell<D}\#\{q > D_0 : q \mid N - \ell\}\cdot L \le \pi(D)\cdot\frac{KL}{\log D_0}\cdot L = O(DL) = o(P)$.
- **(f) Rounding at $d = 1$ (corrected).** The Selberg main term must be the smooth size $\mathcal X = \sum\log q\,\frac{P-3}{2q}$.
  The rounding $\sum_q\log q\,(|I_q| - \frac{P-3}{2q})$ is then the remainder $r_1$. For $Q \ge P/L^3$ it is not trivially small: it is a
  sum of sawtooth values over **primes** $q$.
  - **The earlier version was wrong to cite Lemma S.** Lemma S (`hypothesis-T.md` §2) bounds **unweighted sums over integers**
    $\sum_k e(A/(k+s))$. It is an ingredient inside the proof of Prop. 16.3χ, not an estimate for sums over primes.
  - **Conditional control.** $(\mathrm{LD}_\lambda)$ contains the term $d = 1$, so Proposition C as a conditional statement is unaffected.
  - **Independent control.** The prime-sum estimates that apply are the following.
    - *Setup.* Use blocks $\mathcal J = (3X/4, X]$ instead of dyadic blocks; there are $L/\log(4/3) + O(1)$ of them, each with
      $\mathcal X = \frac P2(\log\frac43 + O(1/L))$, so the product, and hence $P/\lambda$, is unchanged. Vaaler (as in `hypothesis-T.md` §7.4, $d = 1$)
      reduces $r_1$ to $S(Y) = \sum_{q\in\mathcal J}\log q\,e(Y/q)$ with $Y = \pm h(N-3)/2$ or $\pm h(N-P)/2$, $1 \le h \le H := L^2$, plus
      $O(X/H + KL)$. Replacing primes by $\Lambda$ costs $O(\sqrt X L)$.
    - *Case A: $|Y| \ge X^2/64$.* Prop. 16.3χ with $\chi$ trivial gives $\ll XL^5(X^{-1/310} + e^{-c_*(\log X)^3/\Omega^2})$, with
      $\Omega \le (K+1)L$ and $\log X \ge L/2 - 1$. That is a power saving $P^{-c'}$.
    - *Case B: $|Y| < X^2/64$.* This occurs exactly at scales $X > \sqrt{32(N-P)}$, which exist for $K < 2$. Then
      $T := |Y|/X$ satisfies $(\log X)^{32} \le P^{2/3}/3 \le T \le X/64$. Proposition 16.2χ with $d = 1$ (`prop-16-2-chi-top-range.md`,
      an independent proof) gives $|S| \ll X(L^4T^{-1/2} + L^4X^{-1/248})$. Prop. 16.2 of [CC] (audited in `theorem-W-dependencies.md` B.2)
      gives the same shape; it is no longer needed.
    - *Total.* In both cases $|r_1| \ll X/L^2$ per block, hence $O(P/L^2)$ over all blocks. **So $r_1$ is controlled independently of
      $(\mathrm{LD}_\lambda)$.**
  - **Status of the inputs.** Propositions 16.2χ and 16.3χ have written, self-audited proofs.
  - **What is not covered.** For $d > 1$ the same computation needs $\sum\Lambda(n)\chi(n)e(Y/n)$ with $Y = hN/(2d)$. Proposition 16.2χ supplies
    this only for $d \le X^{1/10}$, with a saving too small for a large level. So the terms $d > 1$ up to $P^\lambda$ rest on
    $(\mathrm{LD}_\lambda)$ (see the corrected "Level proved" in §7.3).
- **(g) Selberg remainder.** $\sum_{d_1,d_2<D}|\lambda_{d_1}\lambda_{d_2}||r_{[d_1,d_2]}| \le \sum_{d<D^2}\tau_3(d)|r_d|$, since $|\lambda_d| \le 1$.
- **(h) Main term.** $G(D) \ge \sum_{d<D,\ (d,2)=1}\mu^2(d)/\varphi(d) \ge \frac12\log D$, by the classical
  $\sum_{d<x,(d,k)=1}\mu^2(d)/\varphi(d) \ge \frac{\varphi(k)}k\log x$.
- **(i) Dyadic summation.** There are $\lceil\log_2(P/D_0)\rceil \le \frac{L}{2\log 2} + O(\log L)$ blocks; the last, partial block only
  has fewer elements. Summing gives $\frac P\lambda(1+o(1))$.

**Verdict.** $(\mathrm{LD}_\lambda)$ with $\lambda > 2/(2K-1)$, uniformly over dyadic $Q \in [D_0, P]$ and over $N$ in the band, does
suffice. The exclusion is then valid for $P \ge P_0$, with $P_0$ ineffective.

**Plausibility of $(\mathrm{LD}_\lambda)$.** Square-root cancellation $|r_d| \approx (\mathcal X/d)^{1/2}$ gives
$\sum_{d<P^\lambda}\tau_3(d)|r_d| \approx P^{(1+\lambda)/2}L^2$, which is $\le P/L^3$ for every $\lambda < 1$. The heuristic covers the
supremum over $N$ (subgaussian tails, $P^K$ values). **It is not a theorem.**

### 7.6 Lemma E — the mass decomposition holds for every $N$ (proved)

> **Lemma E.** Let $P \ge 17$ and let $N$ be even, with $N - P > P^{3/2}$ and $N < P^2$. Put $e_q := \lfloor\log_q P\rfloor$. Define
> $$H_{\mathrm{pow}}(N) := \sum_{\ell\in I}\sum_{q\le P}\log q\,(v_q(M_\ell) - e_q)_+,\qquad
>   H_{\mathrm{big}}(N) := \sum_{p>P}\log p\;n_N(p).$$
> **No restricted-support hypothesis is made.** Then:
> 1. $\sum_{\ell\in I}\log(N-\ell) = \mathcal M(N) + H_{\mathrm{pow}}(N) + H_{\mathrm{big}}(N)$ (exact).
> 2. $0 \le H_{\mathrm{pow}}(N) \le \bigl((2L+1)P^{K-1} + \sqrt{2P}\bigr)KL$.
> 3. $N$ carries a restricted-support family if and only if $H_{\mathrm{big}}(N) = 0$ and $n_N(P) = 0$.
>
> Consequently, for every even $N$ with $P^{5/3} \le N \le P^{2-\epsilon}$,
> $$H_{\mathrm{big}}(N) + n_N(P)\log P = (\pi(P)-1)\log N - \mathcal M(N) + O_\epsilon\bigl(KL^2P^{K-1} + KL\sqrt P\bigr).$$
> **Restricted support is the case where $\mathcal M(N)$ reaches its trivial maximum $\sum_\ell\log(N-\ell) - H_{\mathrm{pow}}$.**

*Proof.*
- **Part 1.** Write $\log M = \sum_q v_q\log q$ and split each $q \le P$ as $\min(v_q, e_q) + (v_q - e_q)_+$. The first parts sum to
  $\log\gcd(M, L_P)$. Primes $p > P$ appear with $v_p \le 1$, because $p^2 > P^2 > N$.
- **Part 2.** The L1 injection $\ell \mapsto (q, e_q + 1)$ and its count use neither restricted support nor anything except $q < P$
  (for $q = P$ we have $v_P \le 1 = e_P$). Each bad row contributes at most $\log N$.
- **Part 3.** Restricted support means that every prime factor of every $M_\ell$ is $< P$, i.e. $n(p) = 0$ for every $p \ge P$.
  Compositeness is automatic, because $M_\ell \ge N - P > P$ and all its prime factors are $< P$.
- **Last display.** $\sum_\ell\log(N-\ell) = (\pi(P)-1)\log N - O(P^2/(NL))$. $\square$

**Reading.** A family exists at $N$ exactly when **no** row has a prime factor $\ge P$. By Lemma E the analytic form of this is
"$\mathcal M(N)$ is maximal". Excluding $N$ is equivalent to showing that **one** row $N - \ell$ ($\ell \le P$ prime) has
$P^+(N-\ell) \ge P$. Analytic methods can only prove the quantitative version $H_{\mathrm{big}}(N) \ge \eta P$. That version
is Lemma Ω (§7.10).

### 7.7 Corollary R7 — repetition mass below $P^2$ (proved)

> **R7.** For every restricted-support family with $5/3 \le K \le 2 - \epsilon$ and $P \ge P(\epsilon)$:
> $$\log B \ge KP - \psi(P) - o(P) = (K - 1 - o(1))P\qquad(\ge (K - 1.039)P - o(P)\ \text{explicitly}).$$

*Proof.*
- $\mathrm{lcm}(M_\ell) \mid \mathrm{lcm}(\text{good rows})\cdot\prod_{\text{bad}}M_\ell$, and each good row divides $L_P$ (L1).
  So $\log\mathrm{lcm} \le \psi(P) + \#\text{bad}\cdot\log N = \psi(P) + o(P)$.
- $\sum\log M_\ell \ge KP - O(KL)$ (Theorem A's lower bound), and $\psi(P) < 1.03883P$ (Rosser–Schoenfeld). $\square$

**Comparison.**
- R7 beats R5 on all of $[5/3, 2)$: $K - 1 > \frac{K-1}2 + 0.15 \iff K > 1.3$. At $K = 5/3$: $0.667$ vs $0.483$; as $K \to 2$: $1$ vs $0.65$.
- **It does not escape R4.** $(K - 1)P < P \le \mathbb E\log B$ for $K < 2$. The barrier is met only in the limit $K \to 2$.
  This is consistent: R7 is a consequence of Theorem A, whose content is "$\mathcal M \ge KP$", while the average of $\log B$ is $\approx P$.

### 7.8 Multiplicative rigidity (proved; **Lean**: `mult_rigidity`, `mult_near_rigidity_int`) — and why it cannot help

> **Lemma MR.**
> 1. If $N > P^2$, $0 \le a, b, c, d \le P$ and $(N-a)(N-b) = (N-c)(N-d)$, then $\{a, b\} = \{c, d\}$.
> 2. For any $N \ge 0$, the same equation implies $N\cdot|(a+b) - (c+d)| \le P^2$.

*Proof.* Expanding, $N\bigl((a+b) - (c+d)\bigr) = ab - cd$ and $|ab - cd| \le P^2$. If $N > P^2$, the sums agree, hence so do the
products, so $(a - c)(a - d) = 0$. $\square$ (Lean: `WilliamsonResidual.mult_rigidity`, `mult_near_rigidity_int`, standard
axioms only.)

**Consequences.**
- Above $P^2$, the multiplicative energy of the rows, $\#\{M_aM_b = M_cM_d\}$, is the trivial $2|I|^2 - |I|$.
- Below $P^2$, a non-trivial coincidence needs $1 \le |s| \le P^2/N \le P^{1/3}$ with $Ns = ab - cd$.

**Test against Theorem A (negative).** MR holds for **every** $N$, with or without restricted support. It constrains products of
rows among themselves. It says nothing about $\gcd(M_\ell, L_P)$, which is what Theorem A requires to be maximal. A family of
rows each dividing $L_P$ can have minimal mutual multiplicative energy, and generic $N$ do too. **Multiplicative energy
among rows cannot bound $\mathcal M(N)$ from above, and cannot bound $H_{\mathrm{big}}(N)$ from below.**

### 7.9 Failed routes, each tested against Theorem A

The test is the following. A route can exclude a band only if it yields, **for every $N$ in the band**, either
$\mathcal M(N) \le (K - \eta)P$ or $H_{\mathrm{big}}(N) > 0$. If a route's inequality is equally true for generic $N$ and for
restricted-support $N$, its bound must exceed $\max_N\mathcal M(N)$.

**(i) Divided differences / gcd–lcm.**
- *Identity.* For distinct $\ell_1, \dots, \ell_s$, the divided difference of $f(x) = 1/(N-x)$ gives
  $$\sum_i\frac1{M_{\ell_i}\prod_{j\ne i}(\ell_i - \ell_j)} = \pm\frac1{\prod_iM_{\ell_i}},$$
  so $\mathrm{lcm}(M)\cdot D_P \ge \prod_\ell M_\ell$, with $D_P := \mathrm{lcm}_i\prod_{j\ne i}|\ell_i - \ell_j|$ depending only on $P$.
- *With restricted support.* L1 gives $\log\mathrm{lcm} \le \psi(P) + o(P)$, so $KP \le \psi(P) + \log D_P + o(P)$.
- *Numerically.* `scripts/residual_numerics.py` gives $\log D_P/P = 1.45, 1.57, 1.63$ for $P = 1009, 4001, 10007$, and it is increasing.
  The reason is that $v_p(D_P) = \max_i\sum_{a\ge1}(\#\{j : \ell_j \equiv \ell_i \bmod p^a\} - 1)$ is $\ge 1$ for almost every prime
  $p < P$ that is a difference of two primes. So the route excludes nothing below $K \approx 2.6$.
- *Structural reason.* The identity encodes only $\gcd(M_i, M_j) \mid \ell_i - \ell_j$. That holds for every $N$, and it is used
  with a $\max$ over $i$ that wastes it.

**(ii) Multiplicative energy.** Covered by §7.8 (negative).

**(iii) Exponent-vector combinatorics / dense divisor sets of $L_P$.**
- A good row is a divisor of $L_P$ lying in $[N-P, N]$. The divisors of $L_P$ are the $P$-powersmooth numbers. Below $P^2$ their
  local density near $N$ is $\approx\rho(K) = 1 - \log K \in [0.31, 0.49]$, so every window of length $P$ contains $\gg P$ of them.
- Requiring $\pi(P)$ of them at the shifted primes has "probability" $\rho(K)^{\pi(P)}$. That heuristic explains why no
  family exists, but turning it into a proof is the problem itself (correlations).
- No counting contradiction: there are enough candidates in every window.

**(iv) Primitive divisors and ownership.**
- The private-certificate identities (17.1) and (17.6) and R1–R3 control $\log B$ from below.
- R4 shows that lower bounds of size $\le P$ for $\log B$ cannot contradict universal upper bounds. R7 is the best of this type
  below $P^2$, and it stays $< P$.

**(v) Pointwise Brun–Titchmarsh / Sylvester–Erdős type.**
- Using $n(q) \le \pi(P; q, N)$ and Montgomery–Vaughan $\pi(x; q, a) \le 2x/(\varphi(q)\log(x/q))$, together with
  $n(q) \le (P-3)/q + 1$ for $q > P/e^2$, gives **for every $N$** (effective):
  $$\mathcal M(N) \le 2P\log L + O(P).$$
- This is the Sylvester–Erdős argument restricted to prime positions. It misses $(K-\eta)P$ by a factor $\asymp\log\log P$.
- **Correction (2026-11-25): this bound is weaker than the trivial one.** For every $N$, $\mathcal M(N) \le \sum_\ell\log(N-\ell) \le (K + o(1))P$.
  By Lemma E and BV, $\Sigma_{\mathrm{large}}(N) \le (K - \frac12 + o(1))P$ (`distribution-profile.md`, Lemma T). So the bound $2P\log L$ carries no
  information. Ω asks to beat the **trivial** bound by $\eta P$.
- The loss comes entirely from moduli $q = P^\theta$ with $\theta \to 1$, where Brun–Titchmarsh's $2/(1-\theta)$ diverges.

**(vi) Large-sieve duality.** This gives an exceptional-set theorem, not a pointwise one: Theorem LS below.

### 7.10 Theorem LS (large sieve; proved — **exceptional set, not pointwise**)

> **Theorem LS.** Let $P \ge P_0$, let $J$ be any interval of length $Y \ge 1$, and let $Q \in (P, P^2]$. Then
> $$\#\{N \in J : N \text{ carries a restricted-support family}\} \le \frac{Y + Q^2}{(\pi(P)-1)\sum_{P<p\le Q}1/p}.$$
> In particular:
> - (a) **(below $P^2$)** with $Q = 2P$: the bound is $\frac{(Y + 4P^2)L^2}{P\log 2}(1 + O(1/L))$; with $Y = P^2$,
>   $$\#\{N \le P^2 : \text{family}\} \le (7.22 + o(1))\,P\,L^2,$$
>   so the proportion of $N \in (X, 2X]$, $X = P^K \le P^2$, carrying a family is $\le (7.3 + o(1))L^2P^{1-K}$;
> - (b) **($2 < K < 4$)** with $Q = \sqrt X$: at most $(2 + o(1))\,XL/(P\log(K/2))$ in $(X, 2X]$.

*Proof.*
- Restricted support forbids $p \mid N - \ell$ for every prime $p \ge P$ and every $\ell \in I$. So for each prime
  $p \in (P, Q]$, $N$ avoids the $\omega(p) = \pi(P) - 1$ classes $\ell \bmod p$, which are distinct because $3 \le \ell \le P < p$.
- The arithmetic large sieve (Montgomery–Vaughan) gives $\#\le(Y + Q^2)/\mathcal J$, with
  $\mathcal J = \sum_{q\le Q}\mu^2(q)\prod_{p\mid q}\frac{\omega(p)}{p-\omega(p)}$.
- Since $Q \le P^2$, every squarefree $q \le Q$ with all prime factors $> P$ is $1$ or prime. So
  $\mathcal J \ge (\pi(P)-1)\sum_{P<p\le Q}1/p$.
- For (a): $\sum_{P<p\le2P}1/p = \log(1 + \frac{\log 2}L) + O(L^{-2}) = \frac{\log2}L(1 + O(1/L))$ and $\pi(P) \ge P/L$, so the bound is
  $\frac{(Y+4P^2)L^2}{P\log 2}(1+O(1/L))$. With $Y = P^2$ this is $\frac5{\log2}PL^2 \le 7.22\,PL^2$.
- For (b): $\sum_{P<p\le\sqrt X}1/p = \log(K/2) + O(1/L^2)$. $\square$

**Remarks.**
1. Numerically (`scripts/residual_numerics.py`), there is **no** restricted-support $N \in (2P, P^2)$ for any $11 \le P \le 400$.
2. **The large sieve cannot prove emptiness.** For $X \le P^2$ every admissible $Q$ exceeds $P$, so the bound is
   $\ge Q^2/\mathcal J \gg PL^2/\log(\log Q/L)$. It never drops below $1$. Theorem LS is an exceptional-set statement in the sense
   of §1. It **does not** exclude any given $N$.
3. In terms of $N$: for $P \ge N^{1/2}$, the restricted-support $N$ up to $P^2$ number $\ll N^{1/K}(\log N)^2$.

### 7.11 The missing lemma

> **Lemma Ω (missing; exact form).** There exist $\epsilon \in (0, 1/3)$, $\eta > 0$ and $P_0$ such that for **every** $P \ge P_0$ and
> **every** even $N$ with $P^{5/3} \le N \le P^{2-\epsilon}$, writing $K = \log N/\log P$:
> $$\Sigma_{\mathrm{large}}(N) := \sum_{\substack{\sqrt P<q\le P\\ q\ \mathrm{prime}}}\log q\cdot\#\{\ell\ \mathrm{prime} : 3 \le \ell \le P,\ \ell \equiv N\ (\mathrm{mod}\ q)\} \le \Bigl(K - \frac12 - \eta\Bigr)P.$$
> (Sub-band version $\Omega_J$: the same for $K$ restricted to an interval $J \subset [5/3, 2-\epsilon]$.)

**Ω ⟹ exclusion (proved, with ineffective $P_0$).**
- By BV (§7.5(a)) and the prime-power and window estimates, $\mathcal M(N) \le \frac P2 + \Sigma_{\mathrm{large}}(N) + O(P\log L/L)$ for **every** $N$.
- So Ω gives $\mathcal M(N) \le (K - \eta + o(1))P$, which contradicts Theorem A.
- Hence no restricted-support family has $P^{5/3} \le N \le P^{2-\epsilon}$ (resp. $K \in J$) for $P$ large.

**Equivalent form (Lemma E).** Up to $o(P)$, Ω says that for every such $N$ the rows carry prime mass $\ge \eta P$ above $P$:
$H_{\mathrm{big}}(N) + n_N(P)\log P \ge (\eta - o(1))P$. Hence at least $(\eta/K - o(1))\pi(P)$ rows $N - \ell$ have a prime factor $\ge P$.

**Nature of Ω.**
- It is an **upper bound** for primes in progressions, needed only up to the factor $2K - 1 \in [7/3, 3)$ above the truth.
  The average of $\Sigma_{\mathrm{large}}$ is $P/2$, and numerically $\max_N\mathcal M(N)/(KP) \approx 0.70, 0.66, 0.65$ for
  $P = 1009$ (all $N$), $4001$, $10007$ (samples). **Parity is not involved.**
- It is a **Brun–Titchmarsh-on-average** statement:
  - for **prime** moduli $q \in (\sqrt P, P]$;
  - for the **single residue** $N \bmod q$;
  - with constant $< 2K - 1$ after integrating over $q = P^\theta$, $\theta \in (1/2, 1]$.
- Brun–Titchmarsh per modulus gives the constant $2/(1-\theta)$, which integrates to $2\log L$ (§7.9(v)).

**Why the available technology does not give Ω.**
- **(1)** BV stops at $\theta = 1/2$.
- **(2)** The theorems of Fouvry and Bombieri–Friedlander–Iwaniec beyond $1/2$ need a **fixed** residue $a$ that is small relative to
  $x$, and well-factorable weights. Here the moduli are primes and the "residue" $N \ge P^{5/3}$ is far larger than the moduli. *(Audit correction 2026-11-25: an earlier
  version wrote $N \gg q^2$. That is false for $q$ of size $P$: with $K < 2$ fixed, $N/q^2 \to 0$. Only $N > q$ holds on the whole range, and
  $N \ge q^2$ only for $q \le P^{K/2}$. No external estimate is claimed to apply in either regime.)*
- **(3)** Divisor switching is unavailable. $N - \ell = bq$ with $b \approx N/q \ge P^{K-1}$, and $\lfloor N/q\rfloor$ is constant only on
  stretches of length $\le q^2/N \le P^{2-K}$. So the problem breaks into $\asymp N/Q$ short pieces. Their recombination requires
  Kloosterman-type sums over primes with a reciprocal phase, $\sum_{q\sim Q}\log q\,e(a\bar q/d + Y/(dq))$ with $Y \approx P^K$, for $d$
  up to $P^{6/7}$ (§7.4).

**Assessment.** Ω needs prime-distribution input that is not currently available: a level of distribution beyond $1/2$ for prime
moduli and a "large" residue. None of the restricted-support constraints we have (L1, R1–R7, MR, near-injectivity, the
certificate identities) supplies it, for two reasons:
- every one of them is either true for generic $N$, or is a consequence of "$\mathcal M$ maximal" itself;
- the only structural inequality that sees restricted support, L1/Lemma E, is exactly the lower bound that Ω must beat.

**Weaker versions that are proved.**

| Version | Statement | Status |
|---|---|---|
| Ω-average | $\mathbb E_{N\in(X,2X]}\Sigma_{\mathrm{large}}(N) = (\frac12 + O(\frac1L))P$, $X \ge P^{5/3}$ | proved (Theorem A) |
| Ω-small | $\mathcal M_{\le\sqrt P}(N) \le (\frac12 + o(1))P$ for **every** $N$ | proved (BV, ineffective) |
| Ω-BT | $\mathcal M(N) \le 2P\log L + O(P)$ for **every** $N$ | proved, but **weaker than the trivial** $\mathcal M(N) \le (K + o(1))P$; no information |
| Lemma T (trivial) | $\Sigma_{\mathrm{large}}(N) \le (K - \frac12 + o(1))P$ for every $N$ | proved (`distribution-profile.md`); Ω = beat it by $\eta P$ |
| Ω-exceptional | a family exists for at most $7.3\,PL^2$ values of $N \le P^2$ | proved (Theorem LS); not pointwise |
| Ω-conditional | $(\mathrm{LD}_\lambda)$, $\lambda > 2/(2K-1)$ ⟹ Ω | derivation (Prop. C, audited §7.5) |

### 7.12 The top range $(P/2, P]$: a geometric bound, a necessary condition, and why it does not simplify the problem

**Lemma P (parity; proved, **Lean**: `large_prime_unique_row`).** For every even $N > P$ and every odd $q$ with $2q > P - 3$, at most one
$\ell \in I$ has $q \mid N - \ell$. So $n_N(q) \le 1$ for every prime $q > (P-3)/2$.

*Proof.* If $q \mid N - \ell$ and $q \mid N - \ell'$ with $\ell \ne \ell'$, then $q \mid \ell - \ell'$. This difference is even and nonzero,
and $q$ is odd, so $2q \mid \ell - \ell'$. But $0 < |\ell - \ell'| \le P - 3 < 2q$. $\square$
(No restricted-support hypothesis is used.)

**Lemma G (geometric bound; proved, every $N$).** For every even $N$ with $P^{3/2} < N \le P^2$:
$$T(N) := \sum_{(P-3)/2<q\le P}\log q\;n_N(q) \le \Bigl(\frac{\log 2}{2} + o(1)\Bigr)P = (0.3466 + o(1))P,$$
uniformly in $N$ and effectively. The explicit version from (17.47) is $(\frac12 - 0.1503 + o(1))P$.

*Proof.*
- Let $g_N(q) = \#\{b \text{ odd} : bq \in [N-P, N-3]\}$. For $q > (P-3)/2$ the interval has length $< 2q$, so $g_N(q) \le 1$. If $q \mid N - \ell$, then
  $b = (N-\ell)/q$ is odd (as $N - \ell$ and $q$ are odd), so $n_N(q) \le g_N(q)$, using Lemma P.
- By (7.1) with $m = 2$: $g_N(q) = \frac{P-3}{2q} - \psi(x'_q) - \psi(x_q)$, where $e(hx'_q) = \pm e\bigl(h\frac{N-3}{2q}\bigr)$ and $e(hx_q) = \pm e\bigl(-h\frac{N-P}{2q}\bigr)$.
- The main term is $\sum_{P/2<q\le P}\log q\,\frac{P-3}{2q} = \frac P2(\log 2 + O(1/L))$. The primes $q \in ((P-3)/2, P/2]$ number at most two.
- For the sawtooth sums, use Vaaler with a fixed $H$, then let $H \to \infty$. The sums $\sum_{P/2<q\le P}\log q\,e(\pm hA/(2q))$ with
  $A \in \{N-3, N-P\}$ are $o(P)$ for each fixed $h$, uniformly in $N$: this is Lemma 17.12 as reconstructed in
  `theorem-W-dependencies.md` B.2. Its proof uses only $|Y| = |h|A/2 \ge P^{3/2}/3$ and a bound on $\log N$, which is automatic for
  $K \le 2$. The integer points cost $O(KL)$.
- With $\log q \le L$ and the count $G \ge \frac3{20}P/L$ of (17.47), one also gets the slightly weaker $(0.35 + o(1))P$. $\square$

*Dependencies.* Prop. 16.2 of [CC] (audited reconstruction) and Prop. 16.3χ (self-audited), through Lemma 17.12. In this band there is
no dependency on Th. 15.1.

*Size.* The true average of $T(N)$ is $\pi(P)\sum_{P/2<q\le P}\log q/q \approx (\log 2)P/L = o(P)$. Numerically
(`scripts/residual_numerics.py`, part 4), over 100 000 sampled $N$:

| $P$ | geometric bound: mean / max | true $T(N)$: mean / max |
|---|---|---|
| 4001 | $0.343P$ / $0.398P$ | $0.094P$ / $0.149P$ |
| 10007 | $0.345P$ / $0.384P$ | $0.085P$ / $0.121P$ |

**Lemma G ignores the primality of $\ell$** and loses a factor $\asymp L$.

> **Corollary G (necessary condition; proved, with BV's ineffective $P_0$).** Every restricted-support family with
> $5/3 \le K \le 2 - \epsilon$ and $P \ge P_0(\epsilon)$ satisfies
> $$\Sigma_{\mathrm{mid}}(N) := \sum_{\sqrt P<q\le(P-3)/2}\log q\;n_N(q) \ge \Bigl(K - \frac12 - \frac{\log 2}2 - o(1)\Bigr)P \ge (K - 0.847 - o(1))P.$$

*Proof.* Theorem A gives $\mathcal M(N) \ge (K - o(1))P$. Decompose $\mathcal M(N)$ as
- $\sum_{d\le\sqrt P}\Lambda(d)n(d)$, which is $\le (\frac12 + o(1))P$ for every $N$ (BV for $d \le D_0$, Brun–Titchmarsh on $(D_0, \sqrt P]$, §7.5(a));
- prime powers $q^j \in (\sqrt P, P]$ with $j \ge 2$: $o(P)$ (§7.5(c));
- $\Sigma_{\mathrm{mid}}(N)$;
- $T(N) \le (\frac{\log2}2 + o(1))P$ (Lemma G). $\square$

The implication proposed (with $0.85$) is therefore **verified**, with constant $\frac12 + \frac{\log 2}2 = 0.8466$ (or $0.8497$ with the
explicit $0.1503$). The average of $\Sigma_{\mathrm{mid}}$ is $(\frac12 + O(1/L))P$. Numerically $\max_N\Sigma_{\mathrm{mid}}(N)/((K - 0.847)P) \approx 0.63, 0.62$
($P = 4001, 10007$, sampled $N$ with $5/3 \le K \le 1.98$).

**The corresponding sufficient condition.**

> **Lemma $\Omega_{1/2}$ (open).** There exist $\epsilon, \eta > 0$ and $P_0$ such that for every $P \ge P_0$ and every even $N$ with
> $P^{5/3} \le N \le P^{2-\epsilon}$:
> $$\Sigma_{\mathrm{mid}}(N) \le \Bigl(K - \frac12 - \frac{\log 2}2 - \eta\Bigr)P.$$

$\Omega_{1/2}$ contradicts Corollary G, so it excludes the band. By Lemma G, $\Omega_{1/2} \Rightarrow \Omega$ (with $\eta$ unchanged). The converse
does not follow. **So $\Omega_{1/2}$ is a stronger sufficient condition than $\Omega$, not a weaker one**: it drops the moduli $q > P/2$ but
requires a smaller bound on the rest.

**Does the restriction $q \le P/2$ make the analytic problem easier? No.**
- **(a) The required constant crosses the parity limit.** On $(\sqrt P, P/2]$, write the target as a per-scale constant $C$ times the true size.
  - $\Sigma_{\mathrm{mid}}$ has true size $\approx P/2$, so $\Omega_{1/2}$ needs $C < 2K - 1 - \log 2 \in [1.64, 2.31)$.
  - An upper-bound sieve using level-of-distribution information alone gives at best $C = 2/\lambda \ge 2$. This is optimal for such
    information, by Selberg's parity examples; the classical barrier is a statement about methods, not about $\Omega_{1/2}$.
  - **For $K \le 1.847$, $\Omega_{1/2}$ is therefore out of reach of any sieve-only argument, even with level $\lambda = 1$.** For
    $K \in (1.847, 2)$ it needs $\lambda > 1/(K - 0.847) \in (0.867, 1)$.
  - **By contrast, $\Omega$ needs only $\lambda > 2/(2K-1) \in (2/3, 6/7]$, with no parity issue.**
  - The reason: Lemma G bounds the top range by $0.347P$, while its truth is $o(P)$. That lost slack must be recovered in the middle range.
- **(b) Brun–Titchmarsh.** The divergence $\int^{1}\frac{d\theta}{1-\theta}$ comes from all scales $X_Q = P/q \in [2, P^{o(1)}]$, not only from
  $X_Q < 2$. For every fixed $T$, the method gives
  $\Sigma_{\mathrm{mid}}(N) \le \frac P2\log\frac T2 + 2P\log\frac L{2\log T} + O(P) = 2P\log L + O(P)$, uniformly in $N$.
  - *Correction:* this is worse than the trivial bound $\Sigma_{\mathrm{mid}} \le \Sigma_{\mathrm{large}} \le (K - \frac12 + o(1))P$ (Lemma T of
    `distribution-profile.md`).
  - Lemma G's method on $(P/T, P/2]$ and Brun–Titchmarsh below.
- **(c) Divisor switching.** $N - \ell = bq$ with $b \ge 2N/P \ge 2P^{K-1}$.
  - In modulus $q \in (\sqrt P, P/2]$ the progression has length $(P-3)/(2q) \in [1, \sqrt P/2]$. In modulus $b$ it has length $\le P^{2-K}/4$.
  - Switching to $b$ loses the primality of $q = (N-\ell)/b$. Dropping it costs a factor $\asymp L$. Keeping it gives a two-dimensional
    sieve on progressions of length $\le P^{2-K}$, whose upper bound loses a factor $\ge 4(2-K)^{-2} \ge 36$.
  - The restriction $q \le P/2$ changes neither length.
- **(d) Level of distribution.** The scales without any twisted estimate are $Q \in (6P^{K/2}, P]$ (§7.3, corrected). Removing
  $(P/2, P]$ leaves $(6P^{K/2}, P/2]$, a range of the same logarithmic length.
- **(e) Large sieve / bilinear / dispersion.**
  - The dual large sieve gives exceptional-set bounds only (Theorem LS).
  - A dispersion argument would compare pairs $N - bq$, $N - b'q'$ and produce Kloosterman-type sums in which $N$ enters through
    $N\bar q \bmod d$ and the phase $hN/(dq)$ (§7.4). Nothing in the restriction $q \le P/2$ removes this; I did not obtain any such argument.

**A reduction in the useful direction — now unconditional.** *Update:* the hypothesis below is now **proved**, as Proposition 16.2χ,
and the conclusion is **Theorem B**; see `prop-16-2-chi-top-range.md`. As a result:
- $\sum_{P/\mathcal T<q\le P}\log q\,n_N(q) = o(P)$ for every fixed $\mathcal T$, uniformly in $N$;
- Corollary G is superseded by Corollary B2: $\sum_{\sqrt P<q\le P/\mathcal T}\log q\,n(q) \ge (K - \frac12 - o(1))P$;
- $\Omega_{1/2}$ is obsolete;
- $\Omega \iff \Omega_{\mathcal T}$.

The original conditional discussion is kept below for the record.
- *Hypothesis 16.2χ$_{\mathrm{fix}}$ (proved since; see above).* For every fixed modulus $d$ and character $\chi \bmod d$,
  $\sum_{n\in(3X/4,X)}\Lambda(n)\chi(n)e(Y/n) = o(X)$ uniformly for $(\log X)^{32} \le |Y|/X \le X$.
- *Plausibility.* This is Prop. 16.2 of [CC] with a fixed character. Splitting $n \bmod d$ turns the Type I phases into the shifted
  phases of Lemma S range (i), so it is plausible that the proof of [CC] §16.4 extends. **This has not been written or checked.**
- *What it would give.* For every fixed $T$, Selberg at a fixed level $D$ (then $D \to \infty$) on $(P/T, P]$ gives
  $$\sum_{P/T<q\le P}\log q\;n_N(q) \le \frac{(P/2)\log T}{\frac12(\log D - 1)} + o_D(P) \to o(P),$$
  for every $N$ in the band. This uses $q > P/T > D^2$, (7.0), and $r_d = o(P)$ for each of the finitely many $d < D^2$, via Vaaler and
  16.2χ$_{\mathrm{fix}}$.
- *Consequence.* The necessary condition would become $\sum_{\sqrt P<q\le P/T}\log q\,n(q) \ge (K - \frac12 - o(1))P$. The sufficient condition
  would become $\Omega_T$: the same sum $\le (K - \frac12 - \eta)P$. $\Omega_T$ is **implied by** $\Omega$, so it is a genuine weakening, still with
  $\lambda > 2/(2K-1)$ and no parity problem.
- **$\Omega_T$ remains open; the conditional step only removes the top constant range of scales.**

**Status in the band $5/3 \le K \le 2-\epsilon$.**

| Statement | Type | Status |
|---|---|---|
| Theorem A: $\mathcal M(N) \ge (K - o(1))P$ | necessary condition | proved |
| Corollary G: $\Sigma_{\mathrm{mid}}(N) \ge (K - 0.847 - o(1))P$ | necessary condition | proved; **superseded by Corollary B2** |
| Corollary B2: $\sum_{\sqrt P<q\le P/\mathcal T}\log q\,n(q) \ge (K - \frac12 - o(1))P$ | necessary condition | proved (Theorem B) |
| Theorem B: $\sum_{P/\mathcal T<q\le P}\log q\,n_N(q) = o(P)$ for every $N$ | pointwise upper bound | **proved** (`prop-16-2-chi-top-range.md`) |
| Lemma E: family $\iff H_{\mathrm{big}}(N) = 0$ and $n_N(P) = 0$ | equivalence | proved |
| $\Omega$: $\Sigma_{\mathrm{large}} \le (K - \frac12 - \eta)P$ for all $N$ | sufficient condition | **open** |
| $\Omega_{1/2}$: $\Sigma_{\mathrm{mid}} \le (K - 0.847 - \eta)P$ for all $N$ | sufficient condition (stronger than $\Omega$) | open; obsolete after Theorem B |
| $\Omega_{\mathcal T}$: $\sum_{\sqrt P<q\le P/\mathcal T} \le (K - \frac12 - \eta)P$ for all $N$ | sufficient condition, **equivalent to $\Omega$** (Theorem B) | **open** |
| $(\mathrm{LD}_\lambda)$, $\lambda > 2/(2K-1)$ | sufficient for $\Omega$ | **open** |
| Pointwise upper bounds proved | — | trivial $\Sigma_{\mathrm{large}} \le (K - \frac12 + o(1))P$ (Lemma T); top range $o(P)$ (Theorem B) |
| Theorem LS | exceptional set | proved; excludes no individual $N$ |
| **Proven pointwise exclusions in this band** | — | **none** |

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
| Proposition C ($\mathrm{LD}_\lambda$, $\lambda > 2/(2K-1)$ ⟹ exclusion) | derivation, audited (§7.5) | BV indispensable; $r_1$ via Prop. 16.2/16.3χ ($d=1$), **not** Lemma S; $d>1$ at scales $Q > c\sqrt N$ only via $\mathrm{LD}_\lambda$ |
| Lemma E (mass decomposition, every $N$) | proved | family ⟺ $H_{\mathrm{big}} = 0$ ⟺ $\mathcal M$ maximal |
| R7: $\log B \ge (K-1-o(1))P$ for $K < 2$ | proved | improves R5 on $[5/3,2)$; still below R4's barrier |
| MR multiplicative rigidity | proved, **Lean** | negative for exclusion (true for every $N$) |
| Ω-BT: $\mathcal M(N) \le 2P\log L + O(P)$ | proved | weaker than the trivial bound; no information (corrected 2026-11-25) |
| Lemma T: $\Sigma_{\mathrm{large}}(N) \le (K - \frac12 + o(1))P$ | proved | pointwise; Ω means beating it by $\eta P$ |
| Proposition PF (integrated sieve bound $2\int d\theta/\lambda(\theta)$) | proved (implication) | `distribution-profile.md`; available profiles give $11.6 > K - \frac12$ |
| Theorem LS: $\le 7.3PL^2$ families with $N \le P^2$ | proved | exceptional set, **not pointwise** |
| Lemma P (parity: $n_N(q) \le 1$ for $q > (P-3)/2$) | proved, **Lean** | every $N$ |
| Lemma G: $\sum_{q>(P-3)/2}\log q\,n_N(q) \le (\frac{\log2}2 + o(1))P$ | proved | every $N$; loses a factor $\asymp L$ |
| Corollary G: $\Sigma_{\mathrm{mid}} \ge (K - 0.847 - o(1))P$ for families | proved | necessary condition |
| Lemma Ω | **open** | the single missing estimate (§7.11) |
| Lemma $\Omega_{1/2}$ | open, obsolete | stronger than Ω; beyond sieve methods for $K \le 1.847$ (§7.12) |
| Proposition 16.2χ (twisted reciprocal sums, $d \le X^{1/10}$, $|Y| \le X^2$) | **proved** | new; `prop-16-2-chi-top-range.md` |
| Theorem B (top range $o(P)$, every $N$) | **proved** | new; Corollary B2 supersedes Corollary G |
| Lemma $\Omega_{\mathcal T}$ ($\iff$ Ω) | **open** | the missing estimate is $(\mathrm{LD}_\lambda)$, $\lambda > 2/(2K-1)$, on blocks $X \in [\sqrt P, P/\mathcal T]$ |

**No pointwise exclusion is obtained.** The question is reduced, on $5/3 \le K < 2$, to Lemma Ω (§7.11): a Brun–Titchmarsh-on-average
bound for prime moduli $q \in (\sqrt P, P]$ and the single residue $N \bmod q$, with constant $< 2K - 1$. It follows from
$(\mathrm{LD}_\lambda)$ with $\lambda > 6/7$ (resp. $2/3$). **Neither is proved. Wall II remains open.**
