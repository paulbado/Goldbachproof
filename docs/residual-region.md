# Residual region $P^{5/3} < N < P^{959}$: repetition mass, injectivity, and a barrier

Status: **research note.** The lemmas marked "proved" have a written, self-audited proof; R2, R2′, R2″ also have a Lean proof.
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

> **Lemma R4.** For $P$ large and every $X \ge P^2$, averaging over the even $N \in (X, 2X]$ (with no restricted-support
> hypothesis; $B(N) = \prod_\ell M_\ell/\mathrm{lcm}$ and $v_q(B) = \sum_a(n(q^a)-1)_+$ hold for every $N$):
> $$\mathbb E_N\log B(N) \ge \Bigl(1 - \frac{3\log L}{L}\Bigr)P.$$
> Hence any bound $\log B(N) \le U(P)$ valid **for all** even $N$ in such a range satisfies $U(P) \ge (1 - o(1))P$.

*Proof.* Let $q \le Q_1 := P/L^2$ be an odd prime. As $N = 2n$ runs over $(X, 2X]$, each class $\ell \bmod q$ receives
$X/(2q) + O(1)$ values of $N$, so $\mathbb E\,n_N(q) \ge (\pi(P)-1)(1/q - 2/X) \ge (\pi(P)-1)/q - 2/P$ (since $X \ge P^2$). Since $v_q(B) \ge (n(q)-1)_+ \ge n(q) - 1$,
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

## 6. Exact remaining obstruction (updated)

**(O1) $2.7 < K < 950$: constant gap.** A **universal** bound $\log B(N) \le (\lambda(K) - \epsilon)P$ would suffice, where
$\lambda(K) = \max(0.15K + 0.35, \frac{K-1}{2} + 0.15)$; that is, at most $\approx 1.1P$ near $K = 3$. The current sieve gives
$C_0(1 + \log K)P$ with $C_0 \approx 10$ (Selberg factor $\ge 2$, level $D^3 \approx X\mathcal E^{-1}$, cost $\log(K^2/c_2)$). Closing this
would require an **asymptotic** for $S_Q(N) = \#_{\log q}\{N = \ell + kq\}$ for a fixed $N$, with $Q$ up to $P/4$: equidistribution of
$\ell \le P$ in the fixed class $N \bmod q$ on average over $q \sim Q \le P^{1-o(1)}$. That is an Elliott–Halberstam-type statement for a
fixed residue at level $1 - o(1)$, beyond Bombieri–Vinogradov ($1/2$) and Bombieri–Friedlander–Iwaniec ($4/7$, well-factorable weights).

**(O2) $5/3 < K \le 2.7$: structural gap.** The universal budget is not enough (R4, relative to R3/R5). We would need,
**for restricted-support families**, either $\log B < (\frac{K-1}{2} + 0.15)P$, i.e. a budget **below its average value**
(R4: average $\ge (1 - o(1))P$), or a structural lower bound $> P$. Precise target statement, **open**:
> *(T) For every restricted-support family with $5/3 < K \le 2.7$: $\log B \le (\frac{K-1}{2} + 0.15 - \eta)P$ for a fixed $\eta > 0$.*

Together with R5, (T) would give a contradiction, hence emptiness of the residual region on $5/3 < K \le 2.7$.

**Summary.**
- Proved: R1, R2 (Lean), R2′ (Lean), R2″ (Lean), R3, R3′ ($N < P^{950}$), R4 (correct scope), R5.
- **No pointwise exclusion** on $P^{5/3} < N < P^{950}$.
- **Wall II remains open**; the exact obstructions are (O1) and (T).
