# Residual region $P^{5/3} < N < P^{959}$: repetition mass, injectivity, and a barrier

Status: **research note.** The lemmas marked "proved" have a written, self-audited proof (and R2 a Lean proof).
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

**Barrier corollary.** A "budget" contradiction compares an upper bound $\log B \le U$ with a lower bound coming from the
structure of a family. The best structural lower bound available today is R3(ii) with the absence density
$c = 3/20$, or at best $c_g = (1-\log2)/2$ if one used the full asymptotics of (17.37). If $U$ is proved for **all** $N$
(as the sieve bound of `hypothesis-T.md` is), R4 forces $U \ge (1-o(1))P$, so a contradiction requires
$$cK + \tfrac12 - c > 1 \iff K > 1 + \frac{1}{2c} \approx 4.26\ (c = c_g),\quad 4.33\ (c = 0.15).$$
**Consequence (rigorous, about the method):** no universal upper bound on $\log B$, however sharp, can exclude
$5/3 < K \le 4.26$ by this comparison. **The region $P^{5/3} < N \le P^{4.26}$ requires an upper bound that uses the
restricted support of the family itself**, or an argument other than the budget.

---

## 6. Exact remaining obstruction

Two regimes:

**(O1) $4.26 < K < 950$: constant gap.** The comparison would suffice with a universal bound
$\log B(N) \le (0.15K + 0.35 - \epsilon)P$; at $K \approx 5$ that is $\approx 1.1P$, which is the average order (R4). But the
sieve of `hypothesis-T.md` gives $C_0(1 + \log K)P$ with $C_0 \approx 10$, because of:
- the Selberg factor ($\ge 2$, parity) and the level $D^3 \approx X\mathcal E^{-1}$ (factor 3);
- the cost $\log(1 + K^2/c_2)$ of the exponential saving $\mathcal E = P^{-c_2/K^2}$.

Closing (O1) requires an **asymptotic**, not just an upper bound, for the incidences
$$S_Q(N) = \sum_{\ell\le P}\ \sum_{q\in(Q,2Q]}\log q\,\mathbf 1_{q\mid N-\ell} = \#_{\log q}\{(\ell, q, k) : N = \ell + kq\},$$
uniformly for $Q$ up to $P/4$ and for **a fixed $N$**. That is equidistribution of the primes $\ell \le P$ in the fixed class
$N \bmod q$, on average over prime moduli $q \sim Q$ up to $P^{1-o(1)}$: an Elliott–Halberstam-type statement for a
fixed residue at level $1 - o(1)$. That is beyond Bombieri–Vinogradov (level $1/2$) and beyond the Bombieri–Friedlander–Iwaniec
results for a fixed residue (level $4/7$, with well-factorable weights). **This is the precise obstruction.**

**(O2) $5/3 < K \le 4.26$: structural gap.** By R4, no universal budget is enough. One must exploit, inside the upper
bound, the fact that every $M_\ell$ is $P$-smooth. A natural candidate, not proved: show that for a
restricted-support family, the number of large primes $q$ with $C_q \le P^{\theta}$ is $o(P/L)$, through the injectivity of R2
combined with equidistribution of $\{N/q^b\}$. Note that R2 forces the cofactors $C_q \approx N/q^{b_q}$ to be pairwise distinct.
**Not done.**

**Summary.** R1–R4 are proved (R2 in Lean). R3′ improves $K_0$ from $959$ to $950$. **No pointwise exclusion is
obtained** in $P^{5/3} < N < P^{950}$. Wall II stays open, with the obstruction stated in (O1)–(O2).
