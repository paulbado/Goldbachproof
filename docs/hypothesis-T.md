# Hypothesis T: character-twisted Proposition 16.3 and its consequence for Wall II

Reference: I. O. Bado, *A Closure Chain Toward Williamson's Conjecture* (2026),
DOI 10.13140/RG.2.2.34840.97281, cited "[CC]". Equation numbers (13.x), (16.x), (17.x)
refer to [CC].

## Audit log (2026-11-24, after commit 4af201e)

Corrections made during the audit (details in the sections indicated):

1. **§8, term $D^3\sqrt Q\,L^4$.** The old justification ("$D^3 \le \sqrt Q$") is insufficient: it
   only gives $\le Q L^4$, which is not $\ll P/L$ when $X_Q$ is small. Replaced by
   $D^3 \le 2P^{0.2033}$, $Q \le P/4$, hence $\le P^{0.71}L^4 = o(P/L)$, uniformly over the scales.
2. **§9, dyadic partition.** The old blocks $Q = P/2^{j+1}$, $j \le \lceil\frac15\log_2P\rceil$, could put
   the last block below $P^{4/5}$. Replaced by an exact partition into **full** dyadic blocks
   $(P/2^{j+1}, P/2^j]$, $1 \le j \le J$, with $J$ maximal such that $2^J \le P^{1/5}$. The admissible
   range of the improved sieve becomes $Q \in [P^{4/5}/2, P/4]$ (every constraint rechecked), and
   $q \le Q_J < P^{4/5}$ is handled by Brun–Titchmarsh alone.
3. **§5, Type II.** Uses Lemma S with $s = 0$ instead of (16.15). This **removes** the dependency on
   §16.5 of [CC] (the passage from Green–Harper to subintervals).
4. **§9, small primes.** Bounded directly by Brun–Titchmarsh and $\log(P/q) \ge L/5$; this removes
   the dependency on Prop. 17.9 and Prop. 17.10. Exponents $b \ge 2$ are bounded by Brun–Titchmarsh
   ($\le 4P/\log 2$).
5. **Constants made explicit:** $c_1 = 2^{-18}$, $c_* = c_1(2/5)^3/2$, $c_2 = c_*(4/5)^3(16/25)$,
   hence an explicit $K_0$ (§9). Only the threshold $P_0$ stays effective but not computed.
6. **Lower bound** stated without $o(1)$: $\log B \ge \frac3{20}KP - P$ (§9).
7. **§6:** $\mathcal E_I \le \sqrt2\,\mathcal E_I^{1/2}$ (instead of $\le \mathcal E_I^{1/2}$).
8. **§9.3:** the $10P/L$ from §9.2(a) is absorbed explicitly in the slack of (b) ($1.5403P$ instead of $1.6P$), for $\log P \ge 168$; $10.6$ and $K_0 = 959$ are unchanged.
9. **Dependencies** corrected in §0 and §11: Th. 15.1 and Prop. 17.13/(17.47) of [CC] remain
   **unverified** inputs.

**Status: written and self-audited proof, NOT independently verified.**

**Update (dependency reconstruction):** the two inputs [CC] Th. 15.1 and Prop. 17.13 / (17.47), marked
"unverified" below, are reconstructed in [`theorem-W-dependencies.md`](theorem-W-dependencies.md) (Parts A and B),
from published results only (Matveev–BMS, Brun–Titchmarsh, Rosser–Schoenfeld, an effective PNT, van der Corput,
Beurling–Selberg). Theorem W is therefore **free of internal dependencies on [CC]**, but still **not independently
verified**. The tables of §0 and §11 below describe the state before that reconstruction.

## 0. Status and dependencies

This document contains a **written, self-audited** proof of Proposition 16.3χ (§1–§6), using only
published external results, and a derivation of Theorem W (§7–§9), which is **conditional** on two
unverified results of [CC] (Th. 15.1, (17.47)). **No independent verification yet.**
$c_1$, $c_*$, $c_2$, $C_0$, $K_0$ are explicit; $P_0$ is effective but not computed (and astronomical).

External inputs, used as stated and not reproved here:

| Input | Exact statement used | Where |
|---|---|---|
| van der Corput $k$-th derivative test | if $\lambda \le |f^{(k)}| \le B\lambda$ with constant sign on $J$, $|J| \le Z$, $k \ge 2$: $\sum_{n\in J} e(f(n)) \ll_{k,B} Z\lambda^{1/(2^k-2)} + Z^{1-2^{2-k}}\lambda^{-1/(2^k-2)}$ ((13.3) of [CC]; Graham–Kolesnik Th. 2.8) | Lemma S (i) |
| [MRSTT] Lemma 4.1 | arXiv:2106.03335, Lemma 4.1, conditions (4.2)–(4.3), conclusion (4.4); reproduced in §2 | Lemma S (ii) |
| Vaaler (1985) | §7 | remainders |
| Selberg $\Lambda^2$ (Halberstam–Richert Th. 3.2) | $S \le \mathcal X/G(z) + \sum_{d<z^2,\,d\mid\Pi(z)}3^{\omega(d)}|r_d|$, for $0 \le g(p) < 1$, nonnegative weights | §8 |
| $G(z)$ lower bound | $\sum_{d<z,\,(d,2)=1}\mu^2(d)/\varphi(d) \ge \frac12\sum_{n<z}1/n$ | §8 |
| Brun–Titchmarsh (Montgomery–Vaughan) | $\pi(x;k,a) \le 2x/(\varphi(k)\log(x/k))$ for $(a,k)=1$, $k<x$ | §9 |
| Mertens (Rosser–Schoenfeld) | $\sum_{p\le x}\log p/p < \log x$; $\sum_{Q<p\le 2Q}\log p/p = \log 2 + O(1/\log Q)$ | §8–9 |
| **[CC] Th. 15.1** (not verified) | $\log N \le 32000\log P(1+\log\log P)$ for $P \ge P_1$ | §8 ($K$ bounded), and via (17.30) for (17.47) |
| **[CC] Prop. 17.13 / (17.47)** (not verified) | $G(N,P) \ge 3P/(20\log P)$ for $N > P^{3/2}$, $P \ge P_2$ | §9 lower bound |
| Lean (verified) | (17.1), (17.6) `factor_one_budget`, $a \ge G$ `geomAbs_subset_absent` | §9 |

**No longer used:** Green–Harper Prop. 4.3 / (16.13)–(16.15) of [CC], Props. 17.9 and 17.10,
Th. 17.14 (Th. 15.1 is enough).

Notation: $L_X = \log(2X)$, $\Omega = \log(2|Y|)$, $\Lambda$ von Mangoldt, $e(x) = e^{2\pi i x}$.

---

## 1. Statement

> **Proposition 16.3χ.** There are absolute effective constants $X_0$, $c_* > 0$ such that, for
> every $X \ge X_0$, every integer $1 \le d \le X^{1/4}$, every Dirichlet character $\chi \bmod d$,
> every interval $I \subseteq (X/2, X]$ and every real $Y$ with $|Y| \ge X^2/64$,
> $$\Bigl|\sum_{n\in I}\Lambda(n)\chi(n)e(Y/n)\Bigr| \ll X\,L_X^{5}\Bigl(X^{-1/310} + \exp\Bigl(-c_*\frac{(\log X)^3}{\Omega^2}\Bigr)\Bigr).$$
> The implied constant is absolute. No upper bound is assumed on $|Y|$.

For $d = 1$ and $I = (3X/4, X)$ this is Prop. 16.3 of [CC], up to the value of $c_*$.
The case $Y < 0$ follows from $Y > 0$ by complex conjugation, replacing $\chi$ with $\bar\chi$.
**From here on, $Y > 0$.**

---

## 2. Shifted reciprocal phases

> **Lemma S.** There are absolute $Z_0$, $c_1 > 0$ with the following property. Let $Z \ge Z_0$,
> $0 \le s < 1$, $A$ real with $|A| \ge Z^{3/2}$, and $J \subseteq [Z, 2Z]$ an interval. Then
> $$\Bigl|\sum_{k\in J} e\bigl(A/(k+s)\bigr)\Bigr| \ll Z\Bigl(Z^{-1/62} + \exp\Bigl(-c_1\frac{(\log Z)^3}{\log^2(2|A|)}\Bigr)\Bigr),$$
> uniformly in $s$, $J$ and $A$.

*Proof.* Put $f(t) = A/(t+s)$ and $F = |A|/Z \ge Z^{1/2}$. For every $r \ge 1$ and $t \in [Z, 2Z]$,
$$f^{(r)}(t) = (-1)^r r!\,A\,(t+s)^{-r-1}.\qquad(2.1)$$

*Range (i): $Z^{1/2} \le F \le Z^4$.* By (2.1), $|f^{(k)}|$ has constant sign on $[Z, 2Z]$ and
$$\lambda := \frac{k!|A|}{(2Z+1)^{k+1}} \le |f^{(k)}(t)| \le \frac{k!|A|}{Z^{k+1}} \le 3^{k+1}\lambda.$$
So (13.3) applies with ratio $B = 3^{k+1}$, and $\lambda \asymp_k F Z^{-k}$. This is exactly the situation
of Lemma 16.4 of [CC] (there $B = 2^{k+1}$). With $\alpha = \log F/\log Z \in [1/2, 4]$ and
$k = \lfloor\alpha\rfloor + 2 \le 6$, the same computation gives $\ll Z^{1-1/62}$. The constants depend
only on $k \le 6$, hence are absolute. Shorter subintervals: the powers of $|J|$ in (13.3) are
nonnegative.

*Range (ii): $F > Z^4$.* We apply [MRSTT] Lemma 4.1 with $X = Z$, our $F$, and $\alpha = 3e$.
That lemma reads: *let $X \ge 2$, $F \ge X^4$, $\alpha \ge 1$, $I \subset [X, 2X]$ an interval, and
$f$ smooth on $I$ with*
$$\alpha^{-r^3}F \le \frac{t^r}{r!}|f^{(r)}(t)| \le \alpha^{r^3}F\qquad(t\in I,\ 1\le r\le R_0 := 10\lceil\log F/\log X\rceil+1),\qquad(4.2)$$
$$(\log\alpha)\frac{(\log F)^2}{(\log X)^3} < 10^{-3};\qquad(4.3)$$
*then* $\sum_{n\in I} e(f(n)) \ll \alpha X\exp(-2^{-18}(\log X)^3/(\log F)^2)$, *with an absolute
implied constant.*

- **Condition (4.2).** By (2.1), $\frac{t^r}{r!}|f^{(r)}(t)| = \frac{|A|}{t+s}\bigl(\frac{t}{t+s}\bigr)^r$.
  - *Upper bound:* this is at most $|A|/t \le F$.
  - *Lower bound:* $\frac{|A|}{t+s} \ge \frac{|A|}{2Z+1} \ge F/3$, and
    $\bigl(\frac{t}{t+s}\bigr)^r = (1+s/t)^{-r} \ge e^{-r/Z} \ge e^{-1}$ as long as $r \le Z$.
    Hence the quantity is at least $F/(3e) \ge \alpha^{-r^3}F$, because $\alpha^{r^3} \ge \alpha = 3e$.
- **When (4.3) holds.** Then $\log F < 0.022(\log Z)^{3/2}$, so
  $R_0 \le 0.3(\log Z)^{1/2} + 21 \le Z$ for $Z \ge Z_0$, and the condition $r \le Z$ is met.
  Lemma 4.1 gives $\ll Z\exp(-2^{-18}(\log Z)^3/(\log F)^2)$, and $\log F \le \log(2|A|)$.
- **When (4.3) fails.** Then $(\log Z)^3/(\log F)^2 \le 10^3\log(3e) < 2200$, so
  $\exp(-2^{-18}(\log Z)^3/(\log F)^2) \ge e^{-0.01}$. The trivial bound $|J| + 1 \le 2Z$ is then
  of the stated form.

- **Explicit numbers.** $\log(3e) = 1 + \log 3 < 2.1$. Under (4.3),
  $(\log F)^2 < 4.77\cdot10^{-4}(\log Z)^3$, so $\log F/\log Z < 0.022(\log Z)^{1/2}$ and
  $R_0 \le 0.22(\log Z)^{1/2} + 21$. If (4.3) fails, $2^{-18}(\log Z)^3/(\log F)^2 \le 2^{-18}\cdot 2100 < 0.009$.
- **Sign of $A$.** (2.1), (13.3) and (4.2) only involve $|f^{(r)}|$, and the sign of $f^{(k)}$ is
  constant; so the proof is identical for $A < 0$.

This gives Lemma S with $c_1 = 2^{-18}$. $\square$

*Remark.* Lemma S is not new input: it is Lemma 16.4 of [CC] plus MRSTT Lemma 4.1, after
checking that their hypotheses only involve $|f^{(r)}|$, and that these are uniform in the shift
by (2.1).

---

## 3. Vaughan's identity with a character

Let $U = V = \lfloor X^{1/6}\rfloor$. Since $\chi$ is completely multiplicative,
$\chi\cdot(f*g) = (\chi f)*(\chi g)$. Multiplying the exact identity (13.5) of [CC] by $\chi$ gives
$$\Lambda\chi = \Lambda_{\le V}\chi + (\mu_{\le U}\chi)*(\chi\log) - (\mu_{\le U}\chi)*\chi*(\Lambda_{\le V}\chi) + (\mu_{>U}\chi)*\chi*(\Lambda_{>V}\chi).\qquad(3.1)$$
On $I \subseteq (X/2, X]$, the first term vanishes once $X^{1/6} < X/2$. Hence
$$\sum_{n\in I}\Lambda(n)\chi(n)e(Y/n) = S_{I,1} - S_{I,2} + S_{II},$$
$$S_{I,1} = \sum_{a\le U}\mu(a)\chi(a)\sum_{b\in I/a}\chi(b)(\log b)\,e\bigl(Y/(ab)\bigr),\qquad S_{I,2} = \sum_{a\le UV}\alpha(a)\chi(a)\sum_{b\in I/a}\chi(b)\,e\bigl(Y/(ab)\bigr),$$
$$S_{II} = \sum_{\substack{r>V,\ s>U\\ rs\in I}}\Lambda(r)\chi(r)\,\beta(s)\chi(s)\,e\bigl(Y/(rs)\bigr),$$
with $\alpha(a) = \sum_{e r = a,\ e\le U,\ r\le V}\mu(e)\Lambda(r)$ and $\beta(s) = \sum_{e\mid s,\ e > U}\mu(e)$
exactly as in (13.6), (13.7), (13.10). In particular $|\alpha(a)| \le \log a$ and $|\beta(s)| \le \tau(s)$.
For the twisted coefficients: $(\mu_{\le U}\chi)*(\Lambda_{\le V}\chi) = \chi\cdot\alpha$ and
$(\mu_{>U}\chi)*\chi = \chi\cdot\beta$, again by complete multiplicativity. Here $I/a$ denotes
$\{b : ab \in I\}$, an interval contained in $(X/(2a), X/a]$.

---

## 4. Type I sums

Fix $a \le UV = X^{1/3}$ (at most) and put $Z = X/(2ad)$. Since $d \le X^{1/4}$,
$$Z \ge \tfrac12 X^{1-1/3-1/4} = \tfrac12 X^{5/12}.\qquad(4.1)$$
Split $b \in I/a$ by its residue $\rho \bmod d$, $(\rho, d) = 1$, $0 \le \rho < d$, and write
$b = \rho + dk$. Then
$$\frac{Y}{ab} = \frac{A}{k+s},\qquad A := \frac{Y}{ad},\quad s := \frac{\rho}{d}\in[0,1),$$
and $k$ runs over an interval $J_{a,\rho} \subseteq \bigl((X/(2a)-\rho)/d,\ (X/a-\rho)/d\bigr] \subseteq [Z-1, 2Z]$.
At most one value of $k$ lies in $[Z-1, Z)$; it is bounded trivially.

**Size of $A$.** $A/Z^{3/2} = \frac{Y}{ad}\bigl(\frac{2ad}{X}\bigr)^{3/2} \ge \frac{X^2}{64}\cdot\frac{2^{3/2}(ad)^{1/2}}{X^{3/2}} \ge X^{1/2}/23 \ge 1$.
So Lemma S applies, with $\log(2A) \le \Omega$ and, by (4.1), $\log Z \ge \tfrac25\log X$ for large $X$:
$$\sup_{J\subseteq[Z,2Z]}\Bigl|\sum_{k\in J}e\bigl(A/(k+s)\bigr)\Bigr| \ll Z\,\mathcal E_I,\qquad \mathcal E_I := X^{-1/155} + \exp\Bigl(-c_1\bigl(\tfrac25\bigr)^3\frac{(\log X)^3}{\Omega^2}\Bigr).$$
Here $Z^{-1/62} \le (X^{5/12}/2)^{-1/62} \ll X^{-1/155}$, since $5/(12\cdot62) > 1/155$.

**Weight $\log b$.** $k \mapsto \log(\rho + dk)$ is monotone and bounded by $L_X$. Summation by
parts costs a factor $2L_X$ times the supremum over subintervals.

**Assembly.** Using $|\chi(\rho)| \le 1$, the $\varphi(d) \le d$ classes and $|\alpha(a)| \le \log a$:
$$|S_{I,1}| + |S_{I,2}| \ll \sum_{a\le X^{1/3}}(1+\log a)\cdot d\cdot L_X\Bigl(\frac{X}{2ad}\mathcal E_I + 1\Bigr) \ll X L_X^3\,\mathcal E_I + X^{1/3+1/4}L_X^2.$$
**The modulus $d$ cancels**: $d$ classes, each of length about $X/(ad)$. The last term is
$\ll X^{1-1/310}$, so it is absorbed.

---

## 5. Type II sums

Split $r$ and $s$ into dyadic ranges as in [CC] §13.2.3. The condition $rs \in I \subseteq (X/2, X]$
replaces $3X/4 < rs < X$; with the larger variable first, each nonempty box satisfies
$$X/8 < ML < X,\quad M\ge L,\quad M\ge\sqrt{X/8},\quad X^{1/6}/4\le L\le X^{1/2},\quad M\le 4X^{5/6}.\qquad(5.1)$$
These are (16.6) with $3/16$ replaced by $1/8$. There are $O(L_X^2)$ boxes. Write one box as
$$\mathcal S_{M,L} = \sum_{\substack{M\le m<2M,\ L\le v<2L\\ mv\in I}} a_m b_v\,e\bigl(Y/(mv)\bigr),$$
where $(a_m, b_v)$ are $(\Lambda\chi, \beta\chi)$ or the reverse, restricted to their ranges. **Since
$|\chi| \le 1$, the norm bounds (13.11) hold verbatim:**
$$\sum|a_m|^2 \ll M L_X^3,\qquad \sum|b_v|^2 \ll L L_X^3.$$

Cauchy–Schwarz in $m$, where the second factor is extended to **all integers** $m \in [M, 2M)$
(a sum of nonnegative terms, so this only increases it), followed by expansion in $v$, gives
exactly (16.7):
$$|\mathcal S_{M,L}|^2 \le \sum_m|a_m|^2\sum_{v_1,v_2}b_{v_1}\overline{b_{v_2}}\sum_{m\in J(v_1,v_2)}e\bigl(Y(1/v_1-1/v_2)/m\bigr),$$
$$J(v_1,v_2) = [M, 2M)\cap(I/v_1)\cap(I/v_2),\quad\text{an interval}.$$

**No character and no coprimality condition remains in the inner sum**: $\chi$ sits entirely in the
coefficients, whose moduli were bounded first.

*Diagonal $v_1 = v_2$:* $|J| \le 2M$, so it contributes $\ll \sum|a_m|^2\cdot M\sum|b_v|^2 \ll M^2LL_X^6 \le X^2L_X^6L^{-1}$.

*Off-diagonal, $h = |v_1 - v_2| \ge 1$:* coefficient $a' = Y(v_2 - v_1)/(v_1v_2)$, $|a'| = Yh/(v_1v_2) \le Y$. Moreover
$$\frac{|a'|}{M} \ge \frac{Y}{M(2L)^2} \ge \frac{X^2/64}{4XL} = \frac{X}{256L} \ge \frac{X^{1/2}}{256} \ge (4X^{5/6})^{1/2} \ge M^{1/2}$$
for $X \ge X_0$, using $ML < X$, $L \le X^{1/2}$, $M \le 4X^{5/6}$. So $|a'| \ge M^{3/2}$, and
**Lemma S with $s = 0$, $Z = M$, $J = J(v_1,v_2)$** gives, since $\log M \ge \frac12\log(X/8) \ge \frac25\log X$ and
$\log(2|a'|) \le \Omega$,
$$\Bigl|\sum_{m\in J(v_1,v_2)}e(a'/m)\Bigr| \ll M\,\mathcal E_{II},\qquad \mathcal E_{II} := X^{-1/155} + \exp\Bigl(-c_1\bigl(\tfrac25\bigr)^3\frac{(\log X)^3}{\Omega^2}\Bigr)$$
(with $M^{-1/62} \le X^{-1/155}$ because $M \ge X^{2/5}$). Summing,
$\sum_{v_1\ne v_2}|b_{v_1}b_{v_2}| \le (\sum|b_v|)^2 \le 2L\sum|b_v|^2$, which gives an off-diagonal
contribution $\ll \sum|a_m|^2\cdot ML\sum|b_v|^2\,\mathcal E_{II} \ll X^2L_X^6\mathcal E_{II}$. Hence
$$|\mathcal S_{M,L}|^2 \ll X^2L_X^6\bigl(L^{-1} + \mathcal E_{II}\bigr),\qquad L^{-1} \le 4X^{-1/6},$$
$$|S_{II}| \ll L_X^2\cdot X L_X^3\bigl(X^{-1/12} + \mathcal E_{II}^{1/2}\bigr) = X L_X^5\bigl(X^{-1/12} + \mathcal E_{II}^{1/2}\bigr).$$

---

## 6. Conclusion of Proposition 16.3χ

Put $c_* = c_1(2/5)^3/2 = 2^{-18}\cdot 0.032 \approx 1.22\cdot10^{-7}$. Since $\mathcal E_I \le 2$, we have $\mathcal E_I \le \sqrt2\,\mathcal E_I^{1/2}$ (correction: the earlier version wrote $\mathcal E_I \le \mathcal E_I^{1/2}$, false if $\mathcal E_I > 1$), and
$$\mathcal E_I^{1/2} + \mathcal E_{II}^{1/2} \ll X^{-1/310} + \exp\bigl(-c_*(\log X)^3/\Omega^2\bigr).$$
Adding §4 and §5 proves Prop. 16.3χ. The constants depend neither on $d$, nor on $\chi$, nor on $I$,
nor on $Y$ (beyond the hypothesis $|Y| \ge X^2/64$). $\square$

**Summary of the points raised in the request.**
- *Type I and Type II:* §4 and §5.
- *Shifted phases:* Lemma S.
- *Coprimality:* it does not arise. In Type I we sum only over $(\rho, d) = 1$; in Type II Cauchy–Schwarz
  removes it.
- *Endpoints:* the stray value of $k$ in §4; partial intervals inside Lemma S.
- *Uniformity in $d \le X^{1/4}$:* through (4.1).

---

## 7. The sieve remainder

**Setting.** A restricted-support family (Lean: `BadFamily P N`; a [CC] family satisfies it).
$L = \log P$, $K = \log N/L$. We assume
$$4 < K \le 32000(1 + \log L)\qquad\text{(lower bound: hypothesis; upper bound: [CC] Th. 15.1, unverified)}.$$
**Admissible scales:** $Q \in [P^{4/5}/2,\ P/4]$, $X_Q := P/Q \in [4,\ 2P^{1/5}]$, $\mathcal P_Q$ = primes of $(Q, 2Q]$.
We use $\log(2Q) \ge \frac45 L$ throughout.
$$S_Q := \sum_{q\in\mathcal P_Q}\log q\cdot n_Q(q),\qquad n_Q(q) := \#\{\ell\ \text{prime},\ 3\le\ell\le P,\ q\mid N-\ell\}.$$

**7.1 Change of variable.** For $q \in \mathcal P_Q$: $\ell = N - bq \in [3, P]$ with $\ell$ prime forces
$b$ odd (since $N$ is even and $\ell$, $q$ are odd) and $b \in \mathcal I_q := [\alpha_q, \alpha'_q]$, where
$\alpha_q = (N-P)/q$ and $\alpha'_q = (N-3)/q$. Let $\mathcal A$ be the multiset of the integers $N - bq \ge 3$,
$q \in \mathcal P_Q$, $b \in \mathcal I_q$ odd, each with weight $\log q \ge 0$. Sift by the odd primes $p < D$,
$\Pi(D) = \prod_{2<p<D}p$. Every prime $\ell \in [D, P]$ is coprime to $\Pi(D)$; therefore
$$S_Q \le S(\mathcal A, D) + \sum_{\ell<D}\ \sum_{q\mid N-\ell}\log q \le S(\mathcal A, D) + D\,KL.\qquad(7.0)$$

**7.2 Exact count in a progression** (rederived). Let $m \ge 1$, $\beta \in \mathbb Z$, $\alpha \le \alpha'$ real, and
$\psi(y) := y - \lfloor y\rfloor - \frac12$ for every real $y$. Then
$$\#\{b\in\mathbb Z:\ \alpha\le b\le\alpha',\ b\equiv\beta\ (m)\} = \#\Bigl\{k\in\mathbb Z:\ \tfrac{\alpha-\beta}m\le k\le\tfrac{\alpha'-\beta}m\Bigr\} = \Bigl\lfloor\tfrac{\alpha'-\beta}{m}\Bigr\rfloor - \Bigl\lceil\tfrac{\alpha-\beta}{m}\Bigr\rceil + 1.$$
With $\lfloor y\rfloor = y - \frac12 - \psi(y)$ and $\lceil y\rceil = -\lfloor -y\rfloor = y + \frac12 + \psi(-y)$:
$$= \frac{\alpha'-\alpha}{m} - \psi\Bigl(\frac{\alpha'-\beta}{m}\Bigr) - \psi\Bigl(\frac{\beta-\alpha}{m}\Bigr).\qquad(7.1)$$
This is exact for every real $\alpha \le \alpha'$, with no exceptional cases.

**7.3 Local densities.** Let $d \mid \Pi(D)$ with $d < D^2$. Then $d$ is odd and squarefree, and $d < Q < q$,
so $(q, d) = 1$; this holds also when $\gcd(d, N) > 1$. Write $\bar q$ for the inverse of $q$ mod $d$.
Then $d \mid N - bq \iff b \equiv N\bar q \pmod d$. Since $d$ is odd, CRT says that "$b$ odd and
$b \equiv N\bar q\ (d)$" is a single class $\beta_q \bmod 2d$, which depends only on $q \bmod d$.
By (7.1) with $m = 2d$:
$$\mathcal A_d = \frac{\mathcal X}{d} + r_d,\qquad \mathcal X := \sum_{q\in\mathcal P_Q}\log q\,\frac{P-3}{2q},$$
$$r_d = -\sum_{q\in\mathcal P_Q}\log q\,\bigl[\psi(x'_q) + \psi(x_q)\bigr],\qquad x'_q = \frac{\alpha'_q-\beta_q}{2d},\quad x_q = \frac{\beta_q-\alpha_q}{2d}.$$
So $g(d) = 1/d$ is multiplicative with $0 < g(p) = 1/p < 1$: a sieve of dimension 1.

**7.4 Vaaler and integer points.** Vaaler's inequality is stated for $\psi^*$ ($= \psi$ off $\mathbb Z$, $= 0$ on $\mathbb Z$),
and $|\psi - \psi^*| \le \frac12\mathbf 1_{\mathbb Z}$. If $x'_q \in \mathbb Z$, then $\alpha'_q \in \mathbb Z$ (since $\beta_q, 2d \in \mathbb Z$),
so $q \mid N-3$. Likewise $x_q \in \mathbb Z \Rightarrow q \mid N-P$. Each case concerns at most
$\log N/\log Q \le 1.3K$ primes, so the integer points cost at most $1.3K\log(2Q) \le 1.3KL$.
For $\psi^*$, Vaaler with $H \ge 1$ gives
$$\Bigl|\sum_q\log q\,\psi^*(x_q)\Bigr| \le \sum_{1\le|h|\le H}\frac{|T_h|}{2\pi|h|} + \frac{1}{2H+2}\Bigl(\theta_Q + \sum_{1\le|h|\le H}|T_h|\Bigr) \le \frac{\theta_Q}{2H} + (2+\log H)\max_{1\le|h|\le H}|T_h|,$$
with $T_h = \sum_q\log q\,e(hx_q)$ and $\theta_Q = \sum_{q\in\mathcal P_Q}\log q \le 2Q$. Adding the two endpoints:
$$|r_d| \le \frac{2Q}{H} + 2(2+\log H)\max_{h,\pm}|T^\pm_h| + 1.3KL.\qquad(7.2)$$

**7.5 The periodic factor.** $e(hx'_q) = e\bigl(h\frac{N-3}{2dq}\bigr)\,G^+_h(q)$ and
$e(hx_q) = e\bigl(-h\frac{N-P}{2dq}\bigr)\,G^-_h(q)$, where $G^\pm_h(q) = e(\mp h\beta_q/(2d))$ depends only on
$q \bmod d$ and has modulus 1. On the group $(\mathbb Z/d)^\times$:
$$G = \sum_{\chi\bmod d}\hat G(\chi)\chi,\qquad \hat G(\chi) = \frac{1}{\varphi(d)}\sum_{a\in(\mathbb Z/d)^\times}G(a)\bar\chi(a),\qquad \sum_\chi|\hat G(\chi)|^2 = \frac{1}{\varphi(d)}\sum_a|G(a)|^2 = 1.$$
By Cauchy–Schwarz, $\sum_\chi|\hat G(\chi)| \le \varphi(d)^{1/2} \le \sqrt d$. Hence, with $Y = \pm h(N-3)/(2d)$ or $\mp h(N-P)/(2d)$:
$$|T^\pm_h| \le \sqrt d\,\max_\chi\Bigl|\sum_{q\in\mathcal P_Q}\chi(q)\log q\,e(Y/q)\Bigr| \le \sqrt d\Bigl(\max_\chi\Bigl|\sum_{Q<n\le2Q}\Lambda(n)\chi(n)e(Y/n)\Bigr| + 3\sqrt Q\,L\Bigr),$$
the last term bounding the prime powers $p^k \le 2Q$, $k \ge 2$.

**7.6 Applying Prop. 16.3χ.** $X = 2Q$, $I = (Q, 2Q] \subseteq (X/2, X]$. Conditions:
- $d < D^2 \le (2Q)^{1/4}$ (see §8);
- $|Y| \ge (N-P)/(2d) \ge P^4/(4D^2) \ge P^{3.8} \ge Q^2/16 = X^2/64$;
- $\Omega = \log(2|Y|) \le \log(2HN) \le (K+1)L$ as long as $2H \le P$.

Hence $\max_\chi|\cdots| \le C_T\,2Q\,(\log 4Q)^5\,\mathcal E_Q$, with
$$\mathcal E_Q := (2Q)^{-1/310} + \exp\Bigl(-c_*\frac{(\log 2Q)^3}{(K+1)^2L^2}\Bigr),\qquad \log\mathcal E_Q^{-1} \ge \Lambda_K := \min\Bigl(\frac{L}{400},\ c_2\frac{L}{K^2}\Bigr) - 1,$$
using $(\log 2Q)^3 \ge 0.512L^3$ and $(K+1)^2 \le \frac{25}{16}K^2$, so $c_2 = c_*\cdot0.512\cdot\frac{16}{25} \approx 4.0\cdot10^{-8}$. Combining with (7.2):
$$|r_d| \le \frac{2Q}{H} + C\,\sqrt d\,(2+\log H)\bigl(Q\,L^5\mathcal E_Q + \sqrt Q\,L\bigr) + 1.3KL.\qquad(7.3)$$

---

## 8. Selberg level, remainder term by term

**Sieve used.** Halberstam–Richert Th. 3.2: for nonnegative weights and $\mathcal A_d = g(d)\mathcal X + r_d$
($d \mid \Pi(D)$, $g$ multiplicative, $0 \le g(p) < 1$),
$$S(\mathcal A, D) \le \frac{\mathcal X}{G(D)} + \sum_{d<D^2,\ d\mid\Pi(D)}3^{\omega(d)}|r_d|.$$
The weights $\lambda_d$ satisfy $|\lambda_d| \le 1$, and $3^{\omega(d)} = \tau_3(d)$ counts the pairs $(d_1, d_2)$ with $[d_1, d_2] = d$
($d$ squarefree). The proof ($\sum w_n(\sum_{d\mid a_n}\lambda_d)^2$) holds for arbitrary nonnegative weights.
Here $h(p) = g(p)/(1-g(p)) = 1/(p-1)$, so
$$G(D) = \sum_{d<D,\ d\ \text{odd, squarefree}}\frac{1}{\varphi(d)} \ge \frac12\sum_{n<D}\frac1n \ge \frac12(\log D - 1).$$

**Choice of $H$ and $D$.** $H := D^2L^4$ (so $\log H \le 2L$ and $2H \le P$), and
$$D^3 := X_Q\,\mathcal E_Q^{-1}L^{-10}.$$
**Uniform bounds:** $\mathcal E_Q \ge (2Q)^{-1/310} \ge P^{-1/310}$ and $X_Q \le 2P^{1/5}$ give
$$D^3 \le 2P^{0.2033},\qquad D^2 \le 2^{2/3}P^{0.1356} < (P^{4/5})^{1/4} \le (2Q)^{1/4},\qquad D^2 < Q.$$
**Lower bound on $D$:** for $K \le 32000(1+\log L)$ and $P \ge P_0$, $\Lambda_K \ge 40\log L$, so
$D^3 \ge 4L^{30} \ge 8$.

**Remainder.** We use $\sum_{d\le y}\tau_3(d) \le y(1+\log y)^2$ and $\sum_{d\le y}\tau_3(d)\sqrt d \le y^{3/2}(1+\log y)^2$
(the latter because $\sum_{abc\le y}1 \le y\sum_{a,b\le y}\frac1{ab}$), with $y = D^2$ and $1 + \log y \le L$. By (7.3):

| Term | Bound | Comparison with $P/L$ |
|---|---|---|
| $\frac{2Q}{H}\sum\tau_3$ | $\le 2Q\cdot D^2L^2/(D^2L^4) = 2Q/L^2$ | $\le P/(2L^2)$ ✓ |
| $C\,QL^5\mathcal E_Q(2+\log H)\sum\tau_3\sqrt d$ | $\le 3C\,QL^8\mathcal E_Q D^3 = 3C\,QX_Q/L^2 = 3CP/L^2$ | $o(P/L)$ ✓ |
| $C\sqrt Q\,L(2+\log H)\sum\tau_3\sqrt d$ | $\le 3C\sqrt Q\,L^4D^3 \le 6C\,P^{0.5+0.2033}L^4$ | $= O(P^{0.71}L^4) = o(P/L)$ ✓ (**correction 1**) |
| $1.3KL\sum\tau_3$ | $\le 1.3KL^3D^2 \le 3KP^{0.136}L^3$ | $o(P/L)$ ✓ |

So $\sum_{d<D^2}\tau_3(d)|r_d| \le P/L$ for $P \ge P_0$, uniformly over every admissible $Q$, $N$ and $K$.

**Main term.** $\mathcal X \le \frac P2\sum_{Q<q\le2Q}\frac{\log q}{q} \le \frac P2(\log 2 + c/L)$, and
$\log D = \frac13(\log X_Q + \log\mathcal E_Q^{-1}) - \frac{10}3\log L \ge \frac13(\log X_Q + \Lambda_K) - \frac{10}{3}\log L$. Hence
$$\frac{\mathcal X}{G(D)} \le \frac{P(\log2 + c/L)}{\log D - 1} \le \frac{3P(\log 2 + c/L)}{\log X_Q + \Lambda_K - 10\log L - 3} \le \frac{3P}{\log X_Q + \Lambda_K/2},$$
since $\Lambda_K \ge 40\log L$ and $\log 2 + c/L < 1$. With (7.0):
$$S_Q \le \frac{3P}{\log X_Q + \Lambda_K/2} + \frac{2P}{L}\qquad\bigl(Q\in[P^{4/5}/2, P/4],\ P\ge P_0\bigr).\qquad(8.1)$$

---

## 9. Budget, partition, and Theorem W

$\log B = \sum_q\sum_{b\ge1}\log q\,(n(q^b)-1)_+$ ([CC] (14.4); in Lean, $B$ is defined and (17.4) proved).
A term is nonzero only if $q^b \le (P-3)/2$: two distinct odd indices in the same class differ by a
nonzero multiple of $2q^b$. Primes $q \mid N$ contribute 0, since $n(q) \le 1$.

**9.1 Exact partition (correction 2).** Let $J$ be the largest integer with $2^J \le P^{1/5}$, and $Q_j := P/2^{j+1}$
for $1 \le j \le J$. Then $(Q_J, P/2] = \bigsqcup_{j=1}^J(Q_j, 2Q_j]$ **exactly** (full blocks, no truncated block),
$Q_1 = P/4$, and $Q_J = P/2^{J+1} \in [P^{4/5}/2, P^{4/5})$ because $2^{J+1} > P^{1/5}$. **Every $Q_j$ is admissible**
(§7). Primes $q \le Q_J$ all satisfy $q < P^{4/5}$ and are handled in 9.2 without the improved sieve.

**9.2 Contributions.**
- **(a) $b = 1$, $3 \le q \le Q_J$, $q \nmid N$.** Brun–Titchmarsh: $n(q) \le 2P/((q-1)\log(P/q))$, and $\log(P/q) \ge L/5$. Hence
$$\le \frac{10P}{L}\sum_{q<P^{4/5}}\frac{\log q}{q-1} \le \frac{10P}{L}\Bigl(\tfrac45L + 1\Bigr) \le 8P + \frac{10P}{L}.$$
- **(b) $b \ge 2$.** $q^b \le P/2$ gives $\log(P/q^b) \ge \log 2$, so
$$\le \frac{2P}{\log 2}\sum_{q\ge3}\frac{\log q}{(q-1)^2} \le \frac{2P}{\log 2}\cdot0.533824 \le 1.5403P.$$
  The constant $0.533824$ is the exact sum over $q \le 10^7$ ($0.5338215$, computed) plus a tail
  $\le \sum_{n>10^7}\log n/(n-1)^2 \le (\log 10^7 + 2)/(10^7-1) < 2\cdot10^{-6}$.
- **(c) $b = 1$, $Q_J < q \le P/2$.** Since $(n-1)_+ \le n$, this is $\le \sum_{j=1}^JS_{Q_j}$. By (8.1) with $X_{Q_j} = 2^{j+1}$,
  comparing with an integral (the integrand is decreasing):
$$\sum_{j=1}^J\frac{3P}{(j+1)\log 2 + \Lambda_K/2} \le \int_0^J\frac{3P\,dt}{t\log 2 + \Lambda_K/2} = \frac{3P}{\log 2}\log\Bigl(1 + \frac{2J\log2}{\Lambda_K}\Bigr),$$
  and $\sum_j 2P/L \le 2JP/L \le P$. Since $J\log 2 \le L/5$ and $L/\Lambda_K \le 2\max(400, K^2/c_2)$ for $P \ge P_0$:
$$(c) \le \frac{3P}{\log 2}\log\Bigl(1 + \frac45\max\Bigl(400,\frac{K^2}{c_2}\Bigr)\Bigr) + P.$$

**9.3 Upper bound.** *Bookkeeping (correction):* (a) contains an extra $10P/L$. We absorb it explicitly in the
slack of (b): $(a)+(b) \le 8P + \frac{10P}{L} + 1.5403P \le 9.6P$ as soon as $10/L \le 0.0597$, i.e. $\log P \ge 168$,
which $P \ge P_0$ already implies ($\log P_0 \gtrsim 2.3\cdot10^{23}$, §9.5). Together with the $+P$ from (c), this gives exactly the
constant $10.6$ below; neither $10.6$ nor $K_0$ changes. For $4 < K \le 32000(1+\log L)$ and $P \ge P_0$:
$$\log B \le P\Bigl(10.6 + \frac{3}{\log 2}\log\Bigl(1 + \frac{4K^2}{5c_2}\Bigr)\Bigr) \le C_0P(1 + \log K),$$
with $C_0$ absolute: $\frac{3}{\log 2}(2\log K + \log(2\cdot10^7) + 1) + 10.6$, since $K^2/c_2 > 400$.

**9.4 Lower bound.** For $N > P^{3/2}$:
- Lean `factor_one_budget`: $(N-P)^{1+a+e} \le B$.
- Lean `geomAbs_subset_absent`: $a \ge G(N,P)$.
- [CC] (17.47), unverified: $G(N,P) \ge 3P/(20L)$ for $P \ge P_2$.
- For $N > P^4$: $\log(N-P) \ge KL - 1$.

Hence $\log B \ge \frac{3P}{20L}(KL - 1) \ge \frac{3}{20}KP - P$, **without any implicit $o(1)$**.

**9.5 Theorem W.** Combining 9.3 and 9.4 for $K > 4$:
$$\frac{3}{20}K \le 11.6 + \frac{3}{\log 2}\log\Bigl(1 + \frac{4K^2}{5c_2}\Bigr).$$
The right-hand side grows like $\log K$, so this forces $K \le K_0$. Numerically (computed),
$K_0 = 959$, with $c_2 = 4.0\cdot10^{-8}$ (smallest integer $K$ beyond which the inequality fails).

> **Theorem W (conditional on [CC] Th. 15.1 and (17.47)).** There is an effective $P_0$ such that every
> restricted-support family with $P \ge \max(P_0, P_1, P_2)$ satisfies $N \le P^{K_0}$ with $K_0 = 959$.
> $P_0$ depends on the implied constants of van der Corput, of [MRSTT] Lemma 4.1 and of Selberg/Mertens;
> it is effective but not computed. **The condition $\Lambda_K \ge 40\log L$ with $K$ up to $32000(1+\log L)$ alone
> requires $\log P \gtrsim 2.3\cdot10^{23}$**: the theorem is asymptotic, with no numerical range.

---

## 10. Consequence for Wall II

- **Residual region.** It narrows from $P < N < P^{14\log\log P}$ to $P < N \le P^{959}$, **under the two
  unverified inputs of §0**.
- **Wall II is not closed.** For $P^{3/2} < N \le P^{K_0}$, (9.3) and (9.4) are compatible. For typical $N$,
  $\log B$ really is of order $P$, so this argument can produce no contradiction there.

---

## 11. Audit verdict

**Verified in this audit (checked line by line):**
- Lemma S: every hypothesis of [MRSTT] 4.1, including the range of $r$ and (4.3), with explicit numbers.
- Vaughan's identity with $\chi$: only complete multiplicativity is used, and $\chi(ab) = \chi(a)\chi(b)$ for every $a, b$.
- Type I: residue classes; uniformity in $d \le X^{1/4}$; $|A| \ge Z^{3/2}$ (via $A/Z^{3/2} \ge 0.044X^{1/2}$);
  the stray endpoint; partial summation.
- Type II: Cauchy–Schwarz over all $m$; exact intervals $J(v_1, v_2)$; norms; diagonal; off-diagonal via
  Lemma S with $s = 0$.
- Uniformity in $Y$ (no upper bound needed).
- (7.1); integer points; Vaaler; the Fourier expansion of $G_h$ ($\sqrt{\varphi(d)}$ loss); the four remainder
  terms; the choice of $D$; $G(D)$; $\mathcal X$; the partition; contributions (a)–(c).

**Unverified inputs** (in [CC], used as they stand):
- **Th. 15.1:** $\log N \le 32000\log P(1+\log\log P)$. It enters twice: to bound $K$ (so that
  $\Lambda_K \ge 40\log L$), and through (17.30) in the proof of Prop. 17.13.
- **Prop. 17.13 / (17.47):** $G(N,P) \ge 3P/(20\log P)$ for $N > P^{3/2}$. It relies on Lemma 17.12 (exponential
  sums over primes on proportional intervals, Prop. 16.2/16.3 of [CC]) and on an effective prime number theorem.

**External results** (published, not reproved): van der Corput, [MRSTT] Lemma 4.1, Vaaler, Selberg (Halberstam–Richert),
Montgomery–Vaughan Brun–Titchmarsh, Rosser–Schoenfeld.

**Remaining gaps:**
1. Independent verification of Th. 15.1 and of Prop. 17.13 in [CC]. Without them: Prop. 16.3χ and (8.1) remain
   valid unconditionally (for $K \ll (L/\log L)^{1/2}$); Theorem W does not.
2. Nothing in this document has been formally verified (Lean); only (17.1), (17.4), (17.6) and $a \ge G$ have been.
3. No independent human reading yet.

**Next obstruction (if Theorem W is accepted).** In $P^{3/2} < N \le P^{K_0}$, the budget method has reached its
natural order ($\log B \asymp P$). Two targets remain:
- **(i)** Problem 19.11 of [CC]: a power saving $\mathcal H^{-\kappa}$ for the centered fixed-$N$ correlation in the
  band $3/2 \le \log N/\log P \le 5/3$.
- **(ii)** **No reduction yet exists for $5/3 < \log N/\log P \le K_0$.**

Target (ii) is the strongest open obstruction. Now that the height is polynomial, Prop. 16.3χ gives savings
$P^{-c_*/K_0^2}$ that are uniform in $N$. The natural next statement would be an extension of the exceptional-set
theorem 17.16 of [CC] (Selberg + Bombieri–Vinogradov + large sieve) to every fixed band
$P^{2-\epsilon} < N \le P^{K_0}$, followed by a pointwise exclusion of the exceptional set.
