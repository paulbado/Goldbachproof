# Hypothesis T: character-twisted Proposition 16.3 and its consequence for Wall II

Reference: I. O. Bado, *A Closure Chain Toward Williamson's Conjecture* (2026),
DOI 10.13140/RG.2.2.34840.97281, cited "[CC]". Equation numbers (13.x), (16.x), (17.x)
refer to [CC].

## 0. Status and dependencies

This document proves Proposition 16.3χ (§1–§6) and derives a polynomial height bound
(Theorem W, §7–§9). **It has not been refereed.** All constants are absolute and effective,
but they are not computed numerically.

External inputs, used as stated and not reproved here:

| Input | Exact statement used |
|---|---|
| (13.3) van der Corput | if $\lambda \le |f^{(k)}| \le B\lambda$ on $J$, $|J|\le Z$, $k\ge2$: $\sum_{n\in J} e(f(n)) \ll_{k,B} Z\lambda^{1/(2^k-2)} + Z^{1-2^{2-k}}\lambda^{-1/(2^k-2)}$ |
| [MRSTT] Lemma 4.1 | Matomäki–Radziwiłł–Shao–Tao–Teräväinen, arXiv:2106.03335, Lemma 4.1 (from Iwaniec–Kowalski Th. 8.25); statement reproduced in §2 |
| (16.15) of [CC] | unshifted reciprocal sums on intervals, which rests on Green–Harper, GAFA 24 (2014), Prop. 4.3 |
| Vaaler | for $H\ge1$ there are $c_h$, $|c_h|\le 1/(2\pi|h|)$, such that for every real $x$: $\bigl|\psi^*(x) - \sum_{1\le|h|\le H} c_h e(hx)\bigr| \le \frac{1}{2H+2}\sum_{|h|\le H}\bigl(1-\frac{|h|}{H+1}\bigr)e(hx)$, with $\psi^*(x) = \{x\}-\tfrac12$ off $\mathbb Z$ and $0$ on $\mathbb Z$ |
| Selberg's upper bound sieve | Halberstam–Richert Th. 3.2, with $|\lambda_d|\le1$ |
| Mertens, Brun–Titchmarsh | explicit forms as in [CC] (14.7), (17.26) |
| Results of [CC] | Th. 17.14, Prop. 17.9 / (17.26), Prop. 17.10, (17.47); (17.1) and (17.6) are formalized in Lean (`WilliamsonMurIIRatio.lean`) |

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
coefficients, whose moduli were bounded first. The rest is the proof of Prop. 16.3 in [CC] §16.6,
verbatim. For $h = |v_1 - v_2| \ge 1$, the coefficient $Yh/(v_1v_2)$ is at least $M^{3/2}$ (since
$F \ge X/(256L) \ge M^{1/2}$, which uses only $ML < X$ and $|Y| \ge X^2/64$) and at most $Y$.
Moreover $\log M \ge \tfrac25\log X$, so (16.15) bounds every off-diagonal sum by $O(M\mathcal E_{II})$,
$$\mathcal E_{II} = X^{-1/155} + \exp\bigl(-c_V(\log X)^3/(125\,\Omega^2)\bigr).$$
The diagonal costs $O(L^{-1})$ and the coefficients are bounded by (16.9). This gives
$$|\mathcal S_{M,L}|^2 \ll X^2L_X^6\bigl(L^{-1} + \mathcal E_{II}\bigr),\qquad |S_{II}| \ll X L_X^5\bigl(X^{-1/12} + \mathcal E_{II}^{1/2}\bigr).$$

---

## 6. Conclusion of Proposition 16.3χ

Put $c_* = \min\bigl(c_V/250,\ c_1(2/5)^3/2\bigr)$. Then $\mathcal E_I \le \mathcal E_I^{1/2}$ and
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

**Setting.** Restricted-support family with $P^4 < N < P^{14\log\log P}$ ([CC] Th. 17.14).
Put $L = \log P$, $K = \log N/L \in (4, 14\log\log P)$, a dyadic scale $Q \in [P^{4/5}, P/4]$,
$X_Q := P/Q \ge 4$, $H \ge 1$ and $D \ge 2$ with $D^2 \le Q^{1/4}$ (checked in §8). Let $\mathcal P_Q$
be the primes of $(Q, 2Q]$, and
$$S_Q(N) = \sum_{q\in\mathcal P_Q}\log q\cdot\#\{\ell\le P\ \text{prime}:\ \ell\ge3,\ q\mid N-\ell\}.$$

**Change of variable.** $\ell = N - bq$ with $b$ odd, and
$b \in \mathcal I_q := [\alpha_q, \alpha'_q]$, where $\alpha_q = (N-P)/q$ and $\alpha'_q = (N-3)/q$.
Weighted multiset $\mathcal A = \{(N - bq;\ \log q)\}$. Sifting by $\Pi(D) = \prod_{2<p\le D}p$:
every prime $\ell \in (D, P]$ survives. The primes $\ell \le D$ contribute at most
$\pi(D)\log N \le DKL$ to $S_Q$.

**Local densities.** Let $d \mid \Pi(D)$ with $d \le D^2$. Then $d$ is odd and squarefree, and
$d < Q$, so $(q, d) = 1$. Hence $d \mid N - bq \iff b \equiv N\bar q \pmod d$; together with $b$
odd, this is one class $\beta_q \bmod 2d$ (CRT, $d$ odd), **determined by $q \bmod d$**. With
$\psi(x) = x - \lfloor x\rfloor - \tfrac12$, the exact count is
$$\#\{b\in[\alpha,\alpha'] : b\equiv\beta\ (2d)\} = \frac{\alpha'-\alpha}{2d} - \psi\Bigl(\frac{\alpha'-\beta}{2d}\Bigr) - \psi\Bigl(\frac{\beta-\alpha}{2d}\Bigr),$$
which follows from $\lfloor x\rfloor - \lceil y\rceil + 1$ and $\lceil y\rceil = -\lfloor -y\rfloor$. Therefore
$$\mathcal A_d = \frac{\mathcal X}{d} + R_d,\qquad \mathcal X = \sum_{q\in\mathcal P_Q}\log q\,\frac{P-3}{2q},\qquad g(d) = 1/d.$$

**Bound on $R_d$.** Vaaler's inequality is stated for $\psi^*$, and $\psi^* \neq \psi$ only on
$\mathbb Z$. The arguments are integers only if $q \mid N-3$ or $q \mid N-P$, which happens for at
most $2\log N/\log Q$ primes $q$; this contributes $O(KL)$. For the rest, Vaaler gives
$$|R_d| \le \frac{\theta(2Q)}{H+1} + 2\,(2+\log H)\max_{1\le|h|\le H}\max_\pm|T^\pm_h| + O(KL),$$
$$T^\pm_h = \sum_{q\in\mathcal P_Q}\log q\cdot G^\pm_h(q)\cdot e\bigl(\pm hY^\pm/q\bigr),\qquad Y^+ = \frac{N-3}{2d},\ Y^- = \frac{N-P}{2d},$$
where $G^\pm_h(q) = e(\mp h\beta_q/(2d))$ depends only on $q \bmod d$ and has modulus 1 on reduced
classes. On $(\mathbb Z/d)^\times$, $G = \sum_\chi\hat G(\chi)\chi$ with
$\sum_\chi|\hat G(\chi)|^2 = \varphi(d)^{-1}\sum_a|G(a)|^2 = 1$, hence
$\sum_\chi|\hat G(\chi)| \le \varphi(d)^{1/2}$ **(this is the $\sqrt d$ loss)**. Replacing the primes
by $\Lambda$ costs $O(\sqrt Q\log Q)$. Apply Prop. 16.3χ with $X = 2Q$ and $I = (Q, 2Q]$:
- $d \le D^2 \le (2Q)^{1/4}$;
- $|hY^\pm| \ge N/(4d) \ge P^4/(4P) \ge Q^2/16 = X^2/64$;
- $\Omega \le \log(2HN) \le (K+1)L$ as long as $H \le P$.

This gives
$$|R_d| \ll \frac{Q}{H} + \sqrt d\,(\log H)\bigl(Q\,L^5\,\mathcal E_Q + \sqrt Q\,L\bigr) + KL,\qquad \mathcal E_Q := Q^{-1/310} + \exp\Bigl(-c_*\frac{(\log 2Q)^3}{(K+1)^2L^2}\Bigr).\qquad(7.1)$$

---

## 8. Selberg level, with every loss counted

Selberg (with $|\lambda_d| \le 1$; the number of pairs with $[d_1, d_2] = d$ is at most $\tau_3(d)$):
$$S_Q \le \frac{\mathcal X}{G(D)} + \sum_{d\le D^2,\ d\mid\Pi(D)}\tau_3(d)|R_d| + DKL,\qquad G(D) = \sum_{\substack{d<D\\ d\ \text{odd, squarefree}}}\frac{1}{\varphi(d)} \ge \tfrac12\log D.$$
We use $\sum_{d\le y}\tau_3(d) \le y(1+\log y)^2$ and $\sum_{d\le y}\tau_3(d)\sqrt d \le y^{3/2}(1+\log y)^2$,
with $y = D^2 \le P$ and $H := D^2L^4$ (so $\log H \le 3L$). By (7.1), the remainder is
$$\ll \frac{QD^2L^2}{H} + D^3L^{8}\,Q\,\mathcal E_Q + D^3\sqrt Q\,L^{4} + D^2KL^3.$$
The target is $\ll P/L = QX_Q/L$.
- *First term:* $= Q/L^2$. ✓
- *Third term:* fine as long as $D^3 \le \sqrt Q$.
- *Fourth term:* ✓.
- *Second term:* fine as long as **$D^3 \le X_Q\,\mathcal E_Q^{-1}L^{-9}$**. This is where the $\sqrt d$ loss
  enters: it fixes the exponent $3$, nothing more.

So we take $D^3 := X_Q\mathcal E_Q^{-1}L^{-10}$ (when this is $\ge 8$; otherwise we use Brun–Titchmarsh,
$S_Q \ll P/\log X_Q$). **Compatibility:** $\mathcal E_Q \ge Q^{-1/310}$, so
$D^2 \le (P^{1/5}P^{1/310})^{2/3} \le P^{0.14} \le Q^{1/4}$ and $D^3 \le P^{0.21} \le \sqrt Q$. ✓

**Size of $\log D$.** Since $\log 2Q \ge \tfrac45 L$ and $K \ge 4$,
$$\log\mathcal E_Q^{-1} \ge \min\Bigl(\frac{L}{400},\ c_2\frac{L}{K^2}\Bigr) - 1 =: \Lambda_K,\qquad c_2 = c_*(4/5)^3(16/25).$$
For $K \le 14\log\log P$ and $P$ large, $\Lambda_K \ge 40\log L$. Mertens gives
$\mathcal X \le \tfrac P2(\log 2 + O(1/L))$. Hence
$$S_Q \le \frac{3(\log 2+o(1))\,P}{\log X_Q + \Lambda_K - 10\log L} + O\Bigl(\frac PL\Bigr) \le \frac{3P}{\log X_Q + \Lambda_K/2} + O\Bigl(\frac PL\Bigr).\qquad(8.1)$$
This is uniform in $N$, with absolute effective constants.

---

## 9. Budget and polynomial height (Theorem W)

$\log B = \sum_q\sum_{b\ge1}\log q\,(n(q^b)-1)_+$ ([CC] (14.4)), and only $q^b \le (P-3)/2$
contribute.
- **$q \le P^{4/5}$, $b = 1$:** Brun–Titchmarsh and the partial summation of (17.26)–(17.27), stopped at
  $P^{4/5}$, give $\le 2P\log 5 + O(P)$.
- **$b \ge 2$:** $o(P)$ by Prop. 17.10.
- **$P^{4/5} < q \le P/2$, $b = 1$:** $(n(q)-1)_+ \le n(q)$, so the total is $\le \sum_{Q = P/2^{j+1},\ 1\le j\le J}S_Q$
  with $J = \lceil\tfrac15\log_2 P\rceil$. By (8.1),
$$\sum_j\frac{3P}{j\log2 + \Lambda_K/2} + O\Bigl(\frac{JP}{L}\Bigr) \le \frac{3P}{\log 2}\log\Bigl(1 + \frac{2J\log2}{\Lambda_K}\Bigr) + O(P) \le \frac{3P}{\log2}\log\Bigl(1 + \frac{1}{2}\max\Bigl(400,\frac{K^2}{c_2}\Bigr)\Bigr) + O(P).$$
(We compare the sum with $\int_0^J dj/(j\log2 + \Lambda_K/2)$, the integrand being decreasing, plus the first term $\le 6P/\Lambda_K$; and $2J\log2 \le \tfrac25 L + 2$.)

Hence, **for every restricted-support family with $P^4 < N < P^{14\log\log P}$:**
$$\log B \le C_0\,P\,(1 + \log K)\qquad(P \ge P_0).\qquad(9.1)$$

**Lower bound.** By (17.6) (Lean: `factor_one_budget`) and $a \ge G$ (Lean: `geomAbs_subset_absent`),
$\log B \ge (1 + a)\log A$. By (17.47), $G(N, P) \ge \frac{3P}{20\log P}$ for $N > P^{3/2}$ and
$P \ge P_1$. Since $\log A = KL - o(1)$,
$$\tfrac{3}{20}\,K\,P\,(1 - o(1)) \le C_0\,P\,(1 + \log K).$$

> **Theorem W (polynomial height).** There are absolute effective constants $P_0, K_0$ such that every
> restricted-support family with $P \ge P_0$ satisfies $N \le P^{K_0}$.
> Here $K_0 = \max(4, K^*)$, where $K^*$ is such that $\tfrac{3}{20}K > 2C_0(1+\log K)$ for every $K > K^*$
> (it exists because $\log K = o(K)$); the factor $2$ absorbs the $1 - o(1)$ for $P \ge P_0$.

---

## 10. What this means for Wall II

- **Proved (given the inputs of §0):**
  - the residual region of [CC] Def. 18.1 narrows from $P < N < P^{14\log\log P}$ to $P < N \le P^{K_0}$;
  - in particular $\mathcal R_{\mathrm{upper}}(P) \subseteq (P^{3/2}, P^{K_0}]$;
  - Theorem 17.14 is improved from $\log N \le (C_g + o(1))\log P\log\log P$ to $\log N \le K_0\log P$.
- **Not proved:** $\mathcal R(P) = \emptyset$. **Wall II is not closed.**
  - In the range $P^{3/2} < N \le P^{K_0}$, (9.1) only gives $\log B = O(P)$ with $C_0 \ge \tfrac3{20}K$,
    which is consistent with (17.6).
  - (9.1) cannot produce a contradiction there: for typical $N$, $\log B$ really is of order $P$.
  - The fixed-degree results of [CC] §13 become applicable with $D = K_0$ fixed, but they concern
    saturation (bounded $\omega$ of a deficient complement), not the emptiness of $\mathcal R(P)$.
- **Constants:** $c_*$, $C_0$, $K_0$ are effective but not computed, since $c_V$ (from Green–Harper)
  is not explicit in the sources.

## 11. Points to check before declaring Theorem W "proved"

1. **[MRSTT] Lemma 4.1**, used in range (ii) of Lemma S: the published version should be checked
   against the arXiv statement (4.2)–(4.4) reproduced in §2.
2. **Prop. 17.9, 17.10, Th. 17.14 and (17.47) of [CC]** are used as they stand. They depend on
   Prop. 16.2/16.3 and on an effective prime number theorem; I have not re-verified them.
3. **§5 uses (16.15) as stated in [CC]**, including its passage from Green–Harper Prop. 4.3 (which is
   on $[Y, 2Y]$) to arbitrary subintervals. That passage is short but belongs to [CC].
4. **A referee review of this document.**
