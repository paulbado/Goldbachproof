# The top range by divisor switching, and Wall II under Elliott–Halberstam

Status: **research note with a written proof.** Not formalized in Lean (one algebraic step is), not independently verified.

- **Theorem S (unconditional).** A pointwise bound, with an explicit bounded constant, for the prime moduli `q ∈ (P^θ₀, P]`.
- **Corollary EH (conditional).** The Elliott–Halberstam conjecture at an explicit level `θ(K) < 1` excludes every restricted-support
  family in the band `P^{5/3} ≤ N ≤ P^{2−ε}`, for `P` large.
- **Not proved:** Lemma Ω, `WallIIAt`, Williamson, Goldbach. Corollary EH is conditional on an open conjecture.

Notation: $L = \log P$, $K = \log N/\log P$, $I = \mathbb P\cap[3,P]$, $n_N(q) = \#\{\ell\in I : q \mid N-\ell\}$,
$\mathcal M(N) = \sum_{d\le P}\Lambda(d)n_N(d)$. Theorem A, Lemma T and L1 are in `residual-region.md` and `distribution-profile.md`.

---

## 1. Theorem S

> **Theorem S.** Fix $\delta > 0$. Let $P$ be large, $N$ even with $1 + \delta \le K \le 2 - \delta$, and $\theta_0 \le 1$ with
> $1 + \theta_0 - K \ge \delta$. Then
> $$\sum_{\substack{P^{\theta_0}<q\le P\\ q\ \mathrm{prime}}}\log q\;n_N(q)\ \le\ 8P\Bigl[\frac1{1+\theta_0-K} - \frac1{2-K}\Bigr]\Bigl(1 + O_\delta\Bigl(\frac{\log L}{L}\Bigr)\Bigr) + O_\delta\bigl(P^{1-\delta/3}\bigr),$$
> uniformly in $N$. No restricted-support hypothesis is made, and no distribution estimate for primes in progressions is used.

**External input.** Halberstam–Richert, *Sieve Methods*, Theorem 5.7 (Selberg's sieve for linear forms in an interval):

> Let $a_i, b_i$ ($1 \le i \le g$) be integers with $E := \prod_ia_i\prod_{r<s}(a_rb_s - a_sb_r) \ne 0$, let $\omega(p)$ be the number of
> solutions of $\prod_i(a_in+b_i) \equiv 0 \pmod p$, and suppose $\omega(p) < p$ for all $p$. Then for $1 < y \le z$,
> $$\#\{n : z-y<n\le z,\ a_in+b_i\ \text{prime for all } i\} \le 2^gg!\prod_p\Bigl(1-\frac{\omega(p)}p\Bigr)\Bigl(1-\frac1p\Bigr)^{-g}\frac y{\log^gy}\Bigl(1 + O_g\Bigl(\frac{\log\log3y+\log\log3|E|}{\log y}\Bigr)\Bigr).$$

(The statement is quoted as it is reproduced in recent papers citing [HR, Th. 5.7]; I did not have the book itself.)

**Proof of Theorem S.**

*Step 1 (switching).* Let $q \in (P^{\theta_0}, P]$ be prime and $\ell \in I$ with $q \mid N - \ell$. Then $N - \ell = bq$ with $b$ odd
(Lean: `WilliamsonResidual.switch_pair`), and
$$B_0 := \frac{N-P}{P} \le b < B_1 := \frac{N}{P^{\theta_0}}.$$
So the sum is at most $L\cdot\#\mathcal P$, where $\mathcal P$ is the set of pairs $(b, q)$ with $b$ odd in $[B_0, B_1)$, $q$ prime, and
$N - bq$ a prime of $[3, P]$.

*Step 2 (exceptional pairs).* If an odd prime $p$ divides $\gcd(b, N)$, then $p \mid N - bq = \ell$, so $\ell = p \mid N$. There are at most
$\log N$ such $\ell$, and each $N - \ell$ has at most $K/\theta_0$ prime factors $q > P^{\theta_0}$. These pairs number $O(L)$. From now on
$\gcd(b, 2N) = 1$.

*Step 3 (fixed $b$).* Apply [HR, Th. 5.7] with $g = 2$, the forms $n$ and $-bn + N$, $z = (N-3)/b$, $y = P/b$. Every admissible $q$ lies in
$(z - y, z]$.
- $E = 1\cdot(-b)\cdot(1\cdot N - (-b)\cdot0) = -bN \ne 0$, and $\log\log 3|E| = O(\log L)$.
- $1 < P^{\delta} \le P^{1+\theta_0-K} \le y \le z$.
- $\omega(2) = 1$: $n$ even is a root; for $n$ odd, $N - bn$ is odd.
- For odd $p \mid b$ (so $p \nmid N$): the only root is $n \equiv 0$, $\omega(p) = 1$.
- For odd $p \nmid b$: the roots are $0$ and $N\bar b$; so $\omega(p) = 2$ if $p \nmid N$ and $1$ if $p \mid N$.
- Hence $\omega(p) < p$ for all $p$, and
  $$\mathfrak S(b) := \prod_p\Bigl(1-\frac{\omega(p)}p\Bigr)\Bigl(1-\frac1p\Bigr)^{-2} = 2C_2\prod_{2<p\mid bN}\frac{p-1}{p-2},\qquad C_2 = \prod_{p>2}\Bigl(1 - \frac1{(p-1)^2}\Bigr).$$

So the number of $q$ for this $b$ is at most $8\,\mathfrak S(b)\,w(b)\,(1 + O(\log L/(\delta L)))$, with $w(x) := \dfrac{P/x}{\log^2(P/x)}$.

*Step 4 (mean value of $\mathfrak S$).* Put $h(N) = \prod_{2<p\mid N}\frac{p-1}{p-2}$ and $g(d) = \mu^2(d)\prod_{p\mid d}\frac1{p-2}$ for odd $d$. For
$\gcd(b, 2N) = 1$, $\mathfrak S(b) = 2C_2h(N)\sum_{d\mid b}g(d)$. Let $S(x) := \sum_{b\le x,\ (b,2N)=1}\mathfrak S(b)$. Then
$$S(x) = 2C_2h(N)\sum_{d\le x,\ (d,2N)=1}g(d)\,\Phi(x/d),\qquad \Phi(t) := \#\{m\le t : (m,2N)=1\} = t\,\frac{\varphi(2N)}{2N} + O(2^{\omega(N)}).$$
- $\sum_{(d,2N)=1}g(d)/d = \prod_{p\nmid2N}\bigl(1 + \frac1{p(p-2)}\bigr)$, with tail $\sum_{d>x}g(d)/d \ll x^{-1/2}$, and $\sum_{d\le x}g(d) \ll \log x$.
- $C_2\prod_{p>2}\bigl(1 + \frac1{p(p-2)}\bigr) = \prod_{p>2}\frac{p(p-2)}{(p-1)^2}\cdot\frac{(p-1)^2}{p(p-2)} = 1$.
- So the main coefficient is
  $2\cdot\frac12\prod_{2<p\mid N}\frac{p-1}{p-2}\cdot\frac{p-1}p\cdot\frac{p(p-2)}{(p-1)^2} = 1$.

Hence $S(x) = x + E(x)$ with $E(x) \ll h(N)\bigl(x^{1/2} + 2^{\omega(N)}\log x\bigr) \ll x^{1/2}\log L + P^{o(1)}$.
(The factor $h(N)$ is exactly cancelled by the density of the $b$ coprime to $N$: the bound does not grow with the small prime factors of $N$.)

*Step 5 (partial summation).* $w$ is decreasing on $[B_0, B_1]$ (as $t/\log^2t$ increases for $t > e^2$), so
$$\sum_{B_0\le b<B_1}\mathfrak S(b)w(b) = \int_{B_0}^{B_1}w(x)\,dx + O\Bigl(\max_{[B_0,B_1]}|E(x)|w(x) + \int_{B_0}^{B_1}|E(x)||w'(x)|\,dx\Bigr).$$
- Error: $|E(x)|w(x) \ll PL\,x^{-1/2} + P^{1+o(1)}/x$ and the same for the integral, so the error is $\ll P^{1-(K-1)/2+o(1)} \le P^{1-\delta/3}$.
- Main term: with $v = \log(P/x)$,
  $$\int_{B_0}^{B_1}\frac{P\,dx}{x\log^2(P/x)} = P\Bigl[\frac1{\log(P/B_1)} - \frac1{\log(P/B_0)}\Bigr] = \frac PL\Bigl[\frac1{1+\theta_0-K} - \frac1{2-K}\Bigr] + O_\delta\Bigl(\frac P{L^2}\Bigr).$$

*Step 6.* Multiply by $8$ and by the weight $\log q \le L$. $\square$

**Checks.**
- *Size.* The expected value of the left side is $(1-\theta_0)P$. As $\theta_0 \to 1$ the bound is $\approx \frac{8}{(2-K)^2}(1-\theta_0)P$, i.e. a
  loss factor $8/(2-K)^2$ (72 at $K = 5/3$). This is the usual factor $8$ of the two-dimensional sieve times
  $(\log P\log q)/\log^2(P/b)$.
- *Numerics* (`scripts/switched_sieve.py`): for $P = 4001, 20011$ and 300 random $N$, the left side is $0.07P$–$0.27P$ against bounds $13P$–$80P$.
- *Why the bound does not diverge.* Brun–Titchmarsh per modulus costs $2/(1-\theta')$ at scale $q = P^{\theta'}$, which is not integrable at
  $\theta' = 1$. After switching, the sifted interval has length $P/b \ge P^{1+\theta'-K}$, a fixed power of $P$, so the cost
  $8/(1+\theta'-K)^2$ stays bounded.
- *Range.* The switching needs $q > P^{K-1}$ (otherwise $P/b < 1$). For $K \ge 5/3$ this leaves the moduli $q \in (\sqrt P, P^{K-1}]$ untouched.

**Unconditional consequences.**
1. **Quantitative Theorem B.** With $\theta_0 = 1 - \log\mathcal T/L$: $\sum_{P/\mathcal T<q\le P}\log q\,n_N(q) \le \bigl(\frac{8\log\mathcal T}{(2-K)^2} + o(1)\bigr)\frac PL$, the
   true order of magnitude, uniformly in $N$. (Theorem B of `prop-16-2-chi-top-range.md` gave $o(P)$.)
2. **A bounded pointwise constant.** Brun–Titchmarsh on $(\sqrt P, P^{\theta^*}]$ plus Theorem S above $\theta^*$ gives
   $\mathcal M(N) \le C(K)P$ with $C(5/3) \approx 8.4$. This is finite, unlike $2P\log L$, but **worse than the trivial bound $KP$**, so it excludes nothing.
3. **Profile of `distribution-profile.md`.** Near $\theta' = 1$ the effective level $\lambda(\theta') = (1+\theta'-K)^2/4$ is now available
   unconditionally, instead of the trivial $1-\theta'$.

---

## 2. Corollary EH (conditional)

**Hypothesis EH($\theta$)** (Elliott–Halberstam at level $\theta$; open for every $\theta > 1/2$): for every $A$,
$$\sum_{d\le x^\theta}\max_{(a,d)=1}\Bigl|\pi(x;d,a) - \frac{\pi(x)}{\varphi(d)}\Bigr| \ll_{A,\theta}\frac x{\log^Ax}.$$

Only the following consequence is used, for the single class $a = N$:

**Hypothesis U($\theta$, $\eta$).** For $P \ge P_0$ and every even $N$ in the band: $\sum_{d\le P^\theta}\Lambda(d)\,n_N(d) \le (\theta + \eta)P$.

EH($\theta$) implies U($\theta$, $\eta$) for every $\eta > 0$: $n_N(d) \le \pi(P;d,N)$ for $(d,N)=1$ and $n_N(d) \le 1$ otherwise, and
$\sum_{d\le P^\theta}\Lambda(d)/\varphi(d) = \theta L + O(1)$.

> **Corollary EH.** Let $J \subset [5/3, 2-\epsilon]$, $\theta < 1$ and $\eta > 0$ satisfy
> $$\theta + 8\Bigl[\frac1{1+\theta-K} - \frac1{2-K}\Bigr] \le K - 3\eta\qquad\text{for all } K \in J.$$
> If U($\theta$, $\eta$) holds, then for $P$ large no restricted-support family has $K \in J$. In particular:
> - EH($\theta$) with $\theta > 0.99087$ excludes a neighbourhood of $K = 5/3$;
> - EH($1 - \epsilon^2/13$) excludes the whole band $5/3 \le K \le 2 - \epsilon$;
> - the full Elliott–Halberstam conjecture excludes $P^{5/3} \le N \le P^{2-\epsilon}$ for every fixed $\epsilon > 0$.

*Proof.*
- $\mathcal M(N) = \sum_{d\le P^\theta}\Lambda(d)n_N(d) + \sum_{P^\theta<q\le P}\log q\,n_N(q) + (\text{prime powers } q^j > P^\theta,\ j\ge2)$.
- The first term is $\le (\theta+\eta)P$ by U. The second is $\le (8[\cdots] + o(1))P$ by Theorem S with $\theta_0 = \theta$ (here $1+\theta-K \ge$ a positive
  constant on $J$, since the displayed condition forces it). The third is $\ll P^{1-\theta/2}L + \sqrt P\,L = o(P)$, since $n_N(q^j) \le P/q^j + 1$ (`residual-region.md` §7.5(c)).
- So $\mathcal M(N) \le (K - 2\eta + o(1))P$ for **every** even $N$ with $K \in J$.
- Theorem A: a restricted-support family has $\mathcal M(N) \ge (K - o(1))P$. Contradiction for $P$ large.
- Uniform choice: with $c = 2-K \ge \epsilon$ and $u = 1-\theta < \epsilon^2/13$, $8[\cdots] = \frac{8u}{c(c-u)} < \frac23 \le K - \theta$. $\square$

Levels required (`scripts/switched_sieve.py`):

| $K$ | 5/3 | 1.75 | 1.8 | 1.9 | 1.95 |
|---|---|---|---|---|---|
| $\theta >$ | 0.99087 | 0.99423 | 0.99606 | 0.99889 | 0.99970 |

**What this does and does not say.**
- It replaces the non-standard hypothesis $(\mathrm{LD}_\lambda)$ on the dual sequences by a **standard conjecture**, at an explicit level.
- It uses EH only as a **one-sided** bound, for the **single** residue class $N \bmod d$.
- It is **not** an unconditional result. EH($\theta$) is unknown for every $\theta > 1/2$; the known extensions beyond $1/2$
  (Fouvry–Iwaniec, Bombieri–Friedlander–Iwaniec, Zhang, Polymath, Maynard) require a fixed residue or smooth moduli and do not apply to
  the class $N \bmod q$ with $q$ prime.
- GRH does not help: it gives level $1/2$, which Bombieri–Vinogradov already provides.
- It concerns only the band $5/3 \le K \le 2-\epsilon$ (the proof works for $3/2 < K$; L1 needs $N - P > P^{3/2}$). It does not close Wall II.

**Exact remaining obstruction in the band.** By Lemma T and Theorem S, Ω is equivalent to a saving on the middle moduli only:
$$\sum_{\sqrt P<q\le P^{\theta}}\log q\;n_N(q) \le \Bigl(K - \tfrac12 - 8\Bigl[\tfrac1{1+\theta-K} - \tfrac1{2-K}\Bigr] - \eta\Bigr)P\qquad\text{for all even } N \text{ in the band},$$
for one $\theta < 1$. At $K = 5/3$, $\theta = 0.999$ this asks for an upper bound within a factor $2.19$ of the expected size $(\theta - \frac12)P$.

---

## 3. Algebraic and geometric reformulations: what they give

Each item states the bridge, then what it yields. None gives an estimate beyond those above.

**(a) Chebotarev / class field theory.** $q \mid N - \ell \iff \mathrm{Frob}_\ell = \sigma_N$ in $\mathrm{Gal}(\mathbb Q(\zeta_q)/\mathbb Q) \cong (\mathbb Z/q)^\times$.
So $n_N(q)$ is a Chebotarev count in a cyclotomic field of conductor $q$. The extension is abelian, and Chebotarev there *is* the prime number
theorem in progressions. Effective Chebotarev under GRH gives an error $O(\sqrt P\log(qP))$ per modulus: level $1/2$, the same as
Bombieri–Vinogradov. **Equivalent to the original distribution problem.**

**(b) Trace functions and Deligne-type bounds.** After Vaaler's expansion, the sieve remainders are sums
$T_h(e) = \sum_{q\sim Q}\log q\;e\bigl(h\bar2N\bar q/e\bigr)\,e\bigl(hN/(2eq)\bigr)$ (`distribution-profile.md` §4). For prime $e$, $x \mapsto e(a\bar x/e)$ is the trace
function of a rank-one Artin–Schreier sheaf, and sums of trace functions over primes are the subject of Fouvry–Kowalski–Michel. Two
facts limit this route.
- *Archimedean twist.* The factor $e(hN/(2eq))$ has phase $\approx hP^{K-\lambda-\theta}$ ($e = P^\lambda$, $q = P^\theta$). It is removable by partial
  summation only when $\lambda \ge K - \theta$.
- *Even square-root cancellation is not enough.* Suppose the best possible bound $|T_h(e)| \le Q^{1/2+o(1)}$ held for all $e$, $h$. Then
  $|r_e| \le Q^{1/2+o(1)}$, the absolute Selberg remainder is $\le P^{\lambda+\theta/2+o(1)}$, and the level is $\lambda(\theta) = 1 - \theta/2$. In Proposition PF
  this gives
  $$2\int_{1/2}^1\frac{d\theta}{1-\theta/2} = 4\log\tfrac32 = 1.62 > K - \tfrac12\quad\text{for every } K \text{ in the band}.$$
  **So square-root cancellation in every individual sum $T_h(e)$, the strongest bound of Deligne type, would still not prove Ω through the Selberg sieve with absolute remainders.**
  Cancellation over the moduli $e$ (a dispersion or large-sieve argument, i.e. an EH-type statement) is necessary on this route.
- The unconditional savings available for such sums over primes are small powers of $e$ in restricted ranges; they give a level barely
  above the trivial one (compare §4 of `distribution-profile.md`).

**(c) Modular forms, elliptic curves, complex multiplication.** The splitting condition in (a) is abelian; its automorphic side is
GL(1) (Dirichlet characters). GL(2) spectral theory enters prime distribution through sums of Kloosterman sums over moduli
(Deshouillers–Iwaniec), which is how Bombieri–Friedlander–Iwaniec pass level $1/2$. Those results need a fixed small residue and
well-factorable weights; here the residue is $N \bmod q$ with $N > q^{5/3}$ and the moduli are primes. I found no construction attaching
an elliptic curve or a CM field to the family $\{N - \ell\}$ in a way that encodes "all prime factors $< P$". **No bridge found.**

**(d) Function fields.** Over $\mathbb F_q[t]$ with $q \to \infty$ and fixed degree, Goldbach-type statements are theorems, proved by computing a
Galois (monodromy) group and applying Chebotarev over finite fields. The mechanism is equidistribution in the large-$q$ limit; it has no
analogue over $\mathbb Z$, where the "field of constants" is fixed. **Does not transfer.**

**(e) $p$-adic methods, deformation theory, arithmetic duality.** I found no formulation of the restricted-support condition to which
these apply. **No bridge found.**

**Assessment.** The obstruction is a mean-value statement over moduli. The only reformulation that changes its status is §2: it
becomes a consequence of a standard conjecture. It remains open unconditionally.


---

## 4. Audit of Theorem S (2026-11-25)

Checked step by step against the sources available; no gap found. Points recorded:

- **The sieve input.** The statement used is the one quoted from [HR, Th. 5.7] in recent papers. In that quotation the only hypotheses on
  the forms are that $a_i, b_i$ are integers with $E \ne 0$, that $\omega(p) < p$ for all $p$, and that $1 < y \le z$. There is **no sign
  condition**, so the form $N - bn$ with negative leading coefficient is admissible. The constant appears there as
  $\prod_p(1 - \frac{\omega(p)-1}{p-1})(1-\frac1p)^{-g+1}$, which equals the product used in Step 3. The book itself was not consulted.
- **Interval and error term.** $z = (N-3)/b$, $y = (P-3)/b$; $y \ge P^{1+\theta_0-K-o(1)} \ge P^{\delta/2}$, so the relative error
  $O((\log\log 3y + \log\log 3|E|)/\log y)$ is $O_\delta(\log L/L)$ uniformly in $b$ and $N$ ($|E| = bN \le N^2$).
- **Local densities.** Rechecked: $\omega(2) = 1$, and for odd $p$, $\omega(p) = 1$ if $p \mid bN$ and $2$ otherwise. The pairs with
  $\gcd(b, N) > 1$ were removed in Step 2.
- **Mean of the singular series.** Rechecked: the coefficient of $x$ in $S(x)$ is $1$. The identity
  $\bigl(1 - \frac1{(p-1)^2}\bigr)\bigl(1 + \frac1{p(p-2)}\bigr) = 1$ cancels $C_2$, and the factors at $p \mid N$ cancel exactly.
- **Error terms.** $E(x) \ll h(N)(x^{1/2} + 2^{\omega(N)}\log x)$ with $h(N) \ll \log L$; the partial-summation error is
  $\ll P^{1-(K-1)/2+o(1)}$.
- **Not covered by Theorem S.** The moduli $q \le P^{K-1}$, where $P/b < 1$.

**Verdict:** Theorem S stands as stated, conditional only on the correctness of the quoted [HR, Th. 5.7].

## 5. The intermediate moduli: two further mechanisms tested

**Target** ($K = 5/3$, $\theta = 0.999$): $\sum_{\sqrt P<q\le P^{0.999}}\log q\,n_N(q) \le (1.0943 - \eta)P$, whose expected size is $0.499P$.
This is a bound within a factor $2.19$ of the truth. For comparison, Brun–Titchmarsh gives $2\log 500 \approx 12.4$.

**(i) Dual form (Lean: `WilliamsonDual.lean`).**

```lean
theorem badFamily_iff_residues (hP : 3 ≤ P) (hPN : 2 * P ≤ N) (hN : Even N) :
    BadFamily P N ↔ ∀ r, Nat.Prime r → P ≤ r → ∀ ℓ, Index P ℓ → ¬ ℓ ≡ N [MOD r]
theorem not_badFamily_iff_rep (hP : 3 ≤ P) (hPN : 2 * P ≤ N) (hN : Even N) :
    ¬ BadFamily P N ↔ ∃ ℓ r m, Index P ℓ ∧ Nat.Prime r ∧ P ≤ r ∧ ℓ + m * r = N
```

So excluding a family at $N$ means finding one solution of $\ell + mr = N$ with $\ell \le P$ and $r \ge P$ both prime. This is a **lower-bound
problem** with two prime variables.
- *Circle method.* It cannot give it pointwise: $\sum_{\ell\le P}$ has length $P = N^{1/K}$, so
  $\int|S_\ell T| \le \|S_\ell\|_2\|T\|_2 \gg PL$ already exceeds the main term.

**(ii) Chen-type route.**
- *Lower bound (unconditional).* By the linear sieve with Bombieri–Vinogradov for the primes $\ell \le P$ (level $P^{1/2}$, maximum over
  the class, hence pointwise in $N$), at least $f(s)\,XV(z)$ rows $N - \ell$ have no prime factor below $z = P^{1/(2s)}$.
- *What is needed.* It suffices to show that fewer rows are "bad", i.e. $z$-rough and $P$-smooth.
- *Buchstab model* (`scripts/chen_route.py`). The bad proportion among $z$-rough rows is $0.39$–$0.43$ at $K = 5/3$ and $0.25$–$0.28$ at
  $K = 1.95$. The upper bound for bad rows may therefore lose a factor up to $2.35$ ($K = 5/3$, $s = 4$), up to $3.6$ ($K = 1.95$).
- *Why this does not close it.* Classifying a bad row by its largest prime factor $q$ and dropping the conditions on the cofactor
  turns the upper bound back into $\sum_q n_N(q)$ over $q \in (P^{1/2-o(1)}, P)$, with the same Brun–Titchmarsh loss.
  - Keeping the cofactor conditions requires the distribution of products $p_1\cdots p_k$ in the short interval $[N-P, N]$ in
    progressions. Those with two factors near $P^{5/6}$ are only about $5\%$ of the $z$-rough rows (at $s = 4$). But for them every
    available bound (Theorem S near $\theta_0 = K-1$, or a two-dimensional sieve on a factor) loses a factor of order $10^2$.
  - Net: the margin moves from $2.19$ to about $2.35$ at $K = 5/3$ (and is larger near $K = 2$). The missing input is the same
    short-interval bilinear distribution.

**(iii) First-failure conditions.**
- Every extra condition known on a first failure is an *existence* statement. Examples: $p \mid N - j$ for some $j \le p$; at every
  smaller rank $P'$, some $r \in [P', P)$ divides some $N - \ell$ with $\ell \le P'$ (`first_failure_rank_chain`).
- These are lower bounds on incidences, in the same direction as Theorem A. They shrink the set of possible $N$, but no upper bound for
  $\sum_qn_N(q)$ proved here becomes easier on that subset. **This is an observation about the available arguments, not a theorem that no
  argument can use them.**

**Status.** No unconditional exclusion in the band. Theorem S, Lemma T, Theorem A and the Lean statements above are the proved
results. `WallIIAt` is open.
