
Main file [[Bombieri-Vinogradov]]

Proof of Bombieri-Vinogradov in [[gsm203.pdf]]:

Latex preamble (hidden):
$$\newcommand{\Z}{\mathbb{Z}} \newcommand{\N}{\mathbb{N}} \newcommand{\R}{\mathbb{R}} \newcommand{\C}{\mathbb{C}} 

\newcommand{\sumstar}{\mathop{{\sum\nolimits^{\mathrlap{*}}}}}
$$


## Prereqs

##### Theorem (Siegel-Walfisz)
Let $A > 0$. There exists an absolute constant $c > 0$ such that if $1 \leq q \leq (\log x)^A$ and $a \in (\mathbb{Z}/q\mathbb{Z})^*$, then
$$
\pi(x;q,a) = \frac{\mathrm{li}(x)}{\varphi(q)} + O_A\left(x e^{-c\sqrt{\log x}}\right).
$$

We really only need an arbitrary power of log savings.


### Main theorem (B-V)
For each fixed $A \ge 0$ we have 
$$\sum_{q\le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \pi (y; q, a) - \frac{li(y)}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A+1}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$

NOTE: The proof that follows actually holds on $x \ge e^{16}$ due to the lower bound $U, V \ge e^{\sqrt{\log x}}$. Changing this to something like $U, v \ge e^{(\log 2)/4  \sqrt{\log x}}$ might work instead, but I haven't checked what needs to change in the blueprint.

### Preliminaries
Decomposing the von Mangoldt function into type I and type II functions.

##### Def $\Delta$
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$

##### Lemma $\Delta\chi$
$$\Delta_f(y ;q, a) = \frac{1}{\varphi(q)} \sum_{\chi \pmod{q}, \chi \ne \chi_0} \bar\chi(a) \sum_{n \le y} f(n) \chi(n) $$


Notice:
$$\Delta_{1_P}(x; q, a) = \pi(x; q,a) - \frac{1}{\varphi(q)} \sum_{p \le x, p \not\mid q} 1 $$
##### Lemma 
$$ \sum_{p \le x, p \not \mid q} 1 = li(x) + O(xe^{-c\sqrt{\log x}}+\log q)$$
##### Lemma (B-V Primes)
B-V follows from

For each fixed $A \ge 0$ we have 
$$\sum_{q\le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{1_P}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A+1}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
##### Proof:
The error terms in the previous lemma are absorbed by $\frac{x}{(\log x)^{A+1}}$.


#### Switching to von Mangoldt's function.

##### Lemma
For $x \ge 2$, $q \in \N$ and $a \in (\Z / q\Z)^*$ we have
$$ \max_{y \le x} \left| \Delta_{1_P}(y; q, a) \right| \ll \frac{1}{\log x} \left(\max_{\sqrt x \le y \le x} \left|\Delta_\Lambda(y; q, a)\right| + \sqrt x \right)$$
proof. See p. 279. Uses combinatorics, an estimate on $\sum_{p \le x} 1/\log p$ and partial summation.

##### Corollary
B-V is reduced to:
For each fixed $A \ge 0$ we have 
$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$


#### Applying Vaughan's identity

##### Definition 
For $f : \N \rightarrow \R$ and $r : \N$ we use $f_r$ to denote $n \mapsto f(n) 1_{(n, r) = 1}$
##### Def
Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$ where $\Lambda^\sharp = \mu_{\le V} * \log - (\Lambda_{\le U} * \mu_{\le V}) * 1$ and $\Lambda^\flat = (\Lambda_{>U} * 1) * \mu_{>V}$. This follows chapter 23.
Here $UV \le \sqrt x$ and $U, V \ge e^{\sqrt{\log x}}$


##### Lemma
$$\Delta_{\Lambda_{\le U; r}} (y; q, a) \ll U \le \sqrt{x}$$
$$\sum_{n\le U} \Lambda_r (n) \ll U$$
Therefore

$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda_{\le U; r}}(y; q,a) \right| \le Q \sqrt{x} \ll_A \frac{x}{(\log x)^{A+2}}$$
for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log{x})^{A+3}$



What remains is the contributions of $\Lambda^\sharp$ and $\Lambda^\flat$.

#### Type I functions in arithmetic progressions


##### Lemma 
$$\Delta_{f}(x; q, a) = \sum_{n \le x; (n, q) = 1} \left[1_{n \equiv a  
~(q)} - \frac{1}{\varphi(q)}\right]f(n)$$

##### Lemma 
If $f$ is supported on $[1, y]$ then
$$
\begin{align}
\Delta_{f*g} &= \sum_{k \le y; (k, q) = 1} f(k) \left( \sum_{l \le x/k; l \equiv a \bar k} g(l) - \frac{1}{\varphi(q)} \sum_{l \le x/k; (l, q) = 1} g(l) \right)  \\

&= \sum_{k \le y; (k, q)=1} f(k) \Delta_{g}(x/k; q, a\bar k)

\end{align}
$$


##### Lemma 
If $g$ is cont. diff on $[1, x]$ then 
$$\Delta_{g}(x; q, a) = \Delta_{1}(x; q, a) g(x) - \int_{1}^{x}\Delta_1(t; q, a)g'(t) dt$$
###### Proof.
By Abel summation

##### Lemma
$$\left| \Delta_1(x; q, a) \right| \le 1$$
###### Proof
Carefully consider length q intervals.
Alternatively consider
$$\Delta_1(t; q, j) = \frac{1}{\varphi(q)} \sum_{j' \in (\mathbb{Z}/q\mathbb{Z})^*} \left( \sum_{\substack{n \le t \\ n \equiv j \pmod q}} 1 - \sum_{\substack{n \le t \\ n \equiv j' \pmod q}} 1 \right)$$


##### Lemma
If $g$ is cont. diff and monotone on $[1, y]$ and $g(0) = 0$ then for all $t \ge 1$ and $j \in (\Z / q\Z)^*$ $$\left| \Delta_{g}(x; q; a) \right| \le 2g(t)$$
##### Theorem 
Let $v \ge 0$, and let $f$ be an arithmetic function supported on $[1,y]$. For $x \ge 2$, $q \in \mathbb{N}$ and $a \in (\mathbb{Z}/q\mathbb{Z})^*$, we have
$$|\Delta_{f * \log^v}(x; q, a)| \le 2(\log x)^v \sum_{k \le y} |f(k)|.$$
###### Proof
Straightforward application of the previous lemmas


##### Corollary

For $U,V \ge 1$, $x \ge 2$, $q \in \mathbb{N}$, $r \in \N_{\le x}$ and $a \in (\mathbb{Z}/q\mathbb{Z})^*$, we have
$$\max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} |\Delta_{\Lambda^\sharp_r}(y; q, a)| \ll UV \log x.$$
###### Proof.
Apply the previous lemma twice with $f = \mu_{\le V, r}$; $\nu = 0$ and $f = \Lambda_{\le U} * \mu_{\le V; r}$; $\nu = 0$; $y = UV$.


###### Corollary

$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda_{\le U}}(y; q,a) \right| \le Q \sqrt{x} \ll_A \frac{x}{(\log x)^{A+2}}$$



#### Type II functions in arithmetic progressions

##### Lemma
For $\sqrt x \le y \le x$; $q \le (\log x)^C$; $(a, q) = 1$ and $r \in \N_{\le x}$ we have 
$$ \left| \Delta_{\Lambda_r} (y; q, a) \right| \ll_{A, C} x/(\log x)^A $$

###### Proof
Siegel-Walfisz and the PNT give us 
$$ \left| \Delta_{\Lambda} (y; q, a) \right| \ll_{A, C} x/(\log x)^A $$
And the two quantities differ by $\ll$ 
$$\sum_{(n, r) \ne 1; n \le y} \Lambda(n) = \sum_{p^k \le y; p \mid r} \log p \le \omega(r)\log y \le (\log x)^2 \ll_A x/(\log x)^A$$

##### Theorem
For $\sqrt x \le y \le x$; $q \le (\log x)^C$; $(a, q) = 1$, $r \in \N_{\le x}$ and $UV \le x/e^\sqrt{\log x}$ we have 
$$ \left| \Delta_{\Lambda_r^\flat} (y; q, a) \right| \ll_{A, C} x/(\log x)^A $$
###### Proof
Decompose $\Lambda^{\flat}_r = \Lambda_r - \Lambda^{\sharp}_r - \Lambda_{\le U; r}$
Then bound the corresponding sums using the previous theorems.


Reduction to character sums.

##### Lemma
This is a standard result.
Let $f$ be function from Dirichlet characters. Then
$$\sum_{\chi \ne \chi_0 \pmod q} f(\chi) =\sum_{d \mid q} \sum_{\xi \pmod d} ^* f(1_{(n, q)=1}\xi )$$

##### Lemma
Let $f$ be an arithmetic function.  For $r \le x$, $q > 1$ and $(q, a) = 1)$,

$$\sum_{\xi \pmod q}{}^* \bar \xi(a)\sum_{y \le n} \xi(n)f_r(n) = \sum_{d \mid q} \mu(q/d) \varphi(d) \Delta_{f_{rq}}(y; q, a)$$
###### Proof
Fix $P \in \N$ such that $q \mid P$. Define $F_P$ and $G_P$ on the divisors of $P$ by 
$$F_P(q) := \sum_{\chi \ne \chi_0 \pmod q} \bar \chi(a) \sum_{n \le y} \chi(n) f_{rP}(n) = \Delta_{f_{rP}}(y; q, a) $$
$$G_P(d) := \sum_{\xi \pmod d}{}^* \bar \xi(a) \sum_{n \le y} \xi(n) f_{rP}(n) \text{ if $d > 1$ and $0$ otherwise} $$
Then
$$\begin{align}
F_P(q) &= \sum_{\chi \ne \chi_0 \pmod q} \bar \chi(a) \sum_{n \le y} \chi(n) f_r(n) \\
&= \sum_{d \mid q} \sum_{\xi \pmod d}{}^* \bar \xi(a) \sum_{n \le y} \xi(n) f_{rP}(n) \\
&= \sum_{d \mid q} G_P(d)
\end{align}$$
So by Moebius inversion,
$$G_P(q) = \sum_{d \mid q} \mu(q/d) G_P(d) = \sum_{d \mid q} \mu(q/d) \Delta_{f_{rP}}(y; d, a)$$
Then fix $P = q$. QED


In the remainder of this section, assume $\sqrt x \le y \le x$ and $a \in \Z/q\Z$


##### Theorem
$$\left| \Delta_{\Lambda^\flat}(y; q,a)\right| = \frac{1}{\varphi(q)} \left|\sum_{d \mid q; d>1; \xi \pmod d}^* \bar \xi(a) \sum_{y \le n} \Lambda_{q/d}^\flat(n) \xi(n)\right|$$
Note that there is some overlap with the previous theorem here for grouping the character sum by conductor.

##### Definition
$$S_r(y, \chi) := \left|\sum_{n \le y} \Lambda_r^\flat(n)\chi(n)\right|$$
##### Theorem
$$
\begin{align}
\left| \Delta_{\Lambda^\flat}(y; q,a)\right| \le \frac{1}{\varphi(q)} \left|\sum_{d \mid q; 1 < d \le (\log x)^C}  \sum_{s \mid d} \mu(d/s)\varphi(s)\Delta_{\Lambda^\flat_{q}}(y; s, a) \right| + \\ \frac{1}{\varphi(q)} \sum_{d \mid q; (\log x)^C < d; \xi \pmod d}^*S_{q/d}(y, \xi) 

\end{align}$$

##### Theorem (Taking care of small conductors)

$$\frac{1}{\varphi(q)} \left|\sum_{d \mid q; 1 < d \le (\log x)^C}  \sum_{s \mid d} \mu(d/s)\varphi(s)\Delta_{\Lambda^\flat_{q}}(y; s, a) \right| \ll_{A, C} \frac{x}{\varphi(q) (\log x)^{A+1}}$$

###### Proof
Push the absolute values inside, then
$$
\begin{align}
\sum_{d \mid q; d \le (\log x)^C} \sum_{s \mid d} \varphi(s) \left|\Delta_{\Lambda^\flat_{q}}(y; s, a) \right| &\ll_{A, C} \sum_{d \le (\log x)^C} (\sum_{d \mid s} \varphi(s)) \frac{x}{(\log x)^{A+2C+1}} \\
 &\ll \frac{x}{(\log x)^{A+2C+1}} \sum_{d \le (\log x)^C} d \\
 & \ll \frac{x}{(\log x)^{A+1}}
\end{align}
$$

##### Definition
$$T_r(x, Q) := \sum_{(\log x)^C < d \le Q/r} \frac{1}{\varphi(d)} \sum_{\xi \pmod d}^* \max_{\sqrt{x} \le y \le x} S_r(y, \xi)$$

##### Lemma.
For $d, r \in \N$,
$$\varphi(dr) \ge \varphi(d)\varphi(r).$$

##### Theorem 
$$\sum_{q \le Q} \max_{\substack{\sqrt{x} \le y \le x \\ a \in (\mathbb{Z}/q\mathbb{Z})^\times}} \left| \Delta_{\Lambda^{\flat}}(x; q, a) \right| \le \sum_{r \le Q} \frac{T_r(x, Q)}{\varphi(r)} + O(x/(\log x)^A),$$
###### Proof
Sum the error term of the previous lemma, using 
$$\sum_{n \le x} \frac{1}{\varphi(n)} \ll \log x.$$
Then regroup the main sum by $r$.




#### A large sieve inequality


##### Theorem (Large Sieve Inequality)

Let $Q \ge 1$, $H \in \Z$, $N \in \Z_{\ge 1}$ and $c = (c_{H+1}, \dots, c_{H+N}) \in \C^N$ We then have
$$\sum_{q \le Q} \sumstar_{\chi \pmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H+N} c_n \chi(n) \right|^2 \ll (N+Q^2) \| \vec{c} \|_2^2,$$
###### Proof
This is taken as an axiom for the time being.



(note: should there be a SupportedOn predicate for arithmetic functions?)
##### Theorem 26.6 
Let $f$ and $g$ be two arithmetic functions supported on $[1, M]$ and $[1, N]$ respectively. 

For $x, Q \ge 1$ we have 

$$
\begin{align}
\sum_{q \le Q,} \sumstar_{\chi \pmod q} &\frac{q}{\varphi(q)} \max_{y \le x}\left| \sum_{n \le y} (f * g)(n)\chi(n) \right|  \\
&\ll (\sqrt{MN} + \sqrt M Q + \sqrt N Q + Q^2)(\log x)\left|| f \right||_2 \left|| g \right||_2

\end{align}
$$ 
###### Proof
TBD.  Uses Cauchy Schwarz and large sieve inequality

The proof in the book uses the classical version of Perron's integral formula as $1_{n \le x} = \int_{-T}^{T}\frac{(x/n)^{\alpha+it}}{\alpha+it} dt/(2\pi) + O(...)$
But we have a different version in PNT+ [here](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/web/sect0003.html#formulaGtOne). I haven't worked out how this changes the proof yet.


##### Lemma (Dyadic decomposition of $\Lambda^\flat$)
$$\Lambda^\flat(n) = \sum_{U < 2^j \le 2x/V} (f_j \ast g_j)(n) \quad \text{for } n \le x,$$
where $f_j(k) = (\Lambda_{>U} \ast 1)(k) 1_{2^{j-1} < k \le 2^j}$ and $g_j(\ell) = \mu(\ell) 1_{V < \ell \le x/2^{j-1}}.$$


##### Corollary
For $x, Q \ge 2, U, V \in [1, x]$ and $r \in \N$, we have
$$\sum_{q \le Q} \sumstar_{\chi \pmod q} \frac{q}{\varphi(q)} S_r(y, \chi) \ll \left(x + \frac{Qx}{\sqrt{U}} + \frac{Qx}{\sqrt{V}} + Q^2 \sqrt{x}\right) (\log x)^3.$$
###### Proof
Apply the dyadic decomposition of $\Lambda^\flat$ after multiplying by the indicator function of integers coprime to $r$, then use the previous theorem on each summand.
See p. 285

Note: this confused me for a second, when summing over $j$ at the end note that $U \le 2^j$ so that $\sum_{U \le 2^j \le 2x/N} 2^{-j/2} \ll 1/\sqrt{U}$ 


##### Theorem
$$T_r(x, Q) \ll \frac{x}{(\log x)^{C-3}} + \frac{x(\log x)^4}{\sqrt{U}} + \frac{x(\log x)^4}{\sqrt{V}} + \frac{Q\sqrt{x}(\log x)^3}{r},$$
###### Proof.
Use the previous corollary by dividing the sum of $T_r$ into dyadic intervals.
See p. 285


Plugging the above bound into the bound on $\Delta_{\Lambda^\flat}$ and fixing $U = V = e^{\sqrt{\log x}}$ and $C = A+ 4$ finishes the proof.








