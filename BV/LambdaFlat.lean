import Mathlib
import Architect
import BV.Defs
import BV.Axioms

open ArithmeticFunction

/-! ## Type II sums: the flat part $\Lambda^\flat$ -/

/-- $S_r(y, \xi) := \left|\sum_{n \le y} \Lambda_r^\flat(n)\,\xi(n)\right|$ -/
@[blueprint (latexEnv := "definition") (statement := /--
$$S_r(y, \xi) := \left|\sum_{n \le y} \Lambda_r^\flat(n)\,\xi(n)\right|$$
-/)]
noncomputable def S_r : ℝ := sorry

/-- $T_r(x, Q) := \sum_{(\log x)^C < d \le Q/r} \frac{1}{\varphi(d)} \sum_{\xi \pmod{d}}^* \max_{\sqrt{x} \le y \le x} S_r(y, \xi)$ -/
@[blueprint (latexEnv := "definition") (statement := /--
$$T_r(x, Q) := \sum_{(\log x)^C < d \le Q/r} \frac{1}{\varphi(d)} \sumstar_{\xi \pmod{d}} \max_{\sqrt{x} \le y \le x} S_r(y, \xi)$$
-/) (uses := [S_r])]
noncomputable def T_r : ℝ := sorry

/-! ### Reduction to character sums -/

@[blueprint (latexEnv := "lemma") (statement := /--
This is a standard result. Let $f$ be a function from Dirichlet characters. Then
$$\sum_{\substack{\chi \pmod{q} \\ \chi \ne \chi_0}} f(\chi) = \sum_{d \mid q} \sumstar_{\xi \pmod{d}} f(1_{(n,q)=1}\xi)$$
-/)]
theorem character_sum_by_conductor : 1 = 1 := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
Let $f$ be an arithmetic function. For $r \le x$, $q > 1$ and $(a, q) = 1$,
$$\sumstar_{\xi \pmod{q}} \bar\xi(a) \sum_{n \le y} \xi(n) f_r(n) = \sum_{d \mid q} \mu(q/d)\,\varphi(d)\,\Delta_{f_{rq}}(y;\, d,\, a)$$
-/) (proof := /--
Fix $P \in \N$ with $q \mid P$. Define $F_P$ and $G_P$ on divisors of $P$ by
\begin{align*}
F_P(q) &:= \sum_{\chi \ne \chi_0 \pmod{q}} \bar\chi(a) \sum_{n \le y} \chi(n) f_{rP}(n) = \Delta_{f_{rP}}(y;\, q,\, a), \\
G_P(d) &:= \sumstar_{\xi \pmod{d}} \bar\xi(a) \sum_{n \le y} \xi(n) f_{rP}(n) \quad (d > 1),\quad G_P(1) = 0.
\end{align*}
Since every non-principal character mod $q$ factors through a unique primitive character, $F_P(q) = \sum_{d \mid q} G_P(d)$.
By Möbius inversion,
$$G_P(q) = \sum_{d \mid q} \mu(q/d)\, F_P(d) = \sum_{d \mid q} \mu(q/d)\, \Delta_{f_{rP}}(y;\, d,\, a).$$
Set $P = q$ to conclude.
-/) (uses := [character_sum_by_conductor])]
theorem character_sum_Mobius : 1 = 1 := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
$$\left|\Delta_{\Lambda^\flat}(y;\, q,\, a)\right| \le \frac{1}{\varphi(q)} \left|\sum_{\substack{d \mid q \\ 1 < d \le (\log x)^C}} \sum_{s \mid d} \mu(d/s)\,\varphi(s)\,\Delta_{\Lambda^\flat_q}(y;\,s,\,a)\right| + \frac{1}{\varphi(q)} \sum_{\substack{d \mid q \\ d > (\log x)^C}} \sumstar_{\xi \pmod{d}} S_{q/d}(y, \xi)$$
-/) (uses := [character_sum_by_conductor, character_sum_Mobius, S_r])]
theorem Delta_LambdaFlat_decomp : 1 = 1 := by sorry

@[blueprint (statement := /--
$$\frac{1}{\varphi(q)} \left|\sum_{\substack{d \mid q \\ 1 < d \le (\log x)^C}} \sum_{s \mid d} \mu(d/s)\,\varphi(s)\,\Delta_{\Lambda^\flat_q}(y;\,s,\,a)\right| \ll_{A,C} \frac{x}{\varphi(q)\,(\log x)^{A+1}}$$
-/) (proof := /--
Push the absolute values inside, then
\begin{align*}
\sum_{d \mid q,\, d \le (\log x)^C} \sum_{s \mid d} \varphi(s)\, \left|\Delta_{\Lambda^\flat_q}(y;\, s,\, a)\right|
&\ll_{A,C} \sum_{d \le (\log x)^C} \left(\sum_{s \mid d} \varphi(s)\right) \frac{x}{(\log x)^{A+2C+1}} \\
&\ll \frac{x}{(\log x)^{A+2C+1}} \sum_{d \le (\log x)^C} d \\
&\ll \frac{x}{(\log x)^{A+1}}.
\end{align*}
-/) (uses := [Delta_LambdaFlat_decomp, siegel_walfisz])]
theorem Delta_LambdaFlat_small_conductor : 1 = 1 := by sorry

@[blueprint (statement := /--
$$\sum_{q \le Q} \max_{\substack{\sqrt{x} \le y \le x \\ a \in (\Z/q\Z)^*}} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \le \sum_{r \le Q} \frac{T_r(x,Q)}{\varphi(r)} + O\!\left(\frac{x}{(\log x)^A}\right)$$
-/) (proof := /--
Sum the error from \ref{Delta_LambdaFlat_small_conductor} over $q \le Q$ using
$\sum_{n \le x} 1/\varphi(n) \ll \log x$, then regroup the main sum by $r = q/d$.
-/) (uses := [Delta_LambdaFlat_decomp, Delta_LambdaFlat_small_conductor, character_sum_Mobius, T_r])]
theorem BV_LambdaFlat_via_T : 1 = 1 := by sorry

/-! ### Large sieve estimates -/

@[blueprint (statement := /--
Let $f$ and $g$ be arithmetic functions supported on $[1, M]$ and $[1, N]$ respectively. For $x, Q \ge 1$,
$$\sum_{q \le Q} \sumstar_{\chi \pmod{q}} \frac{q}{\varphi(q)} \max_{y \le x}\left|\sum_{n \le y} (f*g)(n)\chi(n)\right| \ll \left(\sqrt{MN} + \sqrt{M}\,Q + \sqrt{N}\,Q + Q^2\right)(\log x)\,\|f\|_2\,\|g\|_2$$
-/) (proof := /--
Uses Cauchy--Schwarz and the large sieve inequality (\ref{large_sieve}).
The proof in the book uses the classical version of Perron's integral formula as $1_{n \le x} = \int_{-T}^{T}\frac{(x/n)^{\alpha+it}}{\alpha+it} dt/(2\pi) + O(...)$
But we have a different version in PNT+. I haven't worked out how this changes the proof yet.
-/) (uses := [large_sieve])]
theorem LargeSieve_convolution : 1 = 1 := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
$$\Lambda^\flat(n) = \sum_{U < 2^j \le 2x/V} (f_j * g_j)(n) \quad \text{for } n \le x,$$
where $f_j(k) = (\Lambda_{>U} * 1)(k)\,1_{2^{j-1} < k \le 2^j}$ and $g_j(\ell) = \mu(\ell)\,1_{V < \ell \le x/2^{j-1}}$.
-/)]
theorem LambdaFlat_dyadic : 1 = 1 := by sorry

@[blueprint (statement := /--
For $x, Q \ge 2$, $U, V \in [1, x]$ and $r \in \N$,
$$\sum_{q \le Q} \sumstar_{\chi \pmod{q}} \frac{q}{\varphi(q)}\, S_r(y, \chi) \ll \left(x + \frac{Qx}{\sqrt{U}} + \frac{Qx}{\sqrt{V}} + Q^2\sqrt{x}\right)(\log x)^3$$
-/) (proof := /--
Apply the dyadic decomposition \ref{LambdaFlat_dyadic} (restricted to integers coprime to $r$)
and apply \ref{LargeSieve_convolution} to each dyadic piece.
When summing over $j$ note $U \le 2^j$, so $\sum_{U \le 2^j} 2^{-j/2} \ll 1/\sqrt{U}$.
-/) (uses := [LargeSieve_convolution, LambdaFlat_dyadic, S_r])]
theorem BV_char_sum_bound : 1 = 1 := by sorry

@[blueprint (statement := /--
$$T_r(x,Q) \ll \frac{x}{(\log x)^{C-3}} + \frac{x(\log x)^4}{\sqrt{U}} + \frac{x(\log x)^4}{\sqrt{V}} + \frac{Q\sqrt{x}\,(\log x)^3}{r}$$
-/) (proof := /--
Divide the sum defining $T_r$ into dyadic intervals in $d$ and apply \ref{BV_char_sum_bound}.
-/) (uses := [BV_char_sum_bound, LambdaFlat_dyadic, T_r])]
theorem T_r_bound : 1 = 1 := by sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \ll_A \frac{x}{(\log x)^A}$$
-/) (proof := /--
Plug the bound from \ref{T_r_bound} into \ref{BV_LambdaFlat_via_T},
then choose $U = V = e^{\sqrt{\log x}}$ and $C = A + 4$.
-/) (uses := [BV_LambdaFlat_via_T, T_r_bound, Delta_LambdaFlat_small_conductor])]
theorem BV_LambdaFlat : 1 = 1 := by sorry
