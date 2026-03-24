import Mathlib
import Architect
import BV.Defs

open ArithmeticFunction

@[blueprint (latexEnv := "lemma") (statement := /--
If $f$ is an arithmetic function supported on $[1, y]$ then
$$\Delta_{f*g}(x;\,q,\,a) = \sum_{\substack{k \le y \\ (k,q)=1}} f(k)\, \Delta_g\!\left(\frac{x}{k};\, q,\, a\bar{k}\right)$$
-/)]
theorem Delta_convolution_eq : (sorry : Prop) := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
For $x \ge 1$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_1(x;\, q,\, a)| \le 1$$
-/) (proof := /--
Carefully consider length $q$ intervals. Alternatively, write
$$\Delta_1(t;\, q,\, a) = \frac{1}{\varphi(q)} \sum_{a' \in (\Z/q\Z)^*} \left( \sum_{\substack{n \le t \\ n \equiv a \pmod{q}}} 1 - \sum_{\substack{n \le t \\ n \equiv a' \pmod{q}}} 1 \right)$$
and note each inner difference is bounded by $1$ in absolute value.
-/)]
theorem Delta_one_bound : (sorry : Prop) := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable on $[1, x]$ then
$$\Delta_g(x;\,q,\,a) = \Delta_1(x;\,q,\,a)\,g(x) - \int_1^x \Delta_1(t;\,q,\,a)\,g'(t)\,\mathrm{d}t$$
-/) (proof := /--
By Abel summation.
-/) (uses := [Delta_one_bound])]
theorem Delta_abel_summation : (sorry : Prop) := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable and monotone on $[1, y]$ with $g(0) = 0$, then for all $t \ge 1$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_g(x;\, q,\, a)| \le 2g(t)$$
-/) (uses := [Delta_one_bound, Delta_abel_summation])]
theorem Delta_monotone_bound : (sorry : Prop) := by sorry

@[blueprint (statement := /--
Let $v \ge 0$ and let $f$ be an arithmetic function supported on $[1, y]$. For $x \ge 2$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_{f * \log^v}(x;\, q,\, a)| \le 2(\log x)^v \sum_{k \le y} |f(k)|$$
-/) (proof := /--
Straightforward application of the previous lemmas.
-/) (uses := [Delta_one_bound, Delta_abel_summation, Delta_monotone_bound])]
theorem Delta_flog_bound : (sorry : Prop) := by sorry

@[blueprint (statement := /--
For $U, V \ge 1$, $x \ge 2$, $q \in \N$, $r \le x$ and $a \in (\Z/q\Z)^*$,
$$\max_{y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp_r}(y;\, q,\, a)| \ll UV \log x$$
-/) (proof := /--
Apply \ref{Delta_flog_bound} twice: once with $f = \mu_{\le V,\, r}$, $v = 0$,
and once with $f = \Lambda_{\le U} * \mu_{\le V,\, r}$, $v = 0$, $y = UV$.
-/) (uses := [Delta_flog_bound, Delta_convolution_eq])]
theorem Delta_LambdaSharp_bound : (sorry : Prop) := by sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda^\sharp}(y;\, q,\, a)| \ll_A \frac{x}{(\log x)^A}$$
-/) (uses := [Delta_LambdaSharp_bound])]
theorem BV_LambdaSharp : (sorry : Prop) := by sorry
