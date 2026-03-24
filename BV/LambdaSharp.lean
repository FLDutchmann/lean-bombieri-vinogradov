import Mathlib
import Architect
import BV.Delta

open ArithmeticFunction

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
