import Mathlib
import Architect
import BV.Defs

open ArithmeticFunction

@[blueprint (latexEnv := "lemma") (statement := /--
$$\sum_{n \le U} \Lambda(n) \ll U$$
-/)]
theorem sum_vonMangoldt_le : 1 = 1 := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
For $y, U > 0$, $q \in \N$ and $a \in \Z/q\Z$,
$$|\Delta_{\Lambda_{\le U}}(y;\, q,\, a)| \ll U$$
-/) (uses := [sum_vonMangoldt_le])]
theorem Delta_LambdaLE_bound : 1 = 1 := by sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda_{\le U}}(y;\,q,\,a)| \le Q\sqrt{x} \ll_A \frac{x}{(\log x)^{A+2}}$$
-/) (uses := [Delta_LambdaLE_bound])]
theorem BV_LambdaLE : 1 = 1 := by sorry