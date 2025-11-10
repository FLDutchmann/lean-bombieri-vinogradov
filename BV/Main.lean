import BlueprintGen
import Mathlib

namespace BombieriVinogradov


open ArithmeticFunction



noncomputable section

/-! ## Bombieri-Vinogradov Theorem

This module contains the formalization of the Bombieri-Vinogradov theorem,
a fundamental result in analytic number theory.
-/

/-- The logarithmic integral function: li(x) = ∫₂ˣ dt/(log t) -/
noncomputable def logIntegral (x : ℝ) : ℝ := sorry

/-- Prime-counting function in arithmetic progression:
π(x; q, a) counts primes p ≤ x with p ≡ a (mod q)
-/
noncomputable def primeCountingAP (x : ℝ) (q : ℕ) (a : ℕ) : ℝ := sorry


/-!
### Preliminaries

Decomposing the von Mangoldt function into type I and type II functions. -/

/--
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$
-/

@[blueprint]
def Delta (f : ℕ → ℝ) (x : ℝ) (q a : ℕ) : ℝ :=
  sorry

notation3 "Δ_[" f "](" x "; " q ", " a ")" => Delta f x q a

/--
$$\Delta_f(y ;q, a) = \frac{1}{\varphi(q)} \sum_{\chi \pmod{q}, \chi \ne \chi_0} \bar\chi(a) \sum_{n \le y} f(n) \chi(n) $$

-/
@[blueprint (notReady := true)]
lemma Delta_eq_sum_char : 1 = 1 := by
  sorry

/--

Notice:
$$\Delta_{1_P}(x; q, a) = \pi(x; q,a) - \frac{1}{\varphi(q)} \sum_{p \le x, p \not\mid q} 1 $$

-/

@[blueprint]
theorem Delta_primeIndicator_eq : 1 = 1 := by
  sorry

/--
$$ \sum_{p \le x, p \not \mid q} 1 = li(x) + O(xe^{-c\sqrt{\log x}}+\log q)$$

-/

@[blueprint]
lemma sum_primes_not_dvd_eq_li : 1 = 1 := by
  sorry

def C : ℝ := sorry


/--
For $x \ge 2$, $q \in \N$ and $a \in (\Z / q\Z)^*$ we have
$$ \max_{y \le x} \left| \Delta_{1_P}(y; q, a) \right| \ll \frac{1}{\log x} \left(\max_{\sqrt x \le y \le x} \left|\Delta_\Lambda(y; q, a)\right| + \sqrt x \right)$$
proof. See p. 279. Uses combinatorics, an estimate on $\sum_{p \le x} 1/\log p$ and partial summation.
-/
@[blueprint]
theorem max_Delta_1P_le_max_Delta_Lambda : 1 = 1 := by
  /-- See p. 279. Uses combinatorics, an estimate on $\sum_{p \le x} 1/\log p$ and partial summation. -/
  sorry

/-! Wrapping up -/

/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/
theorem BV_Delta_Lambda : 1 = 1 := by
  sorry

/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{1_P}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A+1}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/

theorem BV_Delta_1P : 1 = 1 := by
  sorry


-- Here $UV \le \sqrt x$ and $U, V \ge e^{\sqrt{\log x}}$, not sure how to best encode that.
/-- $\Lambda^\sharp = \mu_{\le V} * \log - (\Lambda_{\le U} * \mu_{\le V}) * 1$ -/
@[blueprint]
def LambdaSharp (U V : ℝ) (n : ℕ) : ℝ := sorry

notation3 "Λ♯[" U ", " V "]" => LambdaSharp U V

/-- $\Lambda^\flat = (\Lambda_{>U} * 1) * \mu_{>V}$-/
@[blueprint]
def LambdaFlat (U V : ℝ) (n : ℕ) : ℝ := sorry

notation3 "Λ♭[" U ", " V "]" => LambdaSharp U V

/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
@[blueprint]
def LambdaLE (U : ℝ) (n : ℕ) : ℝ := sorry

notation3 "Λ≤[" U "]" => LambdaLE U

/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
@[blueprint]
theorem Lambda_decomp {U V : ℝ} (n : ℕ) : Λ n = Λ♯[U, V] n + Λ♭[U, V] n + Λ≤[U] n := by
  sorry

/-
##### Lemma
$$\Delta_{\Lambda_{\le U}} (y; q, a) \ll U \le \sqrt{x}$$
$$\sum_{n\le U} \Lambda (n) \ll U$$

-/


/--
Maximum deviation of primes in residue class a (mod q) from expected distribution.
This represents: max_{y≤x} |π(y; q, a) - li(y)/φ(q)|
-/
noncomputable def maxDeviation (x : ℝ) (q : ℕ) (a : ℕ) : ℝ := sorry

/--
Sum of maximum deviations over all residue classes and moduli up to Q.
This represents: ∑_{q≤Q} max_{y≤x} max_{a ∈ (ℤ/qℤ)*} |π(y; q, a) - li(y)/φ(q)|
-/
noncomputable def sumMaxDeviations (x Q : ℝ) : ℝ := sorry


/-- Implied constant for Bombieri-Vinogradov theorem -/
noncomputable def C_BV (A : ℕ) : ℝ := sorry

/--
For each fixed $A \geq 0$,
$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \pi(y; q, a) - \frac{\text{li}(y)}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A+1}}$$

uniformly for all $x \ge 2$ and $1 \le Q \le \frac{\sqrt{x}}{(\log x)^{A+3}}$. -/
@[blueprint "Bombieri-Vinogradov" (uses := [BV_Delta_1P, sum_primes_not_dvd_eq_li])]
theorem BombieriVinogradov (A : ℕ) {x : ℝ} (hx : 2 ≤ x) {Q : ℝ} (hle_Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    sumMaxDeviations x Q ≤ C_BV A * x / (Real.log x)^(A+1) := by
  /-- Apply BV_Delta and absorb the error terms -/
  sorry

end

end BombieriVinogradov
