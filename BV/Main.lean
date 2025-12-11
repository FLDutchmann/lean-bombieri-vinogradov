import Mathlib
import Architect

import BV.Defs

namespace BombieriVinogradov


open ArithmeticFunction



noncomputable section

/-! ## Bombieri-Vinogradov Theorem

This module contains the formalization of the Bombieri-Vinogradov theorem,
a fundamental result in analytic number theory.
-/


/-! Wrapping up -/

@[blueprint (statement :=
/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{\sqrt x \le y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{\Lambda}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/
)]
theorem BV_Delta_Lambda : 1 = 1 := by
  sorry


/-- Implied constant for Bombieri-Vinogradov theorem -/
noncomputable def C_BV (A : ℕ) : ℝ := sorry

open Nat

@[blueprint "Bombieri-Vinogradov" (statement :=
/--
For each fixed $A \geq 0$,
$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \psi(y; q, a) - \frac{y}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A}}$$

uniformly for all $x \ge 2$ and $1 \le Q \le \frac{\sqrt{x}}{(\log x)^{A+3}}$. -/
)]
theorem bombieri_vinogradov (A : ℕ) {x : ℝ} (hx : 2 ≤ x) {Q : ℝ} (hle_Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    (∑ q ∈ Nat.Icc 1 Q,
        have : NeZero q := sorry
      (Nat.Icc 0 x).sup' (Nat.Icc_zero_nonempty sorry) fun y ↦
        Finset.univ.sup' Finset.univ_nonempty fun (a : ZMod q) ↦ (|ψ y a - x / φ q|))
      ≤ C_BV A * x / (Real.log x)^A := by
  /-- Apply theorem~\ref{BombieriVinogradov.BV_Delta_Lambda} and absorb the error terms -/
  sorry

end



@[blueprint (statement :=
/--
$$\Delta_{1_P}(x; q, a) = \pi(x; q,a) - \frac{1}{\varphi(q)} \sum_{p \le x, p \not\mid q} 1 $$
-/
)]
theorem Delta_primeIndicator_eq : 1 = 1 := by
  sorry


@[blueprint (statement :=
/--
$$ \sum_{p \le x, p \not \mid q} 1 = li(x) + O(xe^{-c\sqrt{\log x}}+\log q)$$
-/
)]
lemma sum_primes_not_dvd_eq_li : 1 = 1 := by
  sorry

def C : ℝ := sorry


@[blueprint (statement :=
/--
For $x \ge 2$, $q \in \N$ and $a \in (\Z / q\Z)^*$ we have
$$ \max_{y \le x} \left| \Delta_{1_P}(y; q, a) \right| \ll \frac{1}{\log x} \left(\max_{\sqrt x \le y \le x} \left|\Delta_\Lambda(y; q, a)\right| + \sqrt x \right)$$
-/
)]
theorem max_Delta_1P_le_max_Delta_Lambda : 1 = 1 := by
  /-- See p. 279. Uses combinatorics, an estimate on $\sum_{p \le x} 1/\log p$ and partial summation. -/
  sorry

@[blueprint (statement :=
/--
For each fixed $A \ge 0$ we have
$$\sum_{q\le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \Delta_{1_P}(y; q,a) \right| \ll_A \frac{x}{(\log x)^{A+1}}$$
uniformly for $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log (x))^{A+3}$
-/
)]
theorem BV_Delta_1P : 1 = 1 := by
  sorry

end BombieriVinogradov
