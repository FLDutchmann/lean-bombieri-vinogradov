import Mathlib
import Architect
import BV.Defs

set_option autoImplicit false

open ArithmeticFunction BV ProofData

variable [ProofData]

theorem LambdaLEU_nonneg {n : ℕ} : 0 ≤ Λ≤U n := by
  by_cases hn : n ≤ U
  · simp [hn]
  · have hn : U < n := by grind
    simp [hn]

theorem LambdaLEU_le_log {n : ℕ} : Λ≤U n ≤ Real.log n := by
  by_cases hn : n ≤ U
  · simp [hn, vonMangoldt_le_log]
  · have hn : U < n := by grind
    simp [hn]
    positivity

@[blueprint (latexEnv := "lemma") (statement := /--
$$\sum_{n \le U} \Lambda(n) \ll U \log{x}$$
-/)]
theorem sum_vonMangoldt_le : summatory Λ≤U U ≤ U * Real.log x := by
  trans ‖summatory Λ≤U U‖
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    --TODO: Replace by positivity extension?
    apply summatory_nonneg
    intros
    apply LambdaLEU_nonneg
  apply summatory_le_UB_of_zero U ProofData.U_nonneg (Real.log x) _ (by simp)
  intro n hnU
  by_cases hn : n = 0
  · simp only [hn, ArithmeticFunction.map_zero, norm_zero]
    have := le_x
    bound
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · apply le_trans LambdaLEU_le_log
    gcongr
    grw [hnU]
    exact U_le_x
  · apply LambdaLEU_nonneg

@[blueprint (latexEnv := "lemma") (statement := /--
For $y, U > 0$, $q \in \N$ and $a \in \Z/q\Z$,
$$|\Delta_{\Lambda_{\le U}}(y;\, q,\, a)| \ll U \log{x} $$
-/) (uses := [sum_vonMangoldt_le])]
theorem Delta_LambdaLEU_bound [ProofData] {y : ℝ} {q : ℕ} {a : ZMod q} :
    |Δ_[Λ≤U](y; q, a)| ≤ 2 * U * Real.log x := by
  rw [Delta]
  sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda_{\le U}}(y;\,q,\,a)| \le Q\sqrt{x} \ll_A \frac{x}{(\log x)^{A+2}}$$
-/) (uses := [Delta_LambdaLEU_bound])]
theorem BV_LambdaLE [ProofData] {A : ℕ} (Q : ℝ) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ≤U](y; q, a)) ≤
      2 * x / (Real.log x)^(A+2) := by
  sorry
