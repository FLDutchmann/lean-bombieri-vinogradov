import Mathlib
import Architect
import BV.Delta
import BV.ForMathlib.Indicator

set_option autoImplicit false

open ArithmeticFunction BV ProofData

variable [ProofData]

theorem LambdaLEU_le_log {n : ℕ} : Λ≤U n ≤ Real.log n := by
  by_cases hn : n ≤ U
  · simp [hn, vonMangoldt_le_log]
  · have hn : U < n := by grind
    simp [hn]
    positivity

omit [ProofData] in
@[gcongr]
theorem summatory_mono_fun (f g : ℕ → ℝ) (x : ℝ) (hfg : ∀ n : ℕ, n ≤ x → f n ≤ g n) :
    summatory f x ≤ summatory g x := by
  rw [summatory, summatory]
  gcongr with n hn
  simp only [Nat.mem_Icc, Nat.cast_nonneg, true_and] at hn
  exact hfg n hn

omit [ProofData] in
@[gcongr]
theorem summatory_mono {f : ℕ → ℝ} {x y : ℝ} (hxy : x ≤ y) (hf : ∀ n : ℕ, n ≤ y → 0 ≤ f n) :
    summatory f x ≤ summatory f y := by
  rw [summatory, summatory]
  gcongr with n
  · simp only [Nat.mem_Icc, Nat.cast_nonneg, true_and, not_le]
    intro n hny _
    exact hf n hny
  · intro n
    simp only [Nat.mem_Icc, Nat.cast_nonneg, true_and]
    gcongr

@[blueprint (latexEnv := "lemma") (statement := /--
$$\sum_{n \le y} \Lambda(n) \ll U \log{x}$$
-/)]
theorem sum_vonMangoldt_le {y : ℝ} (hy : y ≤ x) : summatory Λ≤U y ≤ U * Real.log x := by
  trans summatory Λ≤U U
  ·
    sorry
  trans ‖summatory Λ≤U U‖
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
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
  · positivity

@[blueprint (latexEnv := "lemma") (statement := /--
For $y, U > 0$, $q \in \N$ and $a \in \Z/q\Z$,
$$|\Delta_{\Lambda_{\le U}}(y;\, q,\, a)| \ll U \log{x} $$
-/) (uses := [sum_vonMangoldt_le])]
theorem Delta_LambdaLEU_bound [ProofData] {y : ℝ} (hy : y ≤ x) {q : ℕ} (hq : 0 < q) {a : ZMod q} :
    |Δ_[Λ≤U](y; q, a)| ≤ 2 * U * Real.log x := by
  rw [Delta]
  grw [abs_sub, abs_mul]
  have : (q.totient : ℝ)⁻¹ ≤ 1 := by
    have : 0 < q.totient := by simp only [Nat.totient_pos, hq];
    field_simp
    norm_cast
  grw [this, abs_one]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have : summatory ((Nat.modEqs a).indicator ⇑Λ≤U) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) (sum_vonMangoldt_le hy)
      intro n hn
      apply Set.indicator_le' (fun _ _ ↦ le_rfl)
      simp
    have : summatory (onCoprime q ⇑Λ≤U) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) (sum_vonMangoldt_le hy)
      sorry
    linarith
  · positivity
  · positivity

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} |\Delta_{\Lambda_{\le U}}(y;\,q,\,a)| \le Q\sqrt{x} \ll_A \frac{x}{(\log x)^{A+2}}$$
-/) (uses := [Delta_LambdaLEU_bound])]
theorem BV_LambdaLE [ProofData] {A : ℕ} (Q : ℝ) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ≤U](y; q, a)) ≤
      2 * x / (Real.log x)^(A+2) := by
  sorry
