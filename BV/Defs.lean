import Mathlib
import Architect


open ArithmeticFunction
open scoped Moebius zeta


-- /-- The logarithmic integral function: li(x) = ∫₂ˣ dt/(log t) -/
-- @[blueprint (latexEnv := "definition") (statement := /-- $\li(x) = \int_2^x \frac{\mathrm{d}t}{\log t}$ -/)]
-- noncomputable def logIntegral (x : ℝ) : ℝ := sorry

-- /-- Prime-counting function in arithmetic progression:
-- π(x; q, a) counts primes p ≤ x with p ≡ a (mod q)
-- -/
-- noncomputable def primeCountingAP (x : ℝ) (q : ℕ) (a : ℕ) : ℝ := sorry


noncomputable def Nat.Icc (x y : ℝ) : Finset ℕ :=
  if x ≤ y ∧ 0 ≤ y then Finset.Icc (⌈x⌉₊) (⌊y⌋₊) else ∅

@[simp]
theorem Nat.mem_Icc (x : ℝ) {y : ℝ} (n : ℕ) :
    n ∈ Nat.Icc x y ↔ x ≤ n ∧ n ≤ y := by
  by_cases h : y < x
  · grind [Nat.Icc]
  by_cases hy : 0 ≤ y
  · rw [Nat.Icc, if_pos (by grind)]
    simp [Nat.le_floor_iff hy]
  · grind [Nat.Icc]

theorem Nat.mem_Icc_zero {x : ℝ} (n : ℕ) :
    n ∈ Nat.Icc 0 x ↔ n ≤ x := by simp


theorem Nat.Icc_zero_nonempty {x : ℝ} (hx : 0 ≤ x) : (Nat.Icc 0 x).Nonempty := by
  use 0
  simp [hx]

@[simp]
theorem card_natIcc (x : ℝ) {y : ℝ} (hy : 0 ≤ y):
    (Nat.Icc x y).card = ⌊y⌋₊ + 1 - ⌈x⌉₊ := by
  by_cases hxy : x ≤ y
  · simp [Nat.Icc, hxy, hy]
  · simp [Nat.Icc, hxy]
    rw [eq_comm, Nat.sub_eq_zero_iff_le]
    simp only [Order.add_one_le_iff]
    push_neg at hxy
    grw [Nat.floor_lt hy]
    calc _ < x := hxy
    _ ≤ _ := Nat.le_ceil x

@[simp]
theorem card_natIcc_zero (x : ℝ) (hx : 0 ≤ x) :
    (Nat.Icc 0 x).card = ⌊x⌋₊ + 1 := by
  simp [card_natIcc _ hx]

noncomputable def summatory {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) : R :=
  ∑ i ∈ Nat.Icc 0 x, f i

theorem summatory_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R] (f : ℕ → R) (x : ℝ) (hf : ∀ n : ℕ, n ≤ x → 0 ≤ f n ) : 0 ≤ summatory f x := by
  simp [summatory]
  apply Finset.sum_nonneg
  simp only [Nat.mem_Icc, Nat.cast_nonneg, true_and]
  grind


theorem summatory_le_UB {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x : ℝ) (hx : 0 ≤ x) (M : ℝ) (hf : ∀ n : ℕ, n ≤ x → ‖f n‖ ≤ M) :
  ‖summatory f x‖ ≤ (x+1) * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hx)]
    simp
  grw [summatory, norm_sum_le]
  trans ∑ i ∈ Nat.Icc 0 x, M
  · gcongr with n hn
    apply hf
    simpa using hn
  · simp [hx]
    gcongr
    exact Nat.floor_le hx

theorem summatory_le_UB_of_zero {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x : ℝ) (hx : 0 ≤ x) (M : ℝ) (hf : ∀ n : ℕ, n ≤ x → ‖f n‖ ≤ M) (hf0 : f 0 = 0) :
  ‖summatory f x‖ ≤ x * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hx)]
    simp
  grw [summatory, norm_sum_le]
  calc _ = ∑ n ∈ (Nat.Icc 0 x).erase 0, ‖f n‖ := ?_
    _ ≤ ∑ n ∈ (Nat.Icc 0 x).erase 0, M := ?_
    _ ≤ x * M := ?_
  · simp [hf0, Finset.sum_erase]
  · gcongr with n hn
    apply hf
    simp only [Finset.mem_erase, ne_eq, Nat.mem_Icc, Nat.cast_nonneg, true_and] at hn
    exact hn.2
  · simp [hx]
    gcongr
    exact Nat.floor_le hx

def Nat.modEqs {q : ℕ} (a : ZMod q) : Set ℕ := {n : ℕ | n = a}

noncomputable def ψ (x : ℝ) {q : ℕ} (a : ZMod q) : ℝ :=
    summatory ((Nat.modEqs a).indicator Λ) x

@[blueprint (statement :=
/-- For $f : \N \rightarrow \R$ and $r : \N$ we use $f_r$ to denote $n \mapsto f(n) 1_{(n, r) = 1}$-/
)]
def onCoprime {R : Type*} [Zero R] (r : ℕ) (f : ℕ → R) (n : ℕ) : R :=
  if r.Coprime n then f n else 0


/-!
### Preliminaries

Decomposing the von Mangoldt function into type I and type II functions. -/

@[blueprint (statement := /--
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$
-/)]
noncomputable def Delta (f : ℕ → ℝ) (x : ℝ) (q : ℕ) (a : ZMod q) : ℝ :=
  summatory ((Nat.modEqs (a : ZMod q)).indicator f) x -
  (1 / (Nat.totient q : ℝ)) * summatory (onCoprime q f) x

theorem DirichletCharacter.inv_zmod_apply {q : ℕ} {a : ZMod q} (ha : IsUnit a)
    (χ : DirichletCharacter ℂ q) : χ⁻¹ a = χ a⁻¹ := by
  rw [MulChar.inv_apply_eq_inv']
  have hmul : χ a * χ a⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit a ha, map_one]
  exact inv_eq_of_mul_eq_one_right hmul

lemma DirichletCharacter.one_natCast_apply {q : ℕ} [NeZero q] (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if q.Coprime n then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h.symm)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).mp hu).symm)

notation3 "Δ_[" f "](" x "; " q ", " a ")" => Delta f x q a
@[blueprint(statement :=
/--
$$\Delta_f(y ;q, a) = \frac{1}{\varphi(q)} \sum_{\chi \pmod{q}, \chi \ne \chi_0} \bar\chi(a) \sum_{n \le y} f(n) \chi(n) $$
-/)]
lemma Delta_eq_sum_char (f : ℕ → ℝ) (y : ℝ) (q a : ℕ) [NeZero q]
    (ha : IsUnit (a : ZMod q)) :
    open Classical in
    (Delta f y q a : ℂ) = (1 / (Nat.totient q : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then
        star (χ (a : ZMod q)) * summatory (fun n => (f n : ℂ) * χ n) y
      else 0 := by
  have hφ : (Nat.totient q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [Delta, summatory, Nat.modEqs, onCoprime, Set.indicator_apply, Set.mem_setOf_eq]
  push_cast
  -- Suffices to prove the equivalent form with φ cleared
  suffices h : (q.totient : ℂ) * ∑ i ∈ Nat.Icc 0 y, ↑(if (i : ZMod q) = (a : ZMod q) then f i else 0) -
      ∑ i ∈ Nat.Icc 0 y, ↑(if q.Coprime i then f i else 0) =
      ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then
        star (χ (a : ZMod q)) * ∑ x ∈ Nat.Icc 0 y, (f x : ℂ) * χ x else 0 by
    field_simp [hφ]
    linear_combination h
  -- Let F χ = star(χ a') * ∑_n f(n) χ(n)
  set F := fun χ : DirichletCharacter ℂ q =>
    star (χ (a : ZMod q)) * ∑ x ∈ Nat.Icc 0 y, (f x : ℂ) * χ x
  -- Step 1: Split off the χ = 1 term: ∑_{χ≠1} F χ = ∑_χ F χ - F 1
  have hsplit : ∑ χ : DirichletCharacter ℂ q, (if χ ≠ 1 then F χ else 0) = ∑ χ, F χ - F 1 := by
    have hadd := Finset.add_sum_erase Finset.univ F (Finset.mem_univ (1 : DirichletCharacter ℂ q))
    rw [← hadd]
    ring_nf
    rw [← Finset.sum_filter]
    congr
    grind
  rw [hsplit]
  have hFsum : ∑ χ : DirichletCharacter ℂ q, F χ =
      (q.totient : ℂ) * ∑ i ∈ Nat.Icc 0 y, ↑(if (i : ZMod q) = (a : ZMod q) then f i else 0) := by
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy ↦ ?_)
    simp_rw [mul_comm (f y : ℂ), ← mul_assoc, ← Finset.sum_mul, MulChar.star_apply',
      DirichletCharacter.inv_zmod_apply ha, this]
    by_cases h : (y : ZMod q) = a
    · simp [h]
    · simp [h]; grind

  have hF1 : F 1 = ∑ i ∈ Nat.Icc 0 y, ↑(if q.Coprime i then f i else 0) := by
    simp only [F, MulChar.one_apply ha, star_one, one_mul]
    apply Finset.sum_congr rfl; intro n _
    rw [DirichletCharacter.one_natCast_apply]
    split_ifs <;> simp
  rw [hFsum, hF1]

@[blueprint (statement :=
/--
$$\Delta_{\Lambda}(x; q, a) = \psi(x; q,a) - \frac{1}{\varphi(q)} \sum_{p \le x, p \not\mid q} \log{p} $$
-/
)]
theorem Delta_Lambda_eq : 1 = 1 := by
  sorry


@[blueprint (statement :=
/--
$$ \sum_{p \le x, p \not \mid q} \log{p} = x + O(xe^{-c\sqrt{\log x}}+\log q)$$
-/
)]
lemma sum_primes_not_dvd_log_eq_id : 1 = 1 := by
  sorry


class ProofData where
  U : ℝ
  V : ℝ
  x : ℝ
  le_x : 2 ≤ x
  UV_le : U * V ≤ Real.sqrt x
  le_U : Real.exp (Real.sqrt x) ≤ U
  le_V : Real.exp (Real.sqrt x) ≤ V

open ProofData

variable [data : ProofData]

theorem ProofData.U_nonneg : 0 ≤ U := by
  apply le_trans _ le_U
  positivity

theorem ProofData.one_le_U : 1 ≤ U := by
  apply le_trans _ le_U
  simp

theorem ProofData.V_nonneg : 0 ≤ V := by
  apply le_trans _ le_V
  positivity

theorem ProofData.one_le_V : 1 ≤ V := by
  apply le_trans _ le_V
  simp

theorem ProofData.x_nonneg : 0 ≤ x := by
  linarith only [le_x]

theorem ProofData.U_le_x : U ≤ x := by
  calc _ ≤ U * V := le_mul_of_one_le_right U_nonneg one_le_V
    _ ≤ Real.sqrt x := UV_le
    _ ≤ x := by
      refine Real.sqrt_le_iff.mpr ?_
      constructor
      · exact x_nonneg
      · exact le_self_pow₀ (by linarith only [le_x]) (by norm_num)

/-- Restrict an arithmetic function to a set, setting all values outside the set to zero.
Like `Set.indicator` but for `ArithmeticFunction`. -/
noncomputable def ArithmeticFunction.on {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨s.indicator f, by simp⟩


omit [ProofData] in
@[simp]
theorem ArithmeticFunction.on_apply_of_mem {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) (n : ℕ) (hn : n ∈ s) :
    f.on s n = f n := by
  simp [on, hn]

omit [ProofData] in
@[simp]
theorem ArithmeticFunction.on_apply_of_not_mem {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) (n : ℕ) (hn : ¬ n ∈ s) :
    f.on s n = 0 := by
  simp [on, hn]


section Lambda


/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
@[blueprint (statement :=
/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
)]
noncomputable def LambdaLEU [ProofData] : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt.on (Set.Icc 1 (Nat.floor U))

scoped[BV] notation3 "Λ≤U" => LambdaLEU

open BV

@[simp]
theorem LambdaLEU_apply_of_le {n : ℕ} (hn : n ≤ U) :
    Λ≤U n = Λ n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  simp only [LambdaLEU]
  rw [on_apply_of_mem]
  simp [hn, Nat.le_floor]
  grind

@[simp]
theorem LambdaLEU_apply_of_gt {n : ℕ} (hn : U < n) :
    Λ≤U n = 0 := by
  rw [LambdaLEU, on_apply_of_not_mem]
  simp only [Set.mem_Icc, not_and, not_le]
  intro _
  rw [Nat.floor_lt U_nonneg]
  exact hn

/-- $\mu{\le U} = 1_{≤ U} \cdot \mu$ -/
@[blueprint (statement :=
/-- $\mu_{\le U} = 1_{≤ U} \cdot \mu$ -/
)]
noncomputable def moebiusLEV [ProofData] : ArithmeticFunction ℝ :=
  (μ).on (Set.Icc 1 (Nat.floor V))

scoped[BV] notation3 "μ≤V" => moebiusLEV

open ArithmeticFunction in
@[blueprint (statement :=
/-- $\Lambda^\sharp = \mu_{\le V} * \log - (\Lambda_{\le U} * \mu_{\le V}) * 1$ -/
)]
noncomputable def LambdaSharp [ProofData] : ArithmeticFunction ℝ :=
   μ≤V * log - Λ≤U * μ≤V * zeta

scoped[BV] notation3 "Λ♯" => LambdaSharp

@[blueprint (statement :=
/-- $\Lambda^\flat = (\Lambda_{>U} * 1) * \mu_{>V}$-/
)]
noncomputable def LambdaFlat : ArithmeticFunction ℝ :=
  (Λ - Λ≤U) * ζ * (μ - μ≤V)

scoped[BV] notation3 "Λ♭" => LambdaFlat


/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
@[blueprint (statement :=
/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
)]
theorem Lambda_decomp (n : ℕ) : Λ n = Λ♯ n + Λ♭ n + Λ≤U n := by
  simp_rw [← add_apply]
  congr 1
  simp [LambdaFlat, LambdaSharp, LambdaLEU, ← ArithmeticFunction.vonMangoldt_mul_zeta]
  have : (ζ * μ) = (1 : ArithmeticFunction ℝ) := coe_zeta_mul_coe_moebius
  grind

end Lambda
