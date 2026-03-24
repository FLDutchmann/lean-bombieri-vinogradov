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

theorem Nat.Icc_sqrt_nonempty : (Nat.Icc (√x) x).Nonempty := by
  by_cases hx : 4 ≤ x
  · use ⌊x⌋₊
    simp only [mem_Icc]
    constructor
    · trans x - 1
      · rw [Real.sqrt_le_iff]
        have := le_x
        constructor
        · linarith
        · apply le_of_sub_nonneg
          nlinarith
      · simp only [tsub_le_iff_right]
        apply le_of_lt
        apply Nat.lt_floor_add_one
    · apply Nat.floor_le (x_nonneg)
  · use 2
    simp only [mem_Icc, cast_ofNat]
    constructor
    · rw [Real.sqrt_le_iff]
      norm_num
      linarith
    · exact le_x

private theorem maxya.extracted_3 (q : ℕ) (h : NeZero q) : (Nat.Icc (√x) x ×ˢ (Finset.univ : Finset (ZMod q)ˣ)).Nonempty := by
  simp [Nat.Icc_sqrt_nonempty]

/-- The maximum of $f$ over all $y \in \left[\sqrt{x}, x\right]$ and $a \in (\mathbb{Z} / q\mathbb{Z})^* -/
noncomputable def maxya [ProofData] (q : ℕ) (f : ℕ → ZMod q → ℝ) : ℝ :=
open Classical in
  if h : NeZero q then
    ((Nat.Icc (√x) x) ×ˢ (Finset.univ : Finset (ZMod q)ˣ)).sup' (maxya.extracted_3 q h) (fun ⟨n, a⟩ ↦ f n a)
  else 0

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
