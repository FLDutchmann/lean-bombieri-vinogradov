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


noncomputable def Nat.Icc (x y : ℝ) : Finset ℕ := Finset.Icc (⌈x⌉₊) (⌊y⌋₊)

@[simp]
theorem Nat.mem_Icc (x : ℝ) {y : ℝ} (n : ℕ) (hy : 0 ≤ y) :
    n ∈ Nat.Icc x y ↔ x ≤ n ∧ n ≤ y := by
  simp [Nat.Icc, Nat.le_floor_iff hy]

theorem Nat.Icc_zero_nonempty {x : ℝ} (hx : 0 ≤ x) : (Nat.Icc 0 x).Nonempty := by
  use 0
  simp [hx]

noncomputable def summatory {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) : R :=
  ∑ i ∈ Nat.Icc 0 x, f i

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
noncomputable def Delta (f : ℕ → ℝ) (x : ℝ) (q a : ℕ) : ℝ :=
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
  y : ℝ
  le_x : 2 ≤ x
  sqrt_x_le_y : Real.sqrt x ≤ y
  y_le_x : y ≤ x
  UV_le : U * V ≤ Real.sqrt x
  le_U : Real.exp (Real.sqrt x) ≤ U
  le_V : Real.exp (Real.sqrt x) ≤ V


/-- Restrict an arithmetic function to a set, setting all values outside the set to zero.
Like `Set.indicator` but for `ArithmeticFunction`. -/
noncomputable def ArithmeticFunction.on {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨s.indicator f, by simp⟩

section Lambda

open ProofData

variable [data : ProofData]

/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
@[blueprint (statement :=
/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
)]
noncomputable def LambdaLEU [ProofData] : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt.on (Set.Icc 1 (Nat.floor U))

scoped[BV] notation3 "Λ≤U" => LambdaLEU

open BV

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
