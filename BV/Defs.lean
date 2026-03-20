import Mathlib
import Architect


open ArithmeticFunction
open scoped Moebius zeta


/-- The logarithmic integral function: li(x) = ∫₂ˣ dt/(log t) -/
@[blueprint (latexEnv := "definition") (statement := /-- $\li(x) = \int_2^x \frac{\mathrm{d}t}{\log t}$ -/)]
noncomputable def logIntegral (x : ℝ) : ℝ := sorry

/-- Prime-counting function in arithmetic progression:
π(x; q, a) counts primes p ≤ x with p ≡ a (mod q)
-/
noncomputable def primeCountingAP (x : ℝ) (q : ℕ) (a : ℕ) : ℝ := sorry


/-!
### Preliminaries

Decomposing the von Mangoldt function into type I and type II functions. -/

@[blueprint (statement := /--
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$
-/)]
def Delta (f : ℕ → ℝ) (x : ℝ) (q a : ℕ) : ℝ :=
  sorry

notation3 "Δ_[" f "](" x "; " q ", " a ")" => Delta f x q a

@[blueprint(statement :=
/--
$$\Delta_f(y ;q, a) = \frac{1}{\varphi(q)} \sum_{\chi \pmod{q}, \chi \ne \chi_0} \bar\chi(a) \sum_{n \le y} f(n) \chi(n) $$
-/)
 (notReady := true)]
lemma Delta_eq_sum_char : 1 = 1 := by
  sorry

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
