import Mathlib
import Architect
import BV.Defs

open ArithmeticFunction
open scoped Moebius zeta
open BV

/-!
### Preliminaries

Decomposing the von Mangoldt function into type I and type II functions. -/

@[blueprint (statement := /--
$$\Delta_f(x ;q, a) := \sum_{n \le x, ~ n \equiv a \pmod q} f(n) ~ - \frac{1}{\varphi(q)} \sum_{n \le x, (n, q) = 1} f(n) $$
for $x \ge 1$, $q \in \N$
-/)]
noncomputable def Delta {R : Type*} [Field R] (f : ℕ → R) (x : ℝ) (q : ℕ) (a : ZMod q) : R :=
  summatory ((Nat.modEqs (a : ZMod q)).indicator f) x -
  ((Nat.totient q : R)⁻¹) * summatory (onCoprime q f) x

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
    (↑(Delta f y q a) : ℂ) = (1 / (Nat.totient q : ℂ)) *
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
$$\Delta_{\Lambda}(x; q, a) = \psi(x; q,a) - \frac{1}{\varphi(q)} \sum_{n \le x, n \not\mid q} \Lambda{n} $$
-/
) (notReady := true)]
theorem Delta_Lambda_eq (x : ℝ) (q : ℕ) (a : ZMod q) :
    Δ_[Λ](x; q, a) = ψ x a - (q.totient : ℝ)⁻¹ * ∑ n ∈ Nat.Icc 0 x with ¬ n ∣ q, Λ n
   := by
  sorry

def C_D1 : ℝ := sorry
def c_PNT : ℝ := sorry

open ProofData in
@[blueprint (statement :=
/--
$$ \sum_{n \le x, n \not \mid q} \Lambda{n} = x + O(xe^{-c\sqrt{\log x}}+\log q)$$
-/
)]
lemma sum_primes_not_dvd_log_eq_id [ProofData] {q : ℕ}  :
  |summatory (fun n ↦ if ¬ n ∣ q then Λ n else 0) x - x| ≤ C_D1 * (x*Real.exp (- c_PNT * √(Real.log x)) + log q) := by
  /-- TODO: Rephrase this in terms of an arbitrary power of log savings, so we can use the Siegel-Walfisz assumption. -/
  sorry

@[blueprint (latexEnv := "lemma") (statement := /--
If $f$ is an arithmetic function supported on $[1, y]$ then
$$\Delta_{f*g}(x;\,q,\,a) = \sum_{\substack{k \le y \\ (k,q)=1}} f(k)\, \Delta_g\!\left(\frac{x}{k};\, q,\, a\bar{k}\right)$$
-/)]
theorem Delta_convolution_eq {x : ℝ} {q : ℕ} {a : ZMod q} (f g : ArithmeticFunction ℝ) (y : ℝ) (hf_support : ∀ n : ℕ, n > y → f n = 0) :
    Δ_[f*g](x; q, a) = summatory (fun k ↦ if k.Coprime q then f k * Δ_[g](x/k; q, a * (k : ZMod q)⁻¹) else 0) y := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
For $x \ge 1$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_1(x;\, q,\, a)| \le 1$$
-/) (proof := /--
Carefully consider length $q$ intervals. Alternatively, write
$$\Delta_1(t;\, q,\, a) = \frac{1}{\varphi(q)} \sum_{a' \in (\Z/q\Z)^*} \left( \sum_{\substack{n \le t \\ n \equiv a \pmod{q}}} 1 - \sum_{\substack{n \le t \\ n \equiv a' \pmod{q}}} 1 \right)$$
and note each inner difference is bounded by $1$ in absolute value.
-/)]
theorem Delta_one_bound {x : ℝ} {q : ℕ} {a : ZMod q} (ha : IsUnit a) : |Δ_[(ζ : ArithmeticFunction ℝ)](x; q, a)| ≤ 1 := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable on $[1, x]$ then
$$\Delta_g(x;\,q,\,a) = \Delta_1(x;\,q,\,a)\,g(x) - \int_1^x \Delta_1(t;\,q,\,a)\,g'(t)\,\mathrm{d}t$$
-/) (proof := /--
By Abel summation.
-/) (uses := [Delta_one_bound])]
theorem Delta_abel_summation {q : ℕ} {a : ZMod q} (g g': ℝ → ℝ) {x : ℝ} (hg : ContDiffOn ℝ 1 g (Set.Icc 1 x)) (hg' : ∀ t ∈ Set.Icc 1 x, HasDerivAt g (g' t) t) :
    Δ_[fun n ↦ g n](x; q, a) = Δ_[(ζ : ArithmeticFunction ℝ)](x; q, a) - ∫ t in 1..x, Δ_[(ζ : ArithmeticFunction ℝ)](t; q, a) * g' t := by sorry

@[blueprint (latexEnv := "lemma") (statement := /--
If $g$ is continuously differentiable and monotone on $[1, x]$ with $g(0) = 0$, then for all $t \ge 1$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_g(x;\, q,\, a)| \le 2g(x)$$
-/) (uses := [Delta_one_bound, Delta_abel_summation])]
theorem Delta_monotone_bound {q : ℕ} {a : ZMod q} (g : ℝ → ℝ) {x : ℝ} (hg : ContDiffOn ℝ 1 g (Set.Icc 1 x)) :
    |Δ_[fun n ↦ g n](x; q, a)| ≤ 2 * g x := by sorry

@[blueprint (statement := /--
Let $v \ge 0$ and let $f$ be an arithmetic function supported on $[1, x]$. For $x \ge 2$, $q \in \N$ and $a \in (\Z/q\Z)^*$,
$$|\Delta_{f * \log^v}(x;\, q,\, a)| \le 2(\log x)^v \sum_{k \le x} |f(k)|$$
-/) (proof := /--
Straightforward application of the previous lemmas.
-/) (uses := [Delta_one_bound, Delta_abel_summation, Delta_monotone_bound])]
theorem Delta_flog_bound {v : ℕ} {f : ArithmeticFunction ℝ} {x : ℝ} (hx : 2 ≤ x) {q : ℕ} (a : ZMod q) (ha : IsUnit a) : Δ_[f * ppow log v](x; q, a) ≤ 2 * (Real.log x)^v * summatory (fun k ↦ |f k|) x := by sorry
