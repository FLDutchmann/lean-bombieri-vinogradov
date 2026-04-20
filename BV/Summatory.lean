import Mathlib

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

@[simp]
theorem Nat.Icc_eq_empty_of_neg (x : ℝ) {y : ℝ} (hy : y < 0) : Nat.Icc x y = ∅ := by
  simp [Nat.Icc, hy]

@[grind =>]
theorem Nat.Icc_mono_left {x₁ x₂ y : ℝ} (hx : x₁ ≤ x₂) : Nat.Icc x₂ y ⊆ Nat.Icc x₁ y := by
  intro n
  simp only [mem_Icc, and_imp]
  grind

@[grind =>]
theorem Nat.Icc_mono_right {x y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) : Nat.Icc x y₁ ⊆ Nat.Icc x y₂ := by
  intro n
  simp only [mem_Icc, and_imp]
  grind

noncomputable def summatory {R : Type*} [AddCommMonoid R] (f : ℕ → R) (x : ℝ) : R :=
  ∑ i ∈ Nat.Icc 1 x, f i

theorem summatory_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : ℕ → R) (x : ℝ) (hf : ∀ n : ℕ, n ≤ x → 0 ≤ f n ) : 0 ≤ summatory f x := by
  simp [summatory]
  apply Finset.sum_nonneg
  simp only [Nat.mem_Icc]
  grind

theorem summatory_of_neg {R : Type*} [AddCommMonoid R]
    {f : ℕ → R} {x : ℝ} (hx : x < 0) :
    summatory f x = 0 := by
  simp [summatory, Nat.Icc_eq_empty_of_neg _ hx]

theorem summatory_apply {R : Type*} [AddCommMonoid R] {f : ℕ → R} {x : ℝ} :
    summatory f x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n := by
  by_cases hx : 0 ≤ x
  · simp [summatory]
    congr 1
    ext n
    simp only [Nat.mem_Icc, Nat.one_le_cast, Finset.mem_Ioc, Nat.le_floor_iff hx]
    grind
  · have : x < 0 := by linarith
    simp [Nat.floor_of_nonpos this.le, summatory_of_neg this]

@[congr]
theorem summatory_congr {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {f g : ℕ → R} {x y : ℝ} (hxy : x = y) (h : ∀ n : ℕ, 0 < n → n ≤ x → f n = g n) :
    summatory f x = summatory g y := by
  subst hxy
  simp [summatory]
  apply Finset.sum_congr rfl fun n hn ↦ ?_
  simp only [Nat.mem_Icc, Nat.one_le_cast] at hn
  apply h n (by grind) hn.2

theorem summatory_congr_fun {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {f g : ℕ → R} {x : ℝ} (h : ∀ n : ℕ, 0 < n → n ≤ x → f n = g n) :
    summatory f x = summatory g x := by
  simp [summatory]
  apply Finset.sum_congr rfl fun n hn ↦ ?_
  simp only [Nat.mem_Icc, Nat.one_le_cast] at hn
  apply h n (by grind) hn.2

@[gcongr]
theorem summatory_eq_summatory_of_lt_of_eq_zero {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : ℕ → R) (x y : ℝ) (hxy : x ≤ y) (hf : ∀ n : ℕ, x < n ∧ n ≤ y → f n = 0) :
    summatory f x = summatory f y := by
  simp [summatory]
  apply Finset.sum_subset
  · grind
  simp only [Nat.mem_Icc]
  intro n hy hx
  grind

@[push]
theorem summatory_add_distrib {R : Type*} [AddCommMonoid R] {f g : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ f n + g n) x = summatory f x + summatory g x := by
  simp [summatory, Finset.sum_add_distrib]

@[push]
theorem summatory_sub_distrib {R : Type*} [AddCommGroup R] {f g : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ f n - g n) x = summatory f x - summatory g x := by
  simp [summatory]

@[push]
theorem summatory_neg {R : Type*} [AddCommGroup R] {f : ℕ → R} {x : ℝ} :
    summatory (fun n ↦ - f n) x = - summatory f x := by
  simp [summatory]

@[push]
theorem mul_summatory {R : Type*} [Semiring R] {f : ℕ → R} {c : R} {x : ℝ} :
    summatory (fun n ↦ c * f n) x = c * summatory f x := by
  simp [summatory, Finset.mul_sum]

@[push]
theorem summatory_mul {R : Type*} [Semiring R] {f : ℕ → R} {c : R} {x : ℝ} :
    summatory (fun n ↦ f n * c) x = summatory f x * c := by
  simp [summatory, Finset.sum_mul]

@[simp, push]
theorem summatory_zero {R : Type*} [AddCommMonoid R] {x : ℝ} :
    summatory (fun _ ↦ (0 : R)) x = 0 := by
  simp [summatory]


/- This positivity extension was written by an LLM. -/
open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity summatory _ _]
def summatory_positivity : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(summatory $f $x) =>
    let i : Q(ℕ) ← mkFreshExprMVarQ q(ℕ) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    match rbody.toNonneg with
    | some pbody =>
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      assumeInstancesCommute
      return .nonnegative q(summatory_nonneg $f $x (fun n _ => $pr n))
    | none => throwError "body not nonneg"
  | _, _, _ => throwError "not summatory"

theorem summatory_le_UB {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x : ℝ) (hx : 0 ≤ x) (M : ℝ) (hf : ∀ n : ℕ, n ≤ x → ‖f n‖ ≤ M) :
  ‖summatory f x‖ ≤ x * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hx)]
    simp
  grw [summatory, norm_sum_le]
  trans ∑ i ∈ Nat.Icc 1 x, M
  · gcongr with n hn
    apply hf
    simp only [Nat.mem_Icc, Nat.one_le_cast] at hn
    exact hn.2
  · simp [hx]
    gcongr
    exact Nat.floor_le hx

theorem summatory_le_support_mul_UB {R : Type*} {f : ℕ → R}
    [NormedAddCommGroup R] [Lattice R] [IsOrderedAddMonoid R] (x S : ℝ)
    (hS : 0 ≤ S) (M : ℝ) (hf : ∀ n : ℕ, n ≤ S → ‖f n‖ ≤ M)
    (hf_support : ∀ n : ℕ, n > S → f n = 0) :
  ‖summatory f x‖ ≤ S * M := by
  have hM : 0 ≤ M := by
    grw [← hf 0 (mod_cast hS)]
    simp
  by_cases hx : x < 0
  · rw [summatory_of_neg hx]
    simp only [norm_zero, ge_iff_le]
    positivity
  push_neg at hx
  by_cases hyS : x ≤ S
  · apply le_trans <| summatory_le_UB x (by gcongr) M _
    · gcongr
    · grind
  · push_neg at hyS
    calc _ = ‖summatory f S‖ := ?A
     _ ≤ _ := summatory_le_UB S hS M hf
    congr 1
    apply (summatory_eq_summatory_of_lt_of_eq_zero ..).symm
    · linarith only [hyS]
    · grind
