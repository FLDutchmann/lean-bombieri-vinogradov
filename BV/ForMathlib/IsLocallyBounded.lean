import Mathlib

open MeasureTheory

theorem MeasureTheory.IntegrableAtFilter.mul_boundedAtFilter {α : Type u_1} {ε' : Type u_4}
    {mα : MeasurableSpace α} {μ : Measure α} [NormedRing ε']
    {l : Filter α} (hl : l.IsMeasurablyGenerated) {f g : α → ε'} (hg_meas : AEStronglyMeasurable g μ)
    (hf : IntegrableAtFilter f l μ) (hg : l.BoundedAtFilter g) :
    IntegrableAtFilter (f * g) l μ := by
  obtain ⟨s, hsl, hs⟩ := hf
  obtain ⟨s', hs'l, hs'_meas, hs'⟩ := hl.exists_measurable_subset hsl
  obtain ⟨c, hc_pos, hc⟩ := hg.exists_pos
  rw [Asymptotics.IsBigOWith, Filter.Eventually] at hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at hc
  obtain ⟨t, htl, ht_meas, ht⟩ := hl.exists_measurable_subset hc
  use s' ∩ t
  simp only [Filter.inter_mem_iff, hs'l, htl, and_self, true_and]
  rw [← MeasureTheory.integrable_indicator_iff (by measurability),
    show f * g = fun n ↦ f n * g n by rfl, Set.indicator_mul]
  apply Integrable.mul_bdd (c := c)
  · rw [integrable_indicator_iff (by measurability)]
    apply hs.mono_set
    grind
  · fun_prop (disch := measurability)
  · filter_upwards with x
    by_cases hx : x ∈ s' ∩ t
    · simp [hx]
      exact ht (Set.mem_of_mem_inter_right hx)
    · simp [hx]
      grind

-- TODO: Figure out how to not repeat the previous proof
theorem MeasureTheory.IntegrableAtFilter.boundedAtFilter_mul {α : Type u_1} {ε' : Type u_4}
    {mα : MeasurableSpace α} {μ : Measure α} [NormedRing ε']
    {l : Filter α} (hl : l.IsMeasurablyGenerated) {f g : α → ε'} (hg_meas : AEStronglyMeasurable g μ)
    (hf : IntegrableAtFilter f l μ) (hg : l.BoundedAtFilter g) :
    IntegrableAtFilter (g * f) l μ := by
  obtain ⟨s, hsl, hs⟩ := hf
  obtain ⟨s', hs'l, hs'_meas, hs'⟩ := hl.exists_measurable_subset hsl
  obtain ⟨c, hc_pos, hc⟩ := hg.exists_pos
  rw [Asymptotics.IsBigOWith, Filter.Eventually] at hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at hc
  obtain ⟨t, htl, ht_meas, ht⟩ := hl.exists_measurable_subset hc
  use s' ∩ t
  simp only [Filter.inter_mem_iff, hs'l, htl, and_self, true_and]
  rw [← MeasureTheory.integrable_indicator_iff (by measurability),
    show g * f = fun n ↦ g n * f n by rfl, Set.indicator_mul]
  apply Integrable.bdd_mul (c := c)
  · rw [integrable_indicator_iff (by measurability)]
    apply hs.mono_set
    grind
  · fun_prop (disch := measurability)
  · filter_upwards with x
    by_cases hx : x ∈ s' ∩ t
    · simp [hx]
      exact ht (Set.mem_of_mem_inter_right hx)
    · simp [hx]
      grind


theorem Filter.BoundedAtFilter.integrableAtFilter {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} {f : α → β} {l : Filter α}
    (hl : l.IsMeasurablyGenerated) (hμ : μ.FiniteAtFilter l) (hf : l.BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f l μ) :
    IntegrableAtFilter f l μ := by
  rw [BoundedAtFilter] at hf
  apply hf.integrableAtFilter
  · exact hf_meas
  · apply Filter.Tendsto.integrableAtFilter (b := 1)
    · apply tendsto_const_nhds
    · apply (Measurable.stronglyMeasurable _).stronglyMeasurableAtFilter
      fun_prop
    · exact hμ

theorem Filter.BoundedAtFilter.integrableAtFilter_nhds {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} (a : α)
    (hf : (nhds a).BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f (nhds a) μ) :
    IntegrableAtFilter f (nhds a) μ :=
  Filter.BoundedAtFilter.integrableAtFilter (nhds_isMeasurablyGenerated _) (μ.finiteAt_nhds _) hf hf_meas

theorem Filter.BoundedAtFilter.integrableAtFilter_nhdsWithin {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} {s : Set α} (hs : MeasurableSet s) {a : α}
    (hf : (nhdsWithin a s).BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f (nhdsWithin a s) μ) :
    IntegrableAtFilter f (nhdsWithin a s) μ :=
  Filter.BoundedAtFilter.integrableAtFilter (hs.nhdsWithin_isMeasurablyGenerated _) (μ.finiteAt_nhdsWithin _ _) hf hf_meas

-- Potential quibble: It might be helpful to say that e.g. s : ℝ → Finset ℕ is locally bounded, which in this case requires a Norm instance on Finset.
@[fun_prop]
structure IsLocallyBounded {α β : Type*} [TopologicalSpace α] [Norm β] (f : α → β) where
  locally_bdd' : ∀ x, (nhds x).BoundedAtFilter f

theorem IsLocallyBounded.boundedAtFilter {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β}
    (hf : IsLocallyBounded f) (x : α) : (nhds x).BoundedAtFilter f := hf.locally_bdd' x


theorem IsLocallyBounded.locallyIntegrable {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] (f : α → β) (hf_bdd : IsLocallyBounded f)
    (hf_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrable f μ := fun _ ↦
  Filter.BoundedAtFilter.integrableAtFilter_nhds _ (hf_bdd.boundedAtFilter _) hf_meas.stronglyMeasurableAtFilter

theorem MeasureTheory.LocallyIntegrable.mul_isLocallyBounded
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} (hf : LocallyIntegrable f μ)
    (hg : IsLocallyBounded g) (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrable (fun x => f x * g x) μ := fun x ↦
  (hf x).mul_boundedAtFilter (nhds_isMeasurablyGenerated _) hg_meas (hg.locally_bdd' x)

theorem MeasureTheory.LocallyIntegrable.isLocallyBounded_mul
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} (hf : LocallyIntegrable f μ)
    (hg : IsLocallyBounded g) (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrable (fun x => g x * f x) μ := fun x ↦
  (hf x).boundedAtFilter_mul (nhds_isMeasurablyGenerated _) hg_meas (hg.locally_bdd' x)

section Combinators
variable {α β : Type*}

@[fun_prop]
theorem const_isLocallyBounded [TopologicalSpace α] [SeminormedAddCommGroup β] (c : β) :
    IsLocallyBounded (fun (_ : α) ↦ c) :=
  ⟨fun _ ↦ Filter.const_boundedAtFilter _ c⟩

@[fun_prop]
theorem IsLocallyBounded.add [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    (hf : IsLocallyBounded f) (hg : IsLocallyBounded g) :
    IsLocallyBounded (f + g) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).add (hg.boundedAtFilter _)⟩

@[fun_prop]
theorem IsLocallyBounded.neg [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    (hf : IsLocallyBounded f) :
    IsLocallyBounded (- f) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).neg⟩

@[fun_prop]
theorem IsLocallyBounded.smul
    {𝕜 : Type*} [TopologicalSpace α] [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → β} (c : 𝕜)
    (hf : IsLocallyBounded f) : IsLocallyBounded (c • f) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).smul _⟩

@[fun_prop]
theorem IsLocallyBounded.mul [TopologicalSpace α] [SeminormedRing β] {f g : α → β}
    (hf : IsLocallyBounded f) (hg : IsLocallyBounded g) :
    IsLocallyBounded (f * g) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).mul (hg.boundedAtFilter _)⟩

end Combinators


section On

@[fun_prop]
structure IsLocallyBoundedOn {α β : Type*} [TopologicalSpace α] [Norm β] (f : α → β) (s : Set α) where
  locally_bddOn' : ∀ x ∈ s, (nhdsWithin x s).BoundedAtFilter f

/- The API (only the statements) for IsLocallyBoundedOn was generalized from IsLocallyBounded using Claude Sonnet 4.6-/

theorem IsLocallyBoundedOn.boundedAtFilter {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) {x : α} (hx : x ∈ s) :
    (nhdsWithin x s).BoundedAtFilter f := hf.locally_bddOn' x hx

theorem IsLocallyBoundedOn.locallyIntegrableOn {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (hf_bdd : IsLocallyBoundedOn f s) (hf_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrableOn f s μ := fun _ ha ↦
  Filter.BoundedAtFilter.integrableAtFilter_nhdsWithin hs (hf_bdd.boundedAtFilter ha) hf_meas.stronglyMeasurableAtFilter

theorem MeasureTheory.LocallyIntegrableOn.mul_isLocallyBoundedOn
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hs : MeasurableSet s)
    (hf : LocallyIntegrableOn f s μ) (hg : IsLocallyBoundedOn g s)
    (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrableOn (fun x => f x * g x) s μ := fun x hx ↦
  (hf x hx).mul_boundedAtFilter (hs.nhdsWithin_isMeasurablyGenerated _) hg_meas (hg.locally_bddOn' x hx)

theorem MeasureTheory.LocallyIntegrableOn.isLocallyBoundedOn_mul
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hs : MeasurableSet s)
    (hf : LocallyIntegrableOn f s μ) (hg : IsLocallyBoundedOn g s)
    (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrableOn (fun x => g x * f x) s μ := fun x hx ↦
  (hf x hx).boundedAtFilter_mul (hs.nhdsWithin_isMeasurablyGenerated _) hg_meas (hg.locally_bddOn' x hx)



section OnCombinators
variable {α β : Type*}

@[fun_prop]
theorem const_isLocallyBoundedOn [TopologicalSpace α] [SeminormedAddCommGroup β] (c : β)
    (s : Set α) : IsLocallyBoundedOn (fun (_ : α) ↦ c) s :=
  ⟨fun _ _ ↦ Filter.const_boundedAtFilter _ c⟩

@[fun_prop]
theorem IsLocallyBoundedOn.add [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) (hg : IsLocallyBoundedOn g s) :
    IsLocallyBoundedOn (f + g) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).add (hg.boundedAtFilter hx)⟩

@[fun_prop]
theorem IsLocallyBoundedOn.neg [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) :
    IsLocallyBoundedOn (-f) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).neg⟩

@[fun_prop]
theorem IsLocallyBoundedOn.smul
    {𝕜 : Type*} [TopologicalSpace α] [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → β} {s : Set α} (c : 𝕜)
    (hf : IsLocallyBoundedOn f s) : IsLocallyBoundedOn (c • f) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).smul _⟩

@[fun_prop]
theorem IsLocallyBoundedOn.mul [TopologicalSpace α] [SeminormedRing β] {f g : α → β} {s : Set α}
    (hf : IsLocallyBoundedOn f s) (hg : IsLocallyBoundedOn g s) :
    IsLocallyBoundedOn (f * g) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).mul (hg.boundedAtFilter hx)⟩

end OnCombinators

end On

@[fun_prop]
def IsLocallyBounded.isLocallyBoundedOn {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β} (s : Set α)
    (hf : IsLocallyBounded f) : IsLocallyBoundedOn f s :=
  ⟨fun a _ ↦ (hf.locally_bdd' a).mono nhdsWithin_le_nhds⟩
