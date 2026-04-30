import Mathlib.MeasureTheory.Function.LocallyIntegrable


open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory
section LocallyIntegrableOn

/-- This lemma is in a more recent version of mathlib -/
@[gcongr]
axiom LocallyIntegrableOn.congr (h : f =ᵐ[μ.restrict s] g) (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn g s μ


end LocallyIntegrableOn
end MeasureTheory
