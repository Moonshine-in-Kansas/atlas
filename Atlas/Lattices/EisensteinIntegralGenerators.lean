import Atlas.Lattices.EisensteinGenerators
import Atlas.Algebra.EisensteinSpan

namespace Atlas.Lattices
open Atlas.Algebra

theorem eisensteinLeechModule_integral_generators
    (S : Submodule ℤ EisensteinCoordinates)
    (hg : ∀ g ∈ eisensteinGeneratorSet, g ∈ S)
    (hω : ∀ g ∈ eisensteinGeneratorSet, eisensteinOmega • g ∈ S) :
    eisensteinLeechModule.restrictScalars ℤ ≤ S := by
  rw [eisensteinLeechModule_eq_span]
  exact eisensteinSpan_subset_intSubmodule _ S hg hω

/-- An explicit integral generating set, retaining both scalar basis elements. -/
def eisensteinIntegralGeneratorSet : Set EisensteinCoordinates :=
  eisensteinGeneratorSet ∪ ((fun z => eisensteinOmega • z) '' eisensteinGeneratorSet)

theorem eisensteinLeechModule_eq_integral_span :
    eisensteinLeechModule.restrictScalars ℤ =
      Submodule.span ℤ eisensteinIntegralGeneratorSet := by
  apply le_antisymm
  · apply eisensteinLeechModule_integral_generators
    · intro g hg
      exact Submodule.subset_span (Or.inl hg)
    · intro g hg
      exact Submodule.subset_span (Or.inr ⟨g, hg, rfl⟩)
  · apply Submodule.span_le.mpr
    intro z hz
    rcases hz with hz | ⟨g, hg, rfl⟩
    · exact eisensteinGeneratorSet_mem hz
    · exact eisensteinLeechModule.smul_mem _ (eisensteinGeneratorSet_mem hg)

end Atlas.Lattices
