import Atlas.LinearGroups.Triality.ScalarIntersection

/-! Faithful projective split-D₄ comparison for the actual matrix carrier. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def intoProjective : Group F K →* ProjectiveElementary (formD 4 K) :=
  (projectiveElementaryMap (formD 4 K)).comp (intoElementary F K)

theorem intoProjective_injective (hdeg : Module.finrank F K = 3) :
    Function.Injective (intoProjective F K) := by
  apply (MonoidHom.ker_eq_bot_iff (intoProjective F K)).mp
  apply le_antisymm _ bot_le
  intro g hg
  have hs : intoElementary F K g ∈ elementaryScalarSubgroup (formD 4 K) := by
    rw [← projectiveElementaryMap_kernel]
    exact hg
  obtain ⟨c,hc,hs⟩ := hs
  exact Subtype.ext (scalar_eq_one F K hdeg g.val g.property c hs)

end Atlas.Triality
