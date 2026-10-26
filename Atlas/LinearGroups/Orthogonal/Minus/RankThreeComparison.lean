import Atlas.LinearGroups.Orthogonal.Minus.RankThreeKernel
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeOrderComparison

/-! The actual unitary exterior-square comparison, with cardinality used only
for surjectivity of the already constructed injective homomorphism. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem rankThreePSUHom_surjective (hdeg : Module.finrank F K = 2) :
    Function.Surjective (rankThreePSUHom hdeg) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨rankThreePSUHom_injective hdeg,(rankThree_projective_card_eq_unitary hdeg).symm⟩).surjective

/-- The actual PSU4 quotient acts as all projective elementary isometries of the minus form. -/
def rankThreeUnitaryEquiv (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.PSU F K 4 hdeg ≃* ProjectiveElementary (form hdeg 2) :=
  MulEquiv.ofBijective (rankThreePSUHom hdeg)
    ⟨rankThreePSUHom_injective hdeg,rankThreePSUHom_surjective hdeg⟩

theorem rankThreeUnitaryEquiv_projection (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) :
    rankThreeUnitaryEquiv hdeg (Atlas.Unitary.projection F K 4 hdeg g) =
      projectiveElementaryMap (form hdeg 2) (rankThreeElementaryHom hdeg g) := rfl

def rankThreeProjectiveEquiv (hdeg : Module.finrank F K = 2) :
    ProjectiveElementary (form hdeg 2) ≃* Atlas.Unitary.PSU F K 4 hdeg :=
  (rankThreeUnitaryEquiv hdeg).symm

end Atlas.Orthogonal.Minus
