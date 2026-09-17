import Atlas.LinearGroups.Orthogonal.D3ExteriorProjective
import Atlas.LinearGroups.Orthogonal.D3ExteriorOrder

/-! # The actual D₃/A₃ exterior-square comparison over every finite field

The map is induced by the genuine bivector action. Its injectivity follows
from the structural scalar kernel, while the independently proved uniform
orders give surjectivity. No simplicity or recognition-from-order argument
is used to obtain a map or its kernel.
-/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
variable {F : Type*} [Field F] [Finite F]

/-- The already constructed injective exterior-square action exhausts the target quotient. -/
theorem projectiveHom_surjective : Function.Surjective (projectiveHom (F := F)) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨projectiveHom_injective, card_psl_four_eq_projectiveD_three⟩).surjective

/-- Actual exterior-square comparison PSL₄(F) ≃ PΩ⁺₆(F), in every finite characteristic. -/
def projectiveEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F ≃*
    ProjectiveElementary (formD 3 F) :=
  MulEquiv.ofBijective projectiveHom ⟨projectiveHom_injective, projectiveHom_surjective⟩

/-- Agreement of the isomorphism with the original determinant-one exterior-square action. -/
theorem projectiveEquiv_projection (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    projectiveEquiv (QuotientGroup.mk g) = projectiveElementaryMap _ (toElementary g) := rfl

/-- The comparison in the D-to-A direction, retaining the same actual group models. -/
def d3EquivPSL4 : ProjectiveElementary (formD 3 F) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) F := projectiveEquiv.symm

end Atlas.Orthogonal.D3Exterior
