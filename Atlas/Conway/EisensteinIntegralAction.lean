import Atlas.Conway.EisensteinCentralizer
import Atlas.Lattices.EisensteinShortLines

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Restriction of a full Hermitian lattice isometry to the actual rational lattice. -/
def eisensteinRationalIntegralAction (g : eisensteinHermitianGroup) :
    rationalEisensteinLattice ≃ₗ[ℤ] rationalEisensteinLattice where
  toFun z := ⟨g.val z.val, (g.property.2.2 z.val).mp z.property⟩
  invFun z := ⟨g.val.symm z.val, (g.property.2.2 _).mpr (by
    simpa only [LinearEquiv.apply_symm_apply] using z.property)⟩
  left_inv z := Subtype.ext (g.val.symm_apply_apply z.val)
  right_inv z := Subtype.ext (g.val.apply_symm_apply z.val)
  map_add' z w := Subtype.ext (map_add g.val z.val w.val)
  map_smul' a z := Subtype.ext (map_zsmul g.val a z.val)

/-- The action on the integral Eisenstein lattice, with no change of model. -/
def eisensteinIntegralAction (g : eisensteinHermitianGroup) :
    EisensteinLattice ≃ₗ[ℤ] EisensteinLattice :=
  eisensteinIntegralEmbeddingEquiv.trans
    ((eisensteinRationalIntegralAction g).trans eisensteinIntegralEmbeddingEquiv.symm)

theorem eisensteinIntegralAction_agrees (g : eisensteinHermitianGroup) (z : EisensteinLattice) :
    eisensteinCoordinateEmbedding (eisensteinIntegralAction g z).val =
      g.val (eisensteinCoordinateEmbedding z.val) := by
  exact congrArg Subtype.val (eisensteinIntegralEmbeddingEquiv.apply_symm_apply
    (eisensteinRationalIntegralAction g (eisensteinIntegralEmbeddingEquiv z)))

theorem eisensteinIntegralAction_norm (g : eisensteinHermitianGroup) (z : EisensteinLattice) :
    eisensteinNorm (eisensteinIntegralAction g z) = eisensteinNorm z := by
  unfold eisensteinNorm
  rw [eisensteinIntegralAction_agrees]
  exact congrArg eisensteinReal (g.property.2.1 _ _)

theorem eisensteinIntegralAction_scalar (g : eisensteinHermitianGroup)
    (a : Eisenstein) (z : EisensteinLattice) :
    eisensteinIntegralAction g (a • z) = a • eisensteinIntegralAction g z := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  change g.val (eisensteinCoordinateEmbedding (a • z.val)) =
    eisensteinCoordinateEmbedding (a • (eisensteinIntegralAction g z).val)
  rw [eisensteinCoordinateEmbedding_smul, eisensteinCoordinateEmbedding_smul,
    eisensteinIntegralAction_agrees, g.property.1]

theorem eisensteinIntegralAction_one (z : EisensteinLattice) :
    eisensteinIntegralAction 1 z = z := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  rfl

theorem eisensteinIntegralAction_mul (g h : eisensteinHermitianGroup)
    (z : EisensteinLattice) :
    eisensteinIntegralAction (g*h) z = eisensteinIntegralAction g (eisensteinIntegralAction h z) := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  simp only [eisensteinIntegralAction_agrees]
  rfl

/-- The full group acts through integral linear automorphisms. -/
def eisensteinIntegralActionHom : eisensteinHermitianGroup →*
    (EisensteinLattice ≃ₗ[ℤ] EisensteinLattice) where
  toFun := eisensteinIntegralAction
  map_one' := LinearEquiv.ext eisensteinIntegralAction_one
  map_mul' g h := LinearEquiv.ext (eisensteinIntegralAction_mul g h)

theorem eisensteinIntegralAction_theta_range (g : eisensteinHermitianGroup) :
    eisensteinThetaEnd.range.map (eisensteinIntegralAction g).toLinearMap =
      eisensteinThetaEnd.range := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨eisensteinIntegralAction g y, (eisensteinIntegralAction_scalar g _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨eisensteinThetaEnd ((eisensteinIntegralAction g).symm y), ⟨_, rfl⟩, ?_⟩
    change eisensteinIntegralAction g (eisensteinTheta • _) = eisensteinTheta • y
    rw [eisensteinIntegralAction_scalar, LinearEquiv.apply_symm_apply]

/-- The induced automorphism of the actual theta quotient. -/
def eisensteinClassAction (g : eisensteinHermitianGroup) :
    EisensteinClasses ≃ₗ[ℤ] EisensteinClasses :=
  Submodule.Quotient.equiv _ _ (eisensteinIntegralAction g)
    (eisensteinIntegralAction_theta_range g)

@[simp] theorem eisensteinClassAction_mk (g : eisensteinHermitianGroup) (z : EisensteinLattice) :
    eisensteinClassAction g (eisensteinClass z) =
      eisensteinClass (eisensteinIntegralAction g z) := rfl

end Atlas.Conway
