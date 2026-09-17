import Atlas.Fischer.BinaryFourAffineOrder
import Atlas.LinearGroups.Elementary

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Over the binary field every invertible matrix already has determinant one. -/
theorem binaryFour_toGL_surjective : Function.Surjective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 4) Bit →*
      Matrix.GeneralLinearGroup (Fin 4) Bit) := by
  intro g
  have hdet : g.val.det = 1 := by
    have hn := Matrix.GeneralLinearGroup.det_ne_zero g
    have hb : ∀ b : Bit, b ≠ 0 → b=1 := by decide
    exact hb _ hn
  refine ⟨⟨g.val,hdet⟩,?_⟩
  apply Units.ext
  exact Matrix.SpecialLinearGroup.coe_GL_coe_matrix ⟨g.val,hdet⟩

instance binaryFourLinear_perfect : Group.IsPerfect (BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) := by
  letI := Atlas.sl_perfect (F := Bit) 4 (by decide)
  letI : Group.IsPerfect (Matrix.GeneralLinearGroup (Fin 4) Bit) :=
    Group.IsPerfect.ofSurjective binaryFour_toGL_surjective
  exact Group.IsPerfect.ofSurjective (f := binaryFourLinearMatrixEquiv.toMonoidHom)
    binaryFourLinearMatrixEquiv.surjective

def binaryFourLinearPermHom : (BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) →*
    Equiv.Perm BinaryFourSpace where
  toFun a := a.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem binaryFourLinear_even (a : BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) :
    Equiv.Perm.sign a.toEquiv = 1 := by
  let f := Equiv.Perm.sign.comp binaryFourLinearPermHom
  letI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f a,⟨a,rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- A bounded check on the sixteen-point affine coordinate space: each nonzero
translation interchanges eight pairs. This is not a Mathieu permutation certificate. -/
theorem binaryFourTranslation_even (v : BinaryFourSpace) :
    Equiv.Perm.sign (Equiv.addLeft v) = 1 := by
  revert v
  decide +kernel

theorem binaryFourAffine_even (a : BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) :
    Equiv.Perm.sign a.toEquiv = 1 := by
  have he : a.toEquiv = Equiv.addLeft (a 0) * a.linear.toEquiv := by
    apply Equiv.ext
    intro v
    have h := a.map_vadd (0 : BinaryFourSpace) v
    simpa [add_comm] using h
  rw [he,map_mul,binaryFourTranslation_even,binaryFourLinear_even,mul_one]

end Atlas.Fischer
