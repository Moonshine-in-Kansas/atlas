import Atlas.LinearAlgebra.QuadraticWallDeterminant
import Atlas.LinearAlgebra.InvolutionEigenspaces

/-! # The Wall form of an odd-characteristic involution -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

theorem involution_residual_eq_minus (hg : Function.Involutive g) (h2 : (2 : F) ≠ 0) :
    residual Q g = Atlas.LinearInvolution.minus g.toLinearEquiv.toLinearMap := by
  ext x
  rw [Atlas.LinearInvolution.mem_minus]
  constructor
  · rintro ⟨y,rfl⟩
    change g (y - g y) = -(y - g y)
    rw [map_sub,hg y,neg_sub]
  · intro hx
    refine ⟨(2 : F)⁻¹ • x, ?_⟩
    change (2 : F)⁻¹ • x - g ((2 : F)⁻¹ • x) = x
    rw [map_smul]
    change (2 : F)⁻¹ • x - (2 : F)⁻¹ • g.toLinearEquiv.toLinearMap x = x
    rw [hx, ← smul_sub,sub_neg_eq_add, ← two_smul F x,smul_smul,inv_mul_cancel₀ h2,one_smul]

theorem involution_wallForm_apply (hg : Function.Involutive g) (h2 : (2 : F) ≠ 0)
    (u v : residual Q g) :
    wallForm Q g u v = (2 : F)⁻¹ * Q.polarBilin u.val v.val := by
  have hu : g u.val = -u.val := by
    apply (Atlas.LinearInvolution.mem_minus _ _).mp
    exact (congrArg (fun P : Submodule F V => u.val ∈ P)
      (involution_residual_eq_minus Q g hg h2)).mp u.prop
  have he : (residualMap Q g).rangeRestrict ((2 : F)⁻¹ • u.val) = u := by
    apply Subtype.ext
    change (2 : F)⁻¹ • u.val - g ((2 : F)⁻¹ • u.val) = u.val
    rw [map_smul,hu, ← smul_sub,sub_neg_eq_add, ← two_smul F u.val,
      smul_smul,inv_mul_cancel₀ h2,one_smul]
  calc
    _ = wallForm Q g ((residualMap Q g).rangeRestrict ((2 : F)⁻¹ • u.val)) v := by rw [he]
    _ = Q.polarBilin ((2 : F)⁻¹ • u.val) v.val := wallForm_residual Q g _ v
    _ = _ := by simp

theorem involution_wallForm_eq_associated [Invertible (2 : F)]
    (hg : Function.Involutive g) :
    wallForm Q g = (Q.comp (residual Q g).subtype).associated := by
  ext u v
  rw [involution_wallForm_apply Q g hg (Invertible.ne_zero (2 : F))]
  rw [QuadraticMap.associated_comp]
  change (2 : F)⁻¹ * Q.polarBilin u.val v.val = Q.associated u.val v.val
  simp [QuadraticMap.associated_apply,QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar,invOf_eq_inv]

theorem involution_restricted_discr_ne_zero [FiniteDimensional F V] [Invertible (2 : F)]
    (hQ : Q.polarBilin.Nondegenerate) (hg : Function.Involutive g)
    (b : Module.Basis (Fin (Module.finrank F (residual Q g))) F (residual Q g)) :
    QuadraticForm.discr b (Q.comp (residual Q g).subtype) ≠ 0 := by
  have hd := (LinearMap.nondegenerate_iff_det_ne_zero b).mp
    (wallForm_nondegenerate Q g hQ)
  rw [involution_wallForm_eq_associated Q g hg] at hd
  exact hd

/-- The Wall determinant of an involution is exactly the discriminant class of
its minus eigenspace, identified with the actual residual subspace above. -/
theorem involution_wallDeterminantClass [FiniteDimensional F V] [Invertible (2 : F)]
    (hQ : Q.polarBilin.Nondegenerate) (hg : Function.Involutive g)
    (b : Module.Basis (Fin (Module.finrank F (residual Q g))) F (residual Q g)) :
    wallDeterminantClass Q hQ g = Atlas.squareClass F
      (Units.mk0 (QuadraticForm.discr b (Q.comp (residual Q g).subtype))
        (involution_restricted_discr_ne_zero Q g hQ hg b)) := by
  rw [wallDeterminantClass_basis Q hQ g b]
  unfold Atlas.Bilinear.determinantClass
  congr 1
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix b (wallForm Q g)).det = _
  rw [involution_wallForm_eq_associated Q g hg]
  rfl

end Atlas.Quadratic
