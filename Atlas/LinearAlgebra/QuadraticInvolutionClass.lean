import Atlas.LinearAlgebra.QuadraticDeterminantClassClassification
import Atlas.LinearAlgebra.QuadraticInvolutionWall
import Atlas.LinearAlgebra.InvolutionEigenspaceRestrictions
import Atlas.LinearAlgebra.BilinearDeterminantProduct
import Atlas.LinearAlgebra.InvolutionConjugacy

noncomputable section
namespace Atlas.Quadratic
open Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V] [Invertible (2 : F)]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

def involutionPlusForm := Q.comp (plus g.toLinearEquiv.toLinearMap).subtype
def involutionMinusForm := Q.comp (minus g.toLinearEquiv.toLinearMap).subtype

theorem involutionPlusForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate)
    (hg : Function.Involutive g) : (involutionPlusForm Q g).polarBilin.Nondegenerate := by
  have h := plus_nondegenerate Q.polarBilin hQ g.toLinearEquiv.toLinearMap hg
    (isometry_polar Q g) (Invertible.ne_zero (2 : F))
  rw [involutionPlusForm,QuadraticMap.polarBilin_comp]
  exact ⟨h.1,h.2⟩

theorem involutionMinusForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate)
    (hg : Function.Involutive g) : (involutionMinusForm Q g).polarBilin.Nondegenerate := by
  have h := minus_nondegenerate Q.polarBilin hQ g.toLinearEquiv.toLinearMap hg
    (isometry_polar Q g) (Invertible.ne_zero (2 : F))
  rw [involutionMinusForm,QuadraticMap.polarBilin_comp]
  exact ⟨h.1,h.2⟩

theorem involution_wall_discriminantClass (hQ : Q.polarBilin.Nondegenerate)
    (hg : Function.Involutive g) :
    wallDeterminantClass Q hQ g = discriminantClass (involutionMinusForm Q g)
      (involutionMinusForm_nondegenerate Q g hQ hg) := by
  have hm := involution_residual_eq_minus Q g hg (Invertible.ne_zero (2 : F))
  have hr : (Q.comp (residual Q g).subtype).polarBilin.Nondegenerate := by
    have h := involutionMinusForm_nondegenerate Q g hQ hg
    dsimp [involutionMinusForm] at h
    exact (congrArg (fun P : Submodule F V =>
      (Q.comp P.subtype).polarBilin.Nondegenerate) hm).mpr h
  have hw : wallDeterminantClass Q hQ g =
      discriminantClass (Q.comp (residual Q g).subtype) hr := by
    unfold wallDeterminantClass discriminantClass Atlas.Bilinear.determinantClass
    apply congrArg (Atlas.squareClass F)
    apply Units.ext
    change (LinearMap.BilinForm.toMatrix _ (wallForm Q g)).det = _
    rw [involution_wallForm_eq_associated Q g hg]
    rfl
  have hcongr : ∀ (P R : Submodule F V)
      (hp : (Q.comp P.subtype).polarBilin.Nondegenerate)
      (hr : (Q.comp R.subtype).polarBilin.Nondegenerate), P=R →
      discriminantClass (Q.comp P.subtype) hp = discriminantClass (Q.comp R.subtype) hr := by
    intro P R hp hr he
    subst R
    rfl
  exact hw.trans (hcongr _ _ hr (involutionMinusForm_nondegenerate Q g hQ hg) hm)

end Atlas.Quadratic
