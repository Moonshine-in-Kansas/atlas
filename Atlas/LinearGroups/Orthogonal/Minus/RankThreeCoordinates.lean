import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearGroups.Unitary.WittPair
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Free

/-! Actual half-free coordinates from two hyperbolic F-planes to two norm planes. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def tracePairCoordinates (hdeg : Module.finrank F K = 2) :
    VectorD 2 F ≃ₗ[F] (Fin 2 → K) :=
  let b := Module.finBasisOfFinrankEq F K hdeg
  let d := LinearMap.BilinForm.dualBasis (normForm hdeg).polarBilin (normForm_polar_nondegenerate hdeg) b
  ((LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) F F).trans
    (b.equivFun.symm.prodCongr d.equivFun.symm)).trans (LinearEquiv.finTwoArrow F K).symm

theorem tracePairCoordinates_form (hdeg : Module.finrank F K = 2) (v : VectorD 2 F) :
    trace F K (tracePairCoordinates hdeg v 0 *
      conjugation F K (tracePairCoordinates hdeg v 1)) = formD 2 F v := by
  let b := Module.finBasisOfFinrankEq F K hdeg
  let B := (normForm hdeg).polarBilin
  let d := LinearMap.BilinForm.dualBasis B (normForm_polar_nondegenerate hdeg) b
  let x : Fin 2 → F := fun i => v (.inl i)
  let y : Fin 2 → F := fun i => v (.inr i)
  change trace F K (b.equivFun.symm x * conjugation F K (d.equivFun.symm y)) = _
  rw [← normForm_polar hdeg]
  change B (b.equivFun.symm x) (d.equivFun.symm y) = _
  rw [b.equivFun_symm_apply]
  simp only [LinearMap.map_sum₂,LinearMap.map_smul₂,smul_eq_mul]
  have hp (i : Fin 2) : B (b i) (d.equivFun.symm y) = y i := by
    rw [show B (b i) (d.equivFun.symm y) = B (d.equivFun.symm y) (b i) from
      QuadraticMap.polar_comm (normForm hdeg) _ _]
    rw [← LinearMap.BilinForm.dualBasis_repr_apply]
    change d.equivFun (d.equivFun.symm y) i = y i
    rw [LinearEquiv.apply_symm_apply]
  simp only [hp]
  rfl

def rankThreePlaneCoordinates (hdeg : Module.finrank F K = 2) :
    VectorD 2 F ≃ₗ[F] (Fin 2 → K) :=
  let e := Classical.choose (Atlas.Unitary.exists_wittPlaneEquiv (F := F) (K := K) hdeg)
  (tracePairCoordinates hdeg).trans (e.restrictScalars F)

theorem rankThreePlaneCoordinates_form (hdeg : Module.finrank F K = 2) (v : VectorD 2 F) :
    norm F K (rankThreePlaneCoordinates hdeg v 0) +
      norm F K (rankThreePlaneCoordinates hdeg v 1) = formD 2 F v := by
  let e := Classical.choose (Atlas.Unitary.exists_wittPlaneEquiv (F := F) (K := K) hdeg)
  have he := Classical.choose_spec (Atlas.Unitary.exists_wittPlaneEquiv (F := F) (K := K) hdeg)
  change ∀ x y, Atlas.Unitary.hermitian F K (e x) (e y) =
    Atlas.Unitary.hyperbolicPlaneForm (F := F) x y at he
  let w := tracePairCoordinates hdeg v
  apply (algebraMap F K).injective
  rw [map_add,norm_formula hdeg,norm_formula hdeg]
  have hew := he w w
  simp only [Atlas.Unitary.hermitian,Fin.sum_univ_two] at hew
  change (e w 0 * conjugation F K (e w 0) +
    e w 1 * conjugation F K (e w 1)) = algebraMap F K (formD 2 F v)
  change (e w 0 * conjugation F K (e w 0) +
    e w 1 * conjugation F K (e w 1)) = Atlas.Unitary.hyperbolicPlaneForm (F := F) w w at hew
  rw [hew]
  rw [← tracePairCoordinates_form hdeg v,trace_formula hdeg]
  simp only [Atlas.Unitary.hyperbolicPlaneForm,map_mul,conjugation_conjugation hdeg]
  ring

def rankThreeNormCoordinates (hdeg : Module.finrank F K = 2) :
    Vector 2 F K ≃ₗ[F] ((Fin 2 → K) × K) :=
  (rankThreePlaneCoordinates hdeg).prodCongr (LinearEquiv.refl F K)

theorem rankThreeNormCoordinates_form (hdeg : Module.finrank F K = 2) (v : Vector 2 F K) :
    norm F K ((rankThreeNormCoordinates hdeg v).1 0) +
      norm F K ((rankThreeNormCoordinates hdeg v).1 1) +
      norm F K (rankThreeNormCoordinates hdeg v).2 = form hdeg 2 v := by
  change (norm F K (rankThreePlaneCoordinates hdeg v.1 0) +
    norm F K (rankThreePlaneCoordinates hdeg v.1 1)) + norm F K v.2 = _
  rw [rankThreePlaneCoordinates_form,form_apply]

end Atlas.Orthogonal.Minus
