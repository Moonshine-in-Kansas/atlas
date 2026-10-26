import Atlas.Rudvalis.FourPlaneTorsion
import Atlas.Rudvalis.SignGram

/-! The single quadratic constraint on the six affine-plane parameters. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def fourPlaneParameterBasis (i : Fin 6) : FourPlaneParameters :=
  (![Pi.single 0 1,Pi.single 1 1,Pi.single 2 1,Pi.single 3 1,0,0] i,
    ![0,0,0,0,1,0] i,![0,0,0,0,0,1] i)

def fourPlaneParameterCoefficient (v : FourPlaneParameters) (i : Fin 6) : Bit :=
  ![v.1 0,v.1 1,v.1 2,v.1 3,v.2.1,v.2.2] i

theorem fourPlaneParameter_expansion (v : FourPlaneParameters) :
    (∑ i : Fin 6,fourPlaneParameterCoefficient v i • fourPlaneParameterBasis i)=v := by
  apply Prod.ext
  · funext j
    fin_cases j <;> simp [fourPlaneParameterCoefficient,fourPlaneParameterBasis,Fin.sum_univ_succ,Pi.single_apply]
  · apply Prod.ext <;> simp [fourPlaneParameterCoefficient,fourPlaneParameterBasis,Fin.sum_univ_succ]

noncomputable def fourPlaneSyndrome (r : Fin 4 → Bit) : FourPlaneParameters →ₗ[Bit] Bit :=
  (Atlas.Codes.binaryDot (signGenerator 16)).comp (fourPlaneParamMap r)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem fourPlaneSyndrome_basis_certificate (r : Fin 4 → Bit) (j : Fin 19) (i : Fin 6)
    (hr : (∑ k,r k)=1) :
    Atlas.Codes.binaryDot (signGenerator j) (fourPlaneParamMap r (fourPlaneParameterBasis i))=
      (if j=16 then 1 else 0)*fourPlaneSyndrome r (fourPlaneParameterBasis i) := by
  simp only [fourPlaneSyndrome,LinearMap.comp_apply,Atlas.Codes.binaryDot_apply]
  simp_rw [← Equiv.sum_comp seedCoordinateEquiv]
  decide +kernel +revert

theorem fourPlaneSyndrome_pairing (r : Fin 4 → Bit) (hr : (∑ k,r k)=1)
    (v : FourPlaneParameters) (j : Fin 19) :
    Atlas.Codes.binaryDot (signGenerator j) (fourPlaneParamMap r v)=
      (if j=16 then 1 else 0)*fourPlaneSyndrome r v := by
  rw [← fourPlaneParameter_expansion v]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourPlaneSyndrome_basis_certificate r j i hr]
  ring

set_option maxHeartbeats 1000000 in
theorem fourPlaneSyndrome_onto_witness (r : Fin 4 → Bit) :
    fourPlaneSyndrome r (fourPlaneParameterBasis 0)=1 := by
  simp only [fourPlaneSyndrome,LinearMap.comp_apply,Atlas.Codes.binaryDot_apply]
  simp_rw [← Equiv.sum_comp seedCoordinateEquiv]
  decide +kernel +revert

end Atlas.Rudvalis
